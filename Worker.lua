-- Worker.lua ? parallel DC mesher (NO direct MeshPool usage)

local ReplicatedStorage = game:GetService("ReplicatedStorage")
local Players           = game:GetService("Players")

local DC  = require(ReplicatedStorage.Modules.DualContouring)
local SDF = require(ReplicatedStorage.Modules.SDF)

-- --- Config ---------------------------------------------------------
local GROUND_RAISE_VOX  = 2.0
-- Use double-sided triangles on LOD0 to fully close the shell and improve
-- collision accuracy at the bottoms of hills.  This duplicates each
-- triangle when lodLevel <= 0, generating inward-facing faces as well.
local BASE_DOUBLE_SIDED = true

-- Solid debug colors per LOD.  Use bright, high-contrast hues so the
-- triangles are easier to see.  LOD 0 (nearest) uses bright red; LOD 1
-- uses bright green; LOD 2 and higher use bright blue.  Adjust these
-- values if you prefer different colors.
local LOD_COLORS = {
	[0] = Color3.fromRGB(255, 0,   0),   -- Bright red for crisp triangles
	[1] = Color3.fromRGB(0,   255, 0),   -- Bright green
	[2] = Color3.fromRGB(0,   0,   255), -- Bright blue
}

-- --- Manager Actor handle (the one that owns MeshPool) --------------
local function getManagerActor()
	local plr = Players.LocalPlayer
	if not plr then return nil end
	local ps = plr:WaitForChild("PlayerScripts")
	return ps:WaitForChild("MesherManagerActor") -- <== Actor
end

-- --- Chunk markers (so manager/manager queue can coordinate) --------
local function getChunkFolder()
	local f = workspace:FindFirstChild("ClientChunks")
	if not f then
		f = Instance.new("Folder")
		f.Name = "ClientChunks"
		f.Parent = workspace
	end
	return f
end

local function claimMarker(key: string, center: Vector3, nonce: number)
	local f = getChunkFolder()
	local v = f:FindFirstChild(key)
	if not v then
		v = Instance.new("BoolValue")
		v.Name = key
		v.Value = false
		v.Parent = f
	end
	v:SetAttribute("JobNonce", nonce)
	v:SetAttribute("Pending", true)
	pcall(function()
		v:SetAttribute("cx", center.X)
		v:SetAttribute("cy", center.Y)
		v:SetAttribute("cz", center.Z)
	end)
	return v
end

local function markerAliveWithNonce(key: string, nonce: number)
	local f = workspace:FindFirstChild("ClientChunks")
	if not f then return false end
	local v = f:FindFirstChild(key)
	if not v then return false end
	return v:GetAttribute("JobNonce") == nonce
end

-- --- DC wrapper -----------------------------------------------------
local function dcGenerate(origin: Vector3, voxelSize: number, nx: number, ny: number, nz: number, baseY: number)
	local function densityFn(p: Vector3)
		return SDF.density(p, baseY)
	end
	return DC.generate({
		origin      = origin,
		cellSize    = voxelSize,
		nx = nx, ny = ny, nz = nz,
		densityFn   = densityFn,
		snapStep    = 6e-4,
		signEps     = 0.01,
		halfOpenXZ  = true,
		closeY      = true,
	})
end

-- --- Worker inbox from ChunkManager --------------------------------
script.Parent:BindToMessage("generateMesh", function(payload)
	local key: string        = payload.Key
	local origin: Vector3    = payload.Origin
	local voxelSize: number  = payload.VoxelSize
	local baseVoxel: number  = payload.BaseVoxelSize
	local dims: Vector3int16 = payload.Dims
	local lodLevel: number   = payload.LODLevel or 0

	local nx, ny, nz = dims.X, dims.Y, dims.Z
	local baseY = (GROUND_RAISE_VOX or 2.0) * (baseVoxel or voxelSize)

	print(string.format("[Worker][DC] job %s LOD=%d origin %d,%d,%d grid %dx%dx%d baseY=%.2f vx=%.2f",
		tostring(key), lodLevel, origin.X, origin.Y, origin.Z, nx, ny, nz, baseY, voxelSize))

	-- Create/claim a marker NOW with a unique nonce
	local nonce  = math.floor((os.clock() * 1000) % 2^31)
	local center = origin + Vector3.new(nx*voxelSize*0.5, 0, nz*voxelSize*0.5)
	claimMarker(key, center, nonce)

	-- Generate geometry
	local verts, tris = dcGenerate(origin, voxelSize, nx, ny, nz, baseY)

	-- If job is stale (manager replaced/cancelled marker), drop it
	if not markerAliveWithNonce(key, nonce) then
		print("[Worker] Dropped stale job for", key)
		return
	end

	-- If no geometry was produced, commit an empty chunk (unload) and finish.
	if (#verts == 0) or (#tris == 0) then
		local managerActor = getManagerActor()
		if managerActor then
			managerActor:SendMessage("commitChunk", {
				Key   = key,
				Verts = {},
				Tris  = {},
				Opts  = {},
				Nonce = nonce,
			})
		else
			warn("[Worker] No MesherManagerActor found; cannot commit", key)
		end
		return
	end

	-- Choose per-LOD solid color + shading hint.
	-- After generating geometry, decide whether to use flat shading based on predicted vertex count.
	-- Flat shading duplicates vertices per triangle, so if the number of triangles is high, we may exceed
	-- the EditableMesh vertex limit (˜60k)?782454775832638†screenshot?. Compute the predicted number of
	-- vertices for flat shading (3 per triangle, or 6 if double-sided) and disable flat shading if
	-- that would exceed ~55k vertices. This keeps chunks crisp when possible but falls back to smooth
	-- shading for extremely detailed chunks to avoid build failures.
	local predictedFlatVerts
	do
		local triPerFace = (BASE_DOUBLE_SIDED and (lodLevel <= 0)) and 6 or 3
		predictedFlatVerts = (#tris) * triPerFace
	end
	local useFlat = (lodLevel <= 0) and (predictedFlatVerts <= 55000)
	local solidColor = LOD_COLORS[lodLevel] or LOD_COLORS[2]
	local flatShade  = useFlat

	-- Hand off to the manager Actor (the only place that touches MeshPool)
	local managerActor = getManagerActor()
	if not managerActor then
		warn("[Worker] No MesherManagerActor found; cannot commit", key)
		return
	end

	-- Choose target collision fidelity based on LOD.  For the nearest
	-- chunks (LOD0), request PreciseConvexDecomposition to generate the
	-- most accurate physics shape possible.  For mid and far LODs, fall
	-- back to less expensive fidelities to save memory and processing
	-- time.  These settings may be adjusted in ChunkManager by splitting
	-- LOD0 into smaller sub-chunks, so the total complexity remains
	-- manageable.
	local cfTarget
	if lodLevel <= 0 then
		cfTarget = Enum.CollisionFidelity.PreciseConvexDecomposition
	elseif lodLevel == 1 then
		cfTarget = Enum.CollisionFidelity.Default
	else
		cfTarget = Enum.CollisionFidelity.Hull
	end

	managerActor:SendMessage("commitChunk", {
		Key   = key,
		Verts = verts,
		Tris  = tris,
		Opts  = {
			DoubleSided     = BASE_DOUBLE_SIDED and (lodLevel <= 0),
			UseVertexColors = false,        -- force solid per-face color
			SolidColor      = solidColor,   -- LOD debug color
			FlatShade       = flatShade,
			CollisionFidelityTarget = cfTarget,
		},
		Nonce = nonce,
	})
end)
