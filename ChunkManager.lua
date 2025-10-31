-- ChunkManager.lua ? DC streaming (one-tall band) with LOD, edge preloading, manager-VM pool ops
-- All mesh pool mutations happen inside MesherManagerActor ("commitChunk"/"unloadChunk").
-- Exposes :updateAround(...) (TerrainClient calls this) and uses :step(centerXZ) internally.

local Players = game:GetService("Players")

local ChunkManager = {}
ChunkManager.__index = ChunkManager

export type Settings = {
	VoxelSize: number,        -- base voxel size (studs)
	CellsPerAxis: number,     -- base XZ cells per chunk (e.g., 64)
	YCells: number,           -- vertical thickness (cells)
	RenderRadius: number,     -- chunk rings around camera (0 = only current)
	PreloadEdge: number?,     -- studs from chunk edge to pre-upgrade neighbors
	MaxWorkers: number,       -- number of worker Actors
	LODBands: { {maxDist: number, factor: number} }?, -- from near to far
}

-- ========== Manager Actor bridge ==========
local function getManagerActor()
	local plr = Players.LocalPlayer
	if not plr then return nil end
	local ps = plr:FindFirstChildOfClass("PlayerScripts")
	return ps and ps:FindFirstChild("MesherManagerActor")
end

local function requestUnloadOnManager(key: string)
	local mgrActor = getManagerActor()
	if mgrActor then
		mgrActor:SendMessage("unloadChunk", { Key = key })
	end
end

-- ========== Utilities ==========
local function keyFor(cx, cy, cz)
	return string.format("%d:%d:%d", cx, cy, cz)
end

local function ringIter(r: number)
	local function line(ax, az, bx, bz, acc)
		local dx, dz = bx - ax, bz - az
		local n = math.max(math.abs(dx), math.abs(dz))
		if n <= 0 then return end
		for i = 0, n do
			local t = i / n
			acc[#acc+1] = { math.floor(ax + t * dx + 0.5), math.floor(az + t * dz + 0.5) }
		end
	end
	local acc = {}
	if r == 0 then
		acc[1] = {0,0}; return acc
	end
	line(-r, -r,  r, -r, acc)
	line( r, -r,  r,  r, acc)
	line( r,  r, -r,  r, acc)
	line(-r,  r, -r, -r, acc)
	return acc
end

local function cloneActor(actorTemplate: Instance)
	local plr = Players.LocalPlayer
	local ps = plr and plr:FindFirstChildOfClass("PlayerScripts")
	local a = actorTemplate:Clone()
	a.Name = "MesherActor_" .. tostring(math.random(1000000, 9999999))
	if ps then a.Parent = ps else a.Parent = actorTemplate.Parent end
	return a
end

local function dimsFor(factor: number, baseCells: number, baseY: number): Vector3int16
	return Vector3int16.new(
		math.max(2, math.floor(baseCells / factor + 0.5)),
		math.max(2, math.floor(baseY    / factor + 0.5)),
		math.max(2, math.floor(baseCells / factor + 0.5))
	)
end

-- LOD metric chooser: treat bands as ring counts if they're small (<= RenderRadius+0.5),
-- else treat them as stud distances.
local function chooseLODFactorSmart(bands, ringDist: number, studsDist: number, settings): (number, number)
	local useRings = false
	if bands and #bands > 0 then
		local th = bands[1].maxDist
		if type(th) == "number" and th <= (settings.RenderRadius + 0.5) then
			useRings = true
		end
	end
	local metric = useRings and ringDist or studsDist
	for i = 1, #bands do
		if metric <= bands[i].maxDist then
			return bands[i].factor, i-1 -- lodIdx = i-1
		end
	end
	return bands[#bands].factor, #bands-1
end

-- ========== Constructor ==========
function ChunkManager.new(actorTemplate: Instance, settings: Settings)
	local self = setmetatable({}, ChunkManager)
	self.settings     = settings
	self.actorTemplate= actorTemplate

	self.activeChunks = {}   -- key -> marker BoolValue
	self.pending      = {}   -- key -> worker record
	self.workers      = {}   -- { {Actor=Actor, Busy=bool}, ... }
	self.freeWorkers  = {}   -- stack of available worker records
	self.chunkLOD     = {}   -- key -> current lodIdx
	self.pendingLOD   = {}   -- key -> lodIdx being computed

	-- Job queue: holds chunk requests that could not be dispatched due to lack
	-- of available workers.  The key maps to a job table containing chunk
	-- coordinates and LOD information.  Queued jobs are dispatched in FIFO
	-- order once workers become free.
	self.jobQueue = {}

	-- marker folder
	self.chunkFolder = workspace:FindFirstChild("ClientChunks")
	if not self.chunkFolder then
		local f = Instance.new("Folder")
		f.Name = "ClientChunks"; f.Parent = workspace
		self.chunkFolder = f
	end

	-- workers
	for _ = 1, settings.MaxWorkers do
		local a = cloneActor(actorTemplate)
		local rec = { Actor = a, Busy = false }
		table.insert(self.workers, rec)
		table.insert(self.freeWorkers, rec)
	end

	return self
end

-- ========== Dispatch ==========
function ChunkManager:dispatch(cx: number, cz: number, lodIdx: number, factor: number, origin: Vector3, dims: Vector3int16)
	local key = keyFor(cx, 0, cz)
	-- If no free workers, queue the job for later dispatch.  Overwrite any
	-- existing queued job for the same key so that only the latest LOD
	-- request is kept.  Mark the lod as pending to avoid requeueing.
	if #self.freeWorkers <= 0 then
		self.jobQueue[key] = {
			cx    = cx,
			cz    = cz,
			lodIdx= lodIdx,
			factor= factor,
			origin= origin,
			dims  = dims,
		}
		self.pendingLOD[key] = lodIdx
		return
	end
	local worker = table.remove(self.freeWorkers, #self.freeWorkers)
	worker.Busy = true

	worker.Actor:SendMessage("generateMesh", {
		Key = key,
		Origin = origin,
		VoxelSize = self.settings.VoxelSize * factor,
		BaseVoxelSize = self.settings.VoxelSize,
		Dims = dims,
		LODLevel = lodIdx,
	})
	self.pending[key] = worker
	self.pendingLOD[key] = lodIdx
end

-- ========== Main step (expects XZ world center) ==========
function ChunkManager:step(centerXZ: Vector2)
	local s        = self.settings
	local baseVox  = s.VoxelSize
	local baseY    = s.YCells
	local baseN    = s.CellsPerAxis
	local radius   = s.RenderRadius
	local preload  = s.PreloadEdge or 0

	local bands = s.LODBands or {
		{ maxDist = radius * baseN * baseVox * 0.45, factor = 2 },
		{ maxDist = radius * baseN * baseVox * 0.85, factor = 4 },
		{ maxDist = math.huge,                        factor = 8 },
	}

	local chunkSize = baseVox * baseN
	local wx = math.floor(centerXZ.X / chunkSize)
	local wz = math.floor(centerXZ.Y / chunkSize)
	local lx = centerXZ.X - wx * chunkSize
	local lz = centerXZ.Y - wz * chunkSize

	local wanted: {[string]: boolean} = {}

	local function ensureMarker(key)
		local m = self.activeChunks[key]
		if m then return m end
		local v = Instance.new("BoolValue")
		v.Name = key; v.Value = false
		v:SetAttribute("JobNonce", 0)
		v:SetAttribute("Pending", true)
		v.Parent = self.chunkFolder
		self.activeChunks[key] = v
		return v
	end

	-- request helper; can force a specific lodIdx (0 = highest)
	local function request(dx: number, dz: number, forcedLodIdx: number?)
		local cx, cz = wx + dx, wz + dz
		-- compute distance metrics for LOD selection
		local ringDist = math.max(math.abs(dx), math.abs(dz)) -- Chebyshev (rings)
		local chunkCenter = Vector3.new((wx+dx)*chunkSize + chunkSize*0.5, 0, (wz+dz)*chunkSize + chunkSize*0.5)
		local studsDist = (chunkCenter - Vector3.new(centerXZ.X,0,centerXZ.Y)).Magnitude

		-- pick LOD
		local factor, lodIdx
		if forcedLodIdx ~= nil then
			lodIdx = forcedLodIdx
			local band = bands[lodIdx + 1]
			factor = band and band.factor or 1
		else
			factor, lodIdx = chooseLODFactorSmart(bands, ringDist, studsDist, s)
		end

		local dims   = dimsFor(factor, baseN, baseY)
		local origin = Vector3.new((wx+dx)*chunkSize, 0, (wz+dz)*chunkSize)

		-- Compose a key for this chunk and mark it as wanted.  No splitting: each
		-- chunk uses a single pooled mesh entry regardless of LOD.  If the LOD
		-- needs changing and no job is pending, dispatch a new job.
		local key = keyFor(cx, 0, cz)
		wanted[key] = true
		ensureMarker(key)
		local currentLOD = self.chunkLOD[key]
		local isPending  = (self.pending[key] ~= nil)
		if (not currentLOD) or (lodIdx ~= currentLOD and not isPending) then
			self:dispatch(cx, cz, lodIdx, factor, origin, dims)
		end
	end

	-- === Square streaming ===
	-- 1) Base requests for the visible square, using bands.  To ensure that
	-- nearby chunks are dispatched before distant ones when worker threads
	-- are limited, iterate outward in rings (Chebyshev distance) from the
	-- player.  ringIter(r) returns the perimeter cells of the ring at
	-- distance r.  By processing smaller rings first, we prioritize
	-- high-detail chunks and avoid skipping near terrain even when the
	-- queue is saturated with far jobs.
	for r = 0, radius do
		local coords = ringIter(r)
		for _,coord in ipairs(coords) do
			local dx, dz = coord[1], coord[2]
			request(dx, dz)
		end
	end

	-- 2) Edge pre-upgrade: as you near a boundary within this chunk, force neighbors to LOD0
	if preload > 0 then
		local nearLeft   = (lx <= preload)
		local nearRight  = (chunkSize - lx <= preload)
		local nearFront  = (lz <= preload)
		local nearBack   = (chunkSize - lz <= preload)

		-- cardinals
		if nearLeft  then request(-1,  0, 0) end
		if nearRight then request( 1,  0, 0) end
		if nearFront then request( 0, -1, 0) end
		if nearBack  then request( 0,  1, 0) end

		-- diagonals for corner walking
		if nearLeft   and nearFront then request(-1, -1, 0) end
		if nearLeft   and nearBack  then request(-1,  1, 0) end
		if nearRight  and nearFront then request( 1, -1, 0) end
		if nearRight  and nearBack  then request( 1,  1, 0) end
	end

	-- finalize any completed jobs (marker.Value is set true by ManagerInbox on commit)
	for k, worker in pairs(self.pending) do
		local marker = self.activeChunks[k]
		if marker and marker.Value == true then
			self.pending[k] = nil
			self.chunkLOD[k] = self.pendingLOD[k] or 0
			self.pendingLOD[k] = nil
			worker.Busy = false
			table.insert(self.freeWorkers, worker)
		end
	end
	-- Remove queued jobs for keys that are no longer wanted.  Also remove
	-- pendingLOD for these keys so that future requests can be scheduled.
	for key,_ in pairs(self.jobQueue) do
		if not wanted[key] then
			self.jobQueue[key] = nil
			self.pendingLOD[key] = nil
		end
	end

	-- Dispatch queued jobs while there are free workers and remaining queued jobs.
	-- This ensures that all requested chunks are eventually processed, even if
	-- MaxWorkers limits were exceeded on previous frames.
	for key, job in pairs(self.jobQueue) do
		if #self.freeWorkers <= 0 then
			break
		end
		-- Remove from queue and dispatch
		self.jobQueue[key] = nil
		self:dispatch(job.cx, job.cz, job.lodIdx, job.factor, job.origin, job.dims)
	end

	-- cleanup: anything not wanted gets unloaded by the manager
	for k, marker in pairs(self.activeChunks) do
		if not wanted[k] then
			requestUnloadOnManager(k)
			if marker and marker.Parent then marker:Destroy() end
			self.activeChunks[k] = nil
			self.chunkLOD[k] = nil
			self.pending[k] = nil
			self.pendingLOD[k] = nil
		end
	end
end

-- ========== Back-compat wrapper ==========
function ChunkManager:updateAround(pos)
	local centerXZ: Vector2
	if typeof(pos) == "Vector3" then
		centerXZ = Vector2.new(pos.X, pos.Z)
	elseif typeof(pos) == "Vector2" then
		centerXZ = pos
	else
		local cam = workspace.CurrentCamera
		local p = (cam and cam.CFrame.Position) or Vector3.zero
		centerXZ = Vector2.new(p.X, p.Z)
	end
	self:step(centerXZ)
end

return ChunkManager
