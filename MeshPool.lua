-- MeshPool.lua - CLIENT ONLY (Single-VM pool with vertex-cap guard + batched ApplyMesh)
-- Hosts many chunks inside a small fixed set of EditableMeshes.
-- Changes from previous version:
--   ? Tracks per-pool vertex counts and per-chunk vertsAdded to avoid engine vertex limits.
--   ? pickPoolFor() now checks both triangle and vertex headroom.
--   ? Robust unload/replace adjusts both triCount and vertCount.
--   ? Batches ApplyMesh on Heartbeat (entry.dirty) to avoid spamming ApplyMesh each commit.
--   ? Optional em:RemoveUnused() after removals when pool gets dense.

local RunService   = game:GetService("RunService")
local AssetService = game:GetService("AssetService")

if RunService:IsServer() then
	warn("[MeshPool] Loaded on server; returning no-op stubs.")
	return {
		init = function() end,
		addOrReplaceChunk = function() return false end,
		unloadChunk = function() return false end,
	}
end

local MeshPool = {}

-- Collision fidelity ranking.  The CollisionFidelity enum values do not
-- necessarily correspond to accuracy.  For example, Hull (1) is less
-- accurate than Default (0) because Hull produces a single convex hull
-- while Default voxelizes and may better approximate slopes and concave
-- surfaces?802672436925696screenshot?.  PreciseConvexDecomposition (3) is the
-- most accurate.  Use this ranking table to select the most accurate
-- fidelity when aggregating requirements across chunks.
local CF_RANK = {
	[Enum.CollisionFidelity.PreciseConvexDecomposition] = 3,
	[Enum.CollisionFidelity.Default]                   = 2,
	[Enum.CollisionFidelity.Hull]                      = 1,
	[Enum.CollisionFidelity.Box]                       = 0,
}

-- For precise collision (LOD0), cycle through pool entries when selecting where
-- to store the chunk.  Distributing precise chunks across multiple
-- EditableMesh entries can help avoid lumps that reduce collision accuracy.
local nextPrecisePoolIndex = 1


-- ---------- Tunables ----------
local TRI_CAP        = 19500         -- per EditableMesh entry, sum of faces (one-sided count)
local VERT_CAP       = 58000         -- conservative limit to stay below engine vertex cap
local REMOVE_UNUSED_NEAR = 52000     -- when vertCount exceeds this, prune after removals
local APPLY_PER_FRAME   = 3          -- max pooled parts to ApplyMesh each Heartbeat
local FALLBACK_PART_COLOR = Color3.fromRGB(176,180,176)
local DEFAULT_FACE_COLOR  = Color3.fromHSV(0.33, 0.70, 0.60)
local MAX_PRECISE_PER_ENTRY = 3      -- LOD0 chunks per pooled entry
local MAX_PRECISE_POOL_SLOTS = 3     -- pooled entries available for precise collision chunks

-- ---------- State ----------
-- entry = {
--   em, part,
--   triCount: integer,
--   vertCount: integer,
--   chunkMap: { [key] = { faceIds = {...}, vertsAdded = N } },
--   palette, defaultCid,
--   canSetNormal, canFaceColors,
--   solidCids = {},
--   dirty = false, applying = false,
-- }
local POOL = {}
local CHUNK_INDEX = {}     -- key -> { poolIdx, faceIds = {...}, vertsAdded = N }
local FIXED_CHUNKS = {}    -- key -> fixed entry record

local PoolFolder
local _initialized = false
local _lastCfg = nil

local function clampPreciseIndex()
	local limit = math.min(#POOL, MAX_PRECISE_POOL_SLOTS)
	if limit <= 0 then
		nextPrecisePoolIndex = 1
		return
	end
	if nextPrecisePoolIndex < 1 or nextPrecisePoolIndex > limit then
		nextPrecisePoolIndex = 1
	end
end

local function isPreciseLOD(lodLevel)
	if typeof(lodLevel) ~= "number" then
		return false
	end
	return lodLevel <= 0
end

local function incrementPreciseCount(entry, lodLevel)
	if not entry then return end
	if not isPreciseLOD(lodLevel) then return end
	entry.preciseCount = (entry.preciseCount or 0) + 1
end

local function decrementPreciseCount(entry, lodLevel)
	if not entry then return end
	if not isPreciseLOD(lodLevel) then return end
	local current = entry.preciseCount or 0
	if current <= 0 then
		entry.preciseCount = 0
	else
		entry.preciseCount = current - 1
	end
end

-- ---------- Utils ----------
local function ensureFolder()
	if PoolFolder and PoolFolder.Parent then return PoolFolder end
	local f = workspace:FindFirstChild("ClientPooled")
	if not f then
		f = Instance.new("Folder")
		f.Name = "ClientPooled"
		f.Parent = workspace
	end
	PoolFolder = f
	return f
end

local function triNormal(p1,p2,p3)
	local n = (p2 - p1):Cross(p3 - p1)
	if n.Magnitude < 1e-9 then return Vector3.new(0,1,0) end
	return n.Unit
end

local function triCentroid(p1,p2,p3)
	return (p1 + p2 + p3)/3
end

local function colorKey(c: Color3)
	return string.format("%.5f_%.5f_%.5f", c.R, c.G, c.B)
end

local function solidCidFor(entry, color3: Color3)
	if not entry or not entry.canFaceColors then return nil end
	entry.solidCids = entry.solidCids or {}
	local k = colorKey(color3)
	local cid = entry.solidCids[k]
	if cid then return cid end
	local ok, newcid = pcall(function() return entry.em:AddColor(color3, 1.0) end)
	if ok and newcid then
		entry.solidCids[k] = newcid
		return newcid
	end
	return entry.defaultCid
end

-- ---------- Palette ----------
local function makeHSVPalette(em, levels, baseHue, hueJitter, sMin, sMax, vMin, vMax)
	levels    = math.max(2, levels or 24)
	baseHue   = (baseHue ~= nil) and baseHue or 0.33
	hueJitter = hueJitter or 0.008
	sMin, sMax = sMin or 0.62, sMax or 0.78
	vMin, vMax = vMin or 0.48, vMax or 0.64

	local ids = table.create(levels)
	for i = 0, levels-1 do
		local t  = (levels == 1) and 0.5 or (i/(levels-1))
		local h  = baseHue + (2*t - 1) * hueJitter
		local s  = sMin + (sMax - sMin) * (0.35 + 0.65*t)
		local v  = vMin + (vMax - vMin) * t
		local ok,cid = pcall(function() return em:AddColor(Color3.fromHSV(h, s, v), 1.0) end)
		if not ok or not cid then return nil end
		ids[i+1] = cid
	end
	return ids
end

local function patchIndexForTri(p1,p2,p3, levels, cfg)
	levels = math.max(2, levels or 24); cfg = cfg or {}
	local c  = triCentroid(p1,p2,p3)
	local r  = math.rad(cfg.RotationDeg or 27)
	local cr, sr = math.cos(r), math.sin(r)
	local rx = c.X * cr - c.Z * sr
	local rz = c.X * sr + c.Z * cr
	local wf = cfg.WarpFreq or (1/120)
	local wa = cfg.WarpAmp  or 12.0
	rx = rx + math.noise(rx*wf, rz*wf) * wa
	rz = rz + math.noise((rx+97)*wf, (rz-53)*wf) * wa
	local size = math.max(8, cfg.PatchSize or 90.0)
	local cx, cz = math.floor(rx/size), math.floor(rz/size)
	local function randCell(ix, iz, kx, kz) return 0.5*(math.noise(ix*0.331+kx, iz*0.479+kz)+1) end
	local baseR = randCell(cx, cz, 1.3, 2.1)
	local idx   = math.clamp(1 + math.floor(baseR * (levels - 1) + 0.5), 1, levels)
	local jx = randCell(cx, cz, 0.1, 0.2); local jz = randCell(cx, cz, 0.7, 0.9)
	local cx0, cz0 = (cx + jx)*size, (cz + jz)*size
	local dx, dz = rx - cx0, rz - cz0
	local dist   = math.sqrt(dx*dx + dz*dz)
	local spotR  = (cfg.SpotRadius or 0.45) * size
	local chance = (cfg.SpotChance or 0.10)
	if dist < spotR and randCell(cx, cz, 4.7, 5.9) > (1 - chance) then
		local strength = math.max(1, math.floor(cfg.SpotStrength or 3))
		idx = math.max(1, idx - strength)
	end
	local vf = cfg.VariationFreq or (1/90.0)
	local rr = 0.5 * (math.noise((rx+31)*vf, (rz-17)*vf) + 1)
	local vary = math.floor(cfg.VariationSteps or 1)
	if vary > 0 then
		if rr < 0.5 then idx = idx - vary else idx = idx + vary end
		idx = math.clamp(idx, 1, levels)
	end
	return idx
end

-- ---------- Apply batching ----------
local DIRTY = {}  -- list of entries to flush
local flushing = false

local function markDirty(entry)
	if entry.dirty then return end
	entry.dirty = true
	DIRTY[#DIRTY+1] = entry
end

local function applyPoolMesh(entry)
	-- Convert the EditableMesh into a Content object. If this fails, skip this frame.
	local okContent, content = pcall(function()
		return Content.fromObject(entry.em)
	end)
	if not okContent or not content then
		return
	end

	-- Determine whether we need per-face colors. This mirrors the logic used when
	-- pushing color IDs into the EditableMesh. If true, we disable UsePartColor on
	-- the resulting MeshPart so that face colors are respected. Otherwise, a
	-- fallback part color is applied.
	local faceColorCap    = entry.canFaceColors
	local wantFaceColors  = faceColorCap and (entry.palette ~= nil or entry.defaultCid ~= nil)

	-- Historically this function attempted an in-place ApplyMesh() on the existing
	-- MeshPart, only falling back to creating a new MeshPart if ApplyMesh failed.
	-- However, collisions for EditableMesh objects can become out of sync with the
	-- visual geometry when ApplyMesh is used repeatedly?85239273133226L54-L67?.  To ensure
	-- that the physics geometry matches the new mesh each time, we now always
	-- create a fresh MeshPart from the generated content. This forces Roblox to
	-- recalc the collision data and eliminates the slight gap that could be
	-- observed between the visual triangles and the collision surface.
	-- Prepare options for CreateMeshPartAsync.  We pass the aggregated
	-- collisionFidelity (if any) so that the resulting MeshPart uses the
	-- desired collision representation from the start.  RenderFidelity is set
	-- to Automatic to let Roblox choose the best render fidelity.  See
	-- AssetService:CreateMeshPartAsync documentation for details.
	local createOpts
	do
		local cf = entry.collisionFidelity
		if cf then
			-- Use capitalized keys for CreateMeshPartAsync options.  Roblox's
			-- AssetService expects `CollisionFidelity` and `RenderFidelity`
			-- rather than lower-case names?870761339834114L515-L519?.  Passing
			-- these ensures the resulting MeshPart uses the desired
			-- collision fidelity and render fidelity.  Without these keys,
			-- the default (Hull) is used, leading to inaccurate collisions.
			createOpts = { CollisionFidelity = cf, RenderFidelity = Enum.RenderFidelity.Automatic }
		else
			createOpts = { RenderFidelity = Enum.RenderFidelity.Automatic }
		end
	end
	local okNew, newPartOrErr = pcall(function()
		-- Pass options table if a collision fidelity is specified.  Some API
		-- versions may expect lower-case keys (collisionFidelity), as per
		-- documentation?870761339834114L515-L519?.
		return AssetService:CreateMeshPartAsync(content, createOpts)
	end)
	if not okNew or not newPartOrErr then
		-- If for some reason a new MeshPart cannot be created (e.g. transient
		-- failure), attempt to fall back to ApplyMesh on the existing part. Note
		-- that this may perpetuate stale collision geometry until the next
		-- successful frame.
		local okApply, _ = pcall(function()
			entry.part:ApplyMesh(content)
		end)
		if okApply then
			-- Even though ApplyMesh succeeded, face colors may need to be toggled.
			if wantFaceColors then
				pcall(function() entry.part.UsePartColor = false end)
			else
				pcall(function()
					entry.part.UsePartColor = true
					entry.part.Color = FALLBACK_PART_COLOR
				end)
			end
		end
		return
	end

	local newPart = newPartOrErr
	-- Copy essential properties from the old part to the new part.  Previously
	-- the mesh part used Neon for high-visibility and toggled collisions based on
	-- an aggregated collidable flag.  To improve readability and ensure that all
	-- chunks collide, we instead set SmoothPlastic material and always enable
	-- collisions.  Collision fidelity will be configured below based on the
	-- aggregated fidelity target of this entry.
	newPart.Name       = entry.part.Name
	newPart.Anchored   = true
	newPart.CastShadow = entry.part.CastShadow
	-- Use SmoothPlastic material (Neon was too bright and hindered legibility)
	newPart.Material   = Enum.Material.SmoothPlastic
	newPart.Color      = entry.part.Color
	newPart.CFrame     = entry.part.CFrame
	newPart.Parent     = entry.part.Parent
	-- Always enable collisions, queries, and touch.  Individual chunks specify
	-- their desired collision fidelity (e.g. PreciseConvexDecomposition or Hull),
	-- which will be applied below.  Having collisions enabled on all parts
	-- prevents players from falling through distant chunks and simplifies logic.
	newPart.CanCollide = true
	newPart.CanQuery   = true
	newPart.CanTouch   = true

	-- Configure per-face or solid coloring on the new part. If face colors are
	-- desired, disable UsePartColor so that the per-face color table from the
	-- EditableMesh is used. Otherwise set a fallback color on the part.
	if wantFaceColors then
		pcall(function() newPart.UsePartColor = false end)
	else
		pcall(function()
			newPart.UsePartColor = true
			newPart.Color = FALLBACK_PART_COLOR
		end)
	end

	-- Configure collision fidelity on the new part.  The part was created with
	-- the desired collision fidelity via AssetService:CreateMeshPartAsync,
	-- so further setting may not be necessary.  However, some platforms may
	-- still honour the CollisionFidelity property or require a call to
	-- ResetCollisionFidelityWithEditableMeshDataLua, so we attempt both as
	-- fallbacks.  All calls are wrapped in pcall to tolerate script security.
	do
		local cf = entry.collisionFidelity
		if cf then
			-- Attempt to set property (may be read-only) and recalc using UGC.
			pcall(function()
				newPart.CollisionFidelity = cf
			end)
			pcall(function()
				local ugs = game:GetService("UGCValidationService")
				if ugs and ugs.ResetCollisionFidelityWithEditableMeshDataLua then
					ugs:ResetCollisionFidelityWithEditableMeshDataLua(newPart, entry.em, cf)
				end
			end)
		end
	end

	-- Destroy the old part and replace it with the newly created one.
	entry.part:Destroy()
	entry.part = newPart
end

RunService.Heartbeat:Connect(function()
	if flushing then return end
	flushing = true
	local applied = 0
	local i = 1
	while i <= #DIRTY and applied < APPLY_PER_FRAME do
		local entry = DIRTY[i]
		if entry and entry.dirty and entry.part and entry.part.Parent then
			applyPoolMesh(entry)
			entry.dirty = false
			applied += 1
			-- remove from list (swap pop)
			DIRTY[i] = DIRTY[#DIRTY]
			DIRTY[#DIRTY] = nil
		else
			i += 1
		end
	end
	flushing = false
end)

-- ---------- Helpers ----------
local function removeFaces(entry, faceIds)
	if not entry or not entry.em or not faceIds then return 0 end
	local removed = 0
	for _,fid in ipairs(faceIds) do
		pcall(function() entry.em:RemoveFace(fid) end)
		removed += 1
	end
	return removed
end

local function ensureCapsCached(entry)
	if entry.canSetNormal == nil then
		pcall(function() entry.canSetNormal = (entry.em.SetVertexNormal ~= nil) end)
		if entry.canSetNormal == nil then entry.canSetNormal = false end
	end
	if entry.canFaceColors == nil then
		pcall(function() entry.canFaceColors = (entry.em.SetFaceColors ~= nil) and (entry.em.AddColor ~= nil) end)
		if entry.canFaceColors == nil then entry.canFaceColors = false end
	end
end

local function ensureFaceIds(entry, opts)
	if not entry.canFaceColors then return end
	if not entry.palette and opts.UseVertexColors ~= false then
		entry.palette = makeHSVPalette(
			entry.em,
			(opts.ColorCfg and opts.ColorCfg.Levels) or 24,
			(opts.ColorCfg and opts.ColorCfg.Hue),
			(opts.ColorCfg and opts.ColorCfg.HueJitter),
			(opts.ColorCfg and opts.ColorCfg.SMin),
			(opts.ColorCfg and opts.ColorCfg.SMax),
			(opts.ColorCfg and opts.ColorCfg.VMin),
			(opts.ColorCfg and opts.ColorCfg.VMax)
		)
	end
	if not entry.defaultCid then
		local ok, cid = pcall(function()
			return entry.em:AddColor((opts.ColorCfg and opts.ColorCfg.PartFallbackColor) or DEFAULT_FACE_COLOR, 1.0)
		end)
		if ok and cid then entry.defaultCid = cid end
	end
end

local function colorFace(entry, fid, p1,p2,p3, opts)
	if not entry.canFaceColors then return end

	local cid
	if opts.SolidColor then
		cid = solidCidFor(entry, opts.SolidColor)
	else
		cid = entry.defaultCid
		if entry.palette and opts.UseVertexColors ~= false then
			local idx = patchIndexForTri(p1,p2,p3, #entry.palette, opts.ColorCfg or {})
			cid = entry.palette[idx] or entry.palette[#entry.palette] or cid
		end
	end
	if cid then pcall(function() entry.em:SetFaceColors(fid, {cid, cid, cid}) end) end
end

local function recomputeCollisionFidelity(entry)
	if not entry then return end
	local highest = nil
	local highestRank = -math.huge
	for _,info in pairs(entry.chunkMap) do
		if info and info.collisionFidelity then
			local rank = CF_RANK[info.collisionFidelity] or -math.huge
			if rank > highestRank then
				highest = info.collisionFidelity
				highestRank = rank
			end
		end
	end
	entry.collisionFidelity = highest
end


local function requiredVerts(triCount, uniqueVerts, flatShade, doubleSided)
	if flatShade then
		local perFace = 3
		local faces = triCount * (doubleSided and 2 or 1)
		return perFace * faces
	else
		return uniqueVerts
	end
end

local function pickPoolFor(trisNeed, vertsNeed)
	for i,entry in ipairs(POOL) do
		local roomTri  = (entry.triCount or 0)  + trisNeed  <= TRI_CAP
		local roomVert = (entry.vertCount or 0) + vertsNeed <= VERT_CAP
		if roomTri and roomVert then return i end
	end
	return nil
end

-- Similar to pickPoolFor, but cycle through entries starting from
-- nextPrecisePoolIndex.  This is used for chunks requesting
-- PreciseConvexDecomposition, ensuring they are distributed across
-- multiple entries.  Returns nil if no entry has sufficient room.
local function pickPoolForPrecise(trisNeed, vertsNeed)
	if #POOL == 0 then return nil end
	local limit = math.min(#POOL, MAX_PRECISE_POOL_SLOTS)
	if limit <= 0 then return nil end
	if nextPrecisePoolIndex > limit then
		nextPrecisePoolIndex = 1
	end
	local start = nextPrecisePoolIndex
	for attempt = 0, limit - 1 do
		local idx = ((start - 1 + attempt) % limit) + 1
		local entry = POOL[idx]
		local roomTri  = (entry.triCount or 0)  + trisNeed  <= TRI_CAP
		local roomVert = (entry.vertCount or 0) + vertsNeed <= VERT_CAP
		local preciseRoom = (entry.preciseCount or 0) < MAX_PRECISE_PER_ENTRY
		if roomTri and roomVert and preciseRoom then
			nextPrecisePoolIndex = (idx % limit) + 1
			return idx
		end
	end
	return nil
end

local function createFixedEntry(key)
	local okEm, em = pcall(function()
		return AssetService:CreateEditableMesh({ FixedSize = true })
	end)
	if not okEm or not em then
		warn("[MeshPool] CreateEditableMesh (fixed) failed: ", tostring(em))
		return nil
	end

	local part = Instance.new("MeshPart")
	part.Name = ("FixedChunk_%s"):format(key)
	part.Anchored = true
	part.CastShadow = true
	part.Material = Enum.Material.SmoothPlastic
	part.Color = FALLBACK_PART_COLOR
	part.CFrame = CFrame.new()
	part.CanCollide = true
	pcall(function() part.UsePartColor = false end)
	part.Parent = ensureFolder()

	local entry = {
		em = em,
		part = part,
		triCount = 0,
		vertCount = 0,
		chunkMap = {},
		palette = nil,
		defaultCid = nil,
		canSetNormal = nil,
		canFaceColors = nil,
		solidCids = {},
		dirty = false,
		applying = false,
		collisionFidelity = nil,
		isFixed = true,
		active = true,
		lodLevel = nil,
		preciseCount = 0,
	}
	return entry
end

-- ---------- Public API ----------
function MeshPool.addOrReplaceChunk(key, srcVerts, srcTris, opts)
	if not _initialized or #POOL == 0 then
		MeshPool.init(_lastCfg or { PoolSize = 12, TriCap = 19500 })
	end
	if type(srcVerts) ~= "table" or #srcVerts == 0 then return false end
	if type(srcTris)  ~= "table" or #srcTris  == 0 then return false end

	opts = opts or {}
	local wantFixed = opts.FixedEditable == true
	local lodLevel = opts.LODLevel
	local doubleSided = opts.DoubleSided == true
	local flatShade   = opts.FlatShade == true
	local trisNeeded  = #srcTris * (doubleSided and 2 or 1)
	local vertsNeeded = requiredVerts(#srcTris, #srcVerts, flatShade, doubleSided)

	local isPrecise = false
	do
		local cf = opts.CollisionFidelityTarget
		if cf == Enum.CollisionFidelity.PreciseConvexDecomposition then
			isPrecise = true
		end
	end

	local rec = CHUNK_INDEX[key]
	if rec and rec.isFixed and not wantFixed then
		local fixedEntry = rec.entry or FIXED_CHUNKS[key]
		if fixedEntry then
			local existing = fixedEntry.chunkMap and fixedEntry.chunkMap[key]
			if existing and existing.faceIds then
				removeFaces(fixedEntry, existing.faceIds)
				decrementPreciseCount(fixedEntry, existing.lodLevel or rec.lodLevel)
			end
			FIXED_CHUNKS[key] = nil
			if fixedEntry.part then fixedEntry.part:Destroy() end
			pcall(function() if fixedEntry.em then fixedEntry.em:Destroy() end end)
		end
		CHUNK_INDEX[key] = nil
		rec = nil
	end

	if wantFixed then
		if rec and not rec.isFixed then
			local dynEntry = rec.entry or POOL[rec.poolIdx]
			if dynEntry then
				local removedFaces = removeFaces(dynEntry, rec.faceIds)
				dynEntry.triCount = math.max(0, (dynEntry.triCount or 0) - removedFaces)
				dynEntry.vertCount = math.max(0, (dynEntry.vertCount or 0) - (rec.vertsAdded or 0))
				dynEntry.chunkMap[key] = nil
				recomputeCollisionFidelity(dynEntry)
				markDirty(dynEntry)
				decrementPreciseCount(dynEntry, rec.lodLevel)
			end
			CHUNK_INDEX[key] = nil
			rec = nil
		end
		local entry = FIXED_CHUNKS[key]
		if entry and entry.chunkMap and entry.chunkMap[key] and entry.lodLevel ~= nil and lodLevel ~= nil and entry.lodLevel == lodLevel then
			entry.active = true
			if entry.part and entry.part.Parent == nil then
				entry.part.Parent = ensureFolder()
			end
			CHUNK_INDEX[key] = {
				entry = entry,
				faceIds = entry.chunkMap[key].faceIds,
				vertsAdded = entry.chunkMap[key].vertsAdded,
				isFixed = true,
				lodLevel = entry.lodLevel,
			}
			return true
		end
		if not entry then
			entry = createFixedEntry(key)
			if not entry then
				return false
			end
			FIXED_CHUNKS[key] = entry
		else
			local existing = entry.chunkMap and entry.chunkMap[key]
			if existing and existing.faceIds then
				removeFaces(entry, existing.faceIds)
				decrementPreciseCount(entry, existing.lodLevel)
			end
			entry.chunkMap[key] = nil
			entry.triCount = 0
			entry.vertCount = 0
			entry.collisionFidelity = nil
		end
		ensureCapsCached(entry); ensureFaceIds(entry, opts)
		local pack, err = addFacesInto(entry)
		if not pack then
			warn("[MeshPool] build failed ", err, " for ", key)
			return false
		end
		pack.collisionFidelity = opts.CollisionFidelityTarget
		entry.triCount = #pack.faceIds
		entry.vertCount = pack.vertsAdded or 0
		pack.lodLevel = lodLevel
		entry.chunkMap[key] = pack
		entry.lodLevel = lodLevel
		entry.active = true
		entry.collisionFidelity = pack.collisionFidelity
		incrementPreciseCount(entry, lodLevel)
		if entry.part and entry.part.Parent == nil then
			entry.part.Parent = ensureFolder()
		end
		markDirty(entry)
		CHUNK_INDEX[key] = {
			entry = entry,
			faceIds = pack.faceIds,
			vertsAdded = pack.vertsAdded,
			isFixed = true,
			lodLevel = lodLevel,
		}
		return true
	end

	local recEntry = rec and (rec.entry or POOL[rec.poolIdx]) or nil
	local entry, poolIdx
	if rec and recEntry then
		entry = recEntry; poolIdx = rec.poolIdx
		ensureCapsCached(entry); ensureFaceIds(entry, opts)
		local roomAfter = ((entry.triCount or 0) - #rec.faceIds) + trisNeeded <= TRI_CAP
		local vertAfter = ((entry.vertCount or 0) - (rec.vertsAdded or 0)) + vertsNeeded <= VERT_CAP
		if not (roomAfter and vertAfter) then
			if isPrecise then
				poolIdx = pickPoolForPrecise(trisNeeded, vertsNeeded)
			else
				poolIdx = pickPoolFor(trisNeeded, vertsNeeded)
			end
			if not poolIdx then
				warn(("[MeshPool] no pool has room for %s (t=%d v=%d)"):format(tostring(key), trisNeeded, vertsNeeded))
				return false
			end
			entry = POOL[poolIdx]
			ensureCapsCached(entry); ensureFaceIds(entry, opts)
		end
	else
		if isPrecise then
			poolIdx = pickPoolForPrecise(trisNeeded, vertsNeeded)
		else
			poolIdx = pickPoolFor(trisNeeded, vertsNeeded)
		end
		if not poolIdx then
			warn(("[MeshPool] no pool has room for %s (t=%d v=%d)"):format(tostring(key), trisNeeded, vertsNeeded))
			return false
		end
		entry = POOL[poolIdx]
		ensureCapsCached(entry); ensureFaceIds(entry, opts)
	end

	local function addFacesInto(e)
		local newFaceIds = table.create(trisNeeded)
		local vertsAdded = 0

		if flatShade then
			for _,t in ipairs(srcTris) do
				local a,b,c = t[1], t[2], t[3]
				local p1,p2,p3 = srcVerts[a], srcVerts[b], srcVerts[c]
				if p1 and p2 and p3 then
					local area2 = (p2 - p1):Cross(p3 - p1).Magnitude
					if area2 >= 5e-10 then
						local ok1,v1 = pcall(function() return e.em:AddVertex(p1) end)
						local ok2,v2 = pcall(function() return e.em:AddVertex(p2) end)
						local ok3,v3 = pcall(function() return e.em:AddVertex(p3) end)
						if not (ok1 and ok2 and ok3 and v1 and v2 and v3) then
							return nil, "vertex_add_failed"
						end
						vertsAdded += 3
						if e.canSetNormal then
							local n = triNormal(p1,p2,p3)
							pcall(function()
								e.em:SetVertexNormal(v1, n); e.em:SetVertexNormal(v2, n); e.em:SetVertexNormal(v3, n)
							end)
						end
						local okF, fid = pcall(function() return e.em:AddTriangle(v1, v2, v3) end)
						if not (okF and fid) then return nil, "face_add_failed" end
						colorFace(e, fid, p1,p2,p3, opts)
						newFaceIds[#newFaceIds+1] = fid
						if doubleSided then
							local okB, fidB = pcall(function() return e.em:AddTriangle(v3, v2, v1) end)
							if okB and fidB then
								colorFace(e, fidB, p3,p2,p1, opts)
								newFaceIds[#newFaceIds+1] = fidB
							else
								return nil, "face_add_failed"
							end
						end
					end
				end
			end
		else
			for _,t in ipairs(srcTris) do
				local a,b,c = t[1], t[2], t[3]
				local fid, okF = nil, nil
				local p1,p2,p3 = srcVerts[a], srcVerts[b], srcVerts[c]
				if p1 and p2 and p3 then
					local okAdd, faceId = pcall(function() return e.em:AddTriangle(p1, p2, p3) end)
					if not (okAdd and faceId) then return nil, "face_add_failed" end
					fid = faceId
					colorFace(e, fid, p1,p2,p3, opts)
					newFaceIds[#newFaceIds+1] = fid
					if doubleSided then
						local okB, fidB = pcall(function() return e.em:AddTriangle(p3, p2, p1) end)
						if okB and fidB then
							colorFace(e, fidB, p3,p2,p1, opts)
							newFaceIds[#newFaceIds+1] = fidB
						else
							return nil, "face_add_failed"
						end
					end
				end
			end
		end

		return { faceIds = newFaceIds, vertsAdded = vertsAdded }
	end

	local pack, err = addFacesInto(entry)
	if not pack then
		local old = entry
		local newVertCount = 0
		for _,info in pairs(old.chunkMap) do
			newVertCount += (info.vertsAdded or 0)
		end
		entry.vertCount = newVertCount
		pack, err = addFacesInto(entry)
	end
	if not pack then
		local altIdx
		for i,ent in ipairs(POOL) do
			if i ~= poolIdx then
				if (not isPrecise) or (i <= math.min(#POOL, MAX_PRECISE_POOL_SLOTS)) then
					local roomTri  = (ent.triCount or 0)  + trisNeeded  <= TRI_CAP
					local roomVert = (ent.vertCount or 0) + vertsNeeded <= VERT_CAP
					local preciseRoom = (not isPrecise) or ((ent.preciseCount or 0) < MAX_PRECISE_PER_ENTRY)
					if roomTri and roomVert and preciseRoom then altIdx = i; break end
				end
			end
		end
		if altIdx then
			local altEntry = POOL[altIdx]
			ensureCapsCached(altEntry); ensureFaceIds(altEntry, opts)
			pack, err = addFacesInto(altEntry)
			if pack then
				entry = altEntry
				poolIdx = altIdx
			end
		end
	end
	if not pack then
		warn("[MeshPool] build failed ", err, " for ", key)
		return false
	end

	if pack then pack.collisionFidelity = opts.CollisionFidelityTarget end

	local previousEntry = recEntry
	if rec and previousEntry then
		decrementPreciseCount(previousEntry, rec.lodLevel)
	end

	entry.triCount  = (entry.triCount or 0)  + #pack.faceIds
	entry.vertCount = (entry.vertCount or 0) + (pack.vertsAdded or 0)
	pack.lodLevel = lodLevel
	entry.chunkMap[key] = pack
	incrementPreciseCount(entry, lodLevel)
	CHUNK_INDEX[key] = { entry = entry, poolIdx = poolIdx, faceIds = pack.faceIds, vertsAdded = pack.vertsAdded, isFixed = false, lodLevel = lodLevel }
	recomputeCollisionFidelity(entry)
	markDirty(entry)

	if rec and recEntry and recEntry ~= entry then
		local old = recEntry
		local removedFaces = removeFaces(old, rec.faceIds)
		old.triCount  = math.max(0, (old.triCount or 0)  - removedFaces)
		old.vertCount = math.max(0, (old.vertCount or 0) - (rec.vertsAdded or 0))
		old.chunkMap[key] = nil
		recomputeCollisionFidelity(old)
		markDirty(old)
	end

	return true
end

function MeshPool.unloadChunk(key)
	local rec = CHUNK_INDEX[key]
	if not rec then return false end
	local entry = rec.entry or (rec.poolIdx and POOL[rec.poolIdx]) or nil
	if not entry then
		CHUNK_INDEX[key] = nil
		return false
	end

	if rec.isFixed then
		entry.active = false
		if entry.part then
			entry.part.Parent = nil
		end
		CHUNK_INDEX[key] = nil
		return true
	end

	local removed = removeFaces(entry, rec.faceIds)
	entry.triCount  = math.max(0, (entry.triCount or 0)  - removed)
	entry.vertCount = math.max(0, (entry.vertCount or 0) - (rec.vertsAdded or 0))
	entry.chunkMap[key] = nil
	decrementPreciseCount(entry, rec.lodLevel)
	CHUNK_INDEX[key] = nil

	recomputeCollisionFidelity(entry)

	if (entry.vertCount or 0) > REMOVE_UNUSED_NEAR then
		pcall(function() if entry.em.RemoveUnused then entry.em:RemoveUnused() end end)
	end

	markDirty(entry)
	return true
end

function MeshPool.init(cfg)
	if _initialized then return end
	cfg = cfg or {}; _lastCfg = table.clone and table.clone(cfg) or cfg
	TRI_CAP  = math.max(1000, cfg.TriCap or TRI_CAP)
	MAX_PRECISE_PER_ENTRY = math.max(1, cfg.MaxPrecisePerEntry or MAX_PRECISE_PER_ENTRY)
	local poolSize = math.max(1, cfg.PoolSize or 12)
	MAX_PRECISE_POOL_SLOTS = math.clamp(cfg.PrecisePoolLimit or MAX_PRECISE_POOL_SLOTS, 1, poolSize)
	ensureFolder()
	FIXED_CHUNKS = {}

	for i = 1, poolSize do
		local okEm, em = pcall(function()
			return AssetService:CreateEditableMesh({ FixedSize = false })
		end)
		if not okEm or not em then
			warn("[MeshPool] CreateEditableMesh failed: ", tostring(em))
			return
		end

		local part = Instance.new("MeshPart")
		part.Name = ("PooledMesh_%d"):format(i)
		part.Anchored = true
		part.CastShadow = true
		part.Material = Enum.Material.SmoothPlastic
		part.Color = Color3.new(1,1,1)
		part.CFrame = CFrame.new()
		part.CanCollide = true
		pcall(function() part.UsePartColor = false end)
		part.Parent = ensureFolder()

		POOL[i] = {
			em = em,
			part = part,
			triCount = 0,
			vertCount = 0,
			chunkMap = {},
			palette = nil,
			defaultCid = nil,
			canSetNormal = nil,
			canFaceColors = nil,
			solidCids = {},
			dirty = false,
			applying = false,
			collisionFidelity = nil,
			isFixed = false,
			active = true,
			lodLevel = nil,
			preciseCount = 0,
		}
	end

	_initialized = true
	nextPrecisePoolIndex = 1
	clampPreciseIndex()
	print(string.format("[MeshPool] init: %d pools, TriCap=%d, VertCap<=%d", #POOL, TRI_CAP, VERT_CAP))
end

return MeshPool
