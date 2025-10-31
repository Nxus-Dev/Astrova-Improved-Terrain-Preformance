-- ManagerInbox.client.lua
-- Place under: StarterPlayer/StarterPlayerScripts/MesherManagerActor (Actor)
-- This script owns the single MeshPool VM and commits all chunk adds/replaces/unloads.

local ReplicatedStorage = game:GetService("ReplicatedStorage")

local MeshPool = require(ReplicatedStorage.Modules.MeshPool)

-- Initialize once (tune if needed)
-- Initialize the MeshPool with a smaller pool size to reduce memory usage.  A
-- large pool of EditableMeshes can exceed Roblox's memory budget and cause
-- CreateEditableMesh to fail.  Reducing PoolSize from 16 to 8 alleviates
-- those limits while still providing enough capacity for streaming terrain.
-- Increase pool size to allow more independent pooled meshes.  Having more
-- entries lets us distribute nearby chunks across different EditableMeshes,
-- improving collision accuracy for PreciseConvexDecomposition chunks.  The
-- TriCap remains the same; vertex cap is handled internally.
MeshPool.init({
	PoolSize    = 16,
	TriCap      = 19500,
	-- Vert cap handled inside MeshPool.lua itself
})

-- Markers -----------------------------------------------------------
local function getChunkFolder()
	local f = workspace:FindFirstChild("ClientChunks")
	if not f then
		f = Instance.new("Folder")
		f.Name = "ClientChunks"
		f.Parent = workspace
	end
	return f
end

local function markerAliveWithNonce(key: string, nonce: number)
	local f = workspace:FindFirstChild("ClientChunks")
	if not f then return false end
	local v = f:FindFirstChild(key)
	if not v then return false end
	return v:GetAttribute("JobNonce") == nonce
end

local function finalizeMarker(key: string, nonce: number)
	local f = workspace:FindFirstChild("ClientChunks")
	if not f then return end
	local v = f:FindFirstChild(key)
	if not v then return end
	if v:GetAttribute("JobNonce") ~= nonce then return end
	v.Value = true
	v:SetAttribute("Pending", false)
end

-- If you want absolute zero overlap even on failure, set to true.
local STRICT_SWAP = false

-- Inbox: commit from workers ---------------------------------------
script.Parent:BindToMessage("commitChunk", function(payload)
	if type(payload) ~= "table" then return end
	local key   = payload.Key
	local verts = payload.Verts
	local tris  = payload.Tris
	local opts  = payload.Opts or {}
	local nonce = payload.Nonce

	if not key or type(verts) ~= "table" or type(tris) ~= "table" then
		warn("[ManagerInbox] Bad payload")
		return
	end

	-- Stale job? (newer nonce owns the key)
	if nonce and not markerAliveWithNonce(key, nonce) then
		return
	end

	if STRICT_SWAP then
		pcall(function() MeshPool.unloadChunk(key) end)
	end

	local ok = MeshPool.addOrReplaceChunk(key, verts, tris, opts)
	if not ok then
		warn("[ManagerInbox] addOrReplace failed for", key)
		return
	end

	if nonce then
		finalizeMarker(key, nonce)
	end
end)

-- Inbox: unload from ChunkManager ----------------------------------
script.Parent:BindToMessage("unloadChunk", function(payload)
	local key = payload and payload.Key
	if not key then return end
	pcall(function() MeshPool.unloadChunk(key) end)
end)
