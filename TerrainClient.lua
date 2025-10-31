-- TerrainClient.lua  (CLIENT)
-- - Sets up matte/flat lighting (kills shine)
-- - Streams Dual Contouring chunks using ChunkManager + LOD (+ MeshPool is auto-inited in Worker)

local Players            = game:GetService("Players")
local ReplicatedStorage  = game:GetService("ReplicatedStorage")
local RunService         = game:GetService("RunService")
local Lighting           = game:GetService("Lighting")

--------------------------------------------------------------------------------
-- Lighting: choose how matte you want things
--------------------------------------------------------------------------------
-- "flat"  = super flat (no specular, no diffuse, no shadows)
-- "matte" = no specular, a tiny bit of diffuse so shapes still read
local LIGHTING_MODE = "flat"  -- "flat" or "matte"

local function setupLighting(mode)
	-- turn off post effects that add sheen
	for _,e in ipairs(Lighting:GetChildren()) do
		if e:IsA("BloomEffect") or e:IsA("SunRaysEffect") then
			e.Enabled = false
		end
	end

	if mode == "flat" then
		Lighting.EnvironmentSpecularScale = 0
		Lighting.EnvironmentDiffuseScale  = 0
		Lighting.GlobalShadows            = false
		Lighting.Brightness               = 1
		Lighting.Ambient                  = Color3.fromRGB(185,190,185)
		pcall(function() Lighting.OutdoorAmbient = Lighting.Ambient end)
	else -- matte
		Lighting.EnvironmentSpecularScale = 0
		Lighting.EnvironmentDiffuseScale  = 0.12
		Lighting.GlobalShadows            = true
		Lighting.Brightness               = 1
		Lighting.Ambient                  = Color3.fromRGB(170,175,170)
		pcall(function() Lighting.OutdoorAmbient = Lighting.Ambient end)
	end
end

setupLighting(LIGHTING_MODE)

--------------------------------------------------------------------------------
-- DC streaming settings
--------------------------------------------------------------------------------
local SETTINGS = {
	VoxelSize     = 4,     -- studs per voxel (base)
	CellsPerAxis  = 64,    -- chunk width/length in cells (base)
	YCells        = 20,    -- chunk height in cells (one vertical band)

	-- Visible square (render distance) in rings.  With a large render radius,
	-- many chunks will be streamed.  Setting this to 10 provides a 21×21
	-- grid of chunks around the player.  Combine with larger LOD bands to
	-- reduce detail as distance increases.
	RenderRadius  = 10,

	-- Also used to pre-UPGRADE adjacent chunks to highest LOD before stepping in.
	PreloadEdge   = 50,
	-- Max number of worker Actors.  Increase this to allow more concurrent
	-- Dual Contouring jobs when rendering a larger radius.  Be mindful of
	-- memory limits; each worker holds geometry for its current job.
	MaxWorkers    = 16,

	-- How frequently to update the streaming logic (seconds).  Lower this
	-- value to dispatch new chunk jobs more often, which can help when
	-- increasing MaxWorkers or RenderRadius.  Values below ~0.10 may
	-- introduce overhead; adjust as needed.
	UpdateInterval = 0.15,

	-- LOD bands (Chebyshev ring distance).  For large render distances we
	-- progressively decrease the resolution of far chunks to keep generation
	-- time and memory manageable.  Each band specifies the maximum ring
	-- distance and the voxel factor (CellsPerAxis / factor).  For example,
	-- factor 4 produces 16×16×5 cells; factor 12 produces ~5×5×2 cells.
	LODBands = {
		{ maxDist = 1,  factor = 4  }, -- ring 0–1: high detail
		{ maxDist = 3,  factor = 6  }, -- rings 2–3
		{ maxDist = 6,  factor = 8  }, -- rings 4–6
		{ maxDist = 10, factor = 12 }, -- rings 7–10
		{ maxDist = math.huge, factor = 16 }, -- beyond: very coarse
	},
}

-- Actor template must exist: ReplicatedStorage.MesherActorTemplate (Actor)
local actorTemplate = ReplicatedStorage:FindFirstChild("MesherActorTemplate")
assert(actorTemplate and actorTemplate:IsA("Actor"),
	"Missing ReplicatedStorage.MesherActorTemplate (Actor)")

-- Modules
local ChunkManager = require(ReplicatedStorage.Modules.ChunkManager)
-- NOTE: We no longer init MeshPool here; Worker auto-inits inside its VM.

-- Create manager
local mgr = ChunkManager.new(actorTemplate, SETTINGS)

--------------------------------------------------------------------------------
-- Camera and control setup
--------------------------------------------------------------------------------
-- Camera and control setup
-- (The default camera settings are used.  If you wish to lock the camera to
-- first-person, you can set `player.CameraMode = Enum.CameraMode.LockFirstPerson`
-- in a separate local script.)

--------------------------------------------------------------------------------
-- Player focus position (HRP)
--------------------------------------------------------------------------------
local function focusPos()
	local plr = Players.LocalPlayer
	if not plr then return Vector3.zero end
	local char = plr.Character
	if not char then return Vector3.zero end
	local hrp = char:FindFirstChild("HumanoidRootPart")
	return hrp and hrp.Position or Vector3.zero
end

--------------------------------------------------------------------------------
-- Kick off initial stream and keep it updated
--------------------------------------------------------------------------------
-- Do an immediate prime so you don't see a blank frame
task.defer(function()
	mgr:updateAround(focusPos())
end)

-- Stream as you walk; small cadence so preloading feels snappy
local acc = 0
RunService.RenderStepped:Connect(function(dt)
	acc += dt
	local interval = SETTINGS.UpdateInterval or 0.15
	if acc > interval then
		acc = 0
		mgr:updateAround(focusPos())
	end
end)

print(string.format(
	"[TerrainClient] DC streaming + LOD ? BaseVox=%d Cells=%d Y=%d Radius=%d Preload=%d (Lighting=%s)",
	SETTINGS.VoxelSize, SETTINGS.CellsPerAxis, SETTINGS.YCells, SETTINGS.RenderRadius,
	SETTINGS.PreloadEdge, LIGHTING_MODE
	))
