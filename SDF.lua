-- SDF.lua — Signed distance field for DC (flat-ish, Astroneer-like)

local SDF = {}

-- 2D fbm (XZ) for a gentle heightfield
local function fbm2(x, z, freq, gain, octaves)
	local a, f, amp = 0, freq, 1
	for _ = 1, octaves do
		a += math.noise(x * f, 0, z * f) * amp
		f *= 2
		amp *= gain
	end
	return a
end

-- ====== HILL MODULE (sparse bumps) ======
local HILL_SPACING  = 420.0   -- studs between candidate cells
local HILL_RADIUS   = 120.0   -- bump influence radius
local HILL_HEIGHT   = 28.0    -- max added height
local HILL_CHANCE   = 0.6    -- chance a cell gets a hill

local function randCell(ix, iz, sx, sz)
	-- stable pseudo-random in [0,1] from integer cell coords
	return 0.5 + 0.5 * math.noise(ix*12.9898 + sx, 0, iz*78.233 + sz)
end

local function hillBump(x, z)
	-- pick a coarse grid cell
	local ix = math.floor(x / HILL_SPACING)
	local iz = math.floor(z / HILL_SPACING)

	-- sparse gate so only some cells get a hill
	if randCell(ix, iz, 11.1, 22.2) <= (1 - HILL_CHANCE) then
		return 0
	end

	-- jitter hill center within the cell
	local jx = randCell(ix, iz, 33.3, 44.4)
	local jz = randCell(ix, iz, 55.5, 66.6)
	local cx = (ix + jx) * HILL_SPACING
	local cz = (iz + jz) * HILL_SPACING

	-- radial falloff (smoothstep)
	local dx, dz = x - cx, z - cz
	local d = math.sqrt(dx*dx + dz*dz)
	if d >= HILL_RADIUS then return 0 end
	local t = 1 - d / HILL_RADIUS
	local smooth = t*t*(3 - 2*t)
	return smooth * HILL_HEIGHT
end
-- ========================================

-- density < 0 = solid
local AMP, FREQ, GAIN, OCT = 4, 0.02, 0.5, 3

function SDF.density(worldPos: Vector3, baseY: number)
	local base = baseY + fbm2(worldPos.X, worldPos.Z, FREQ, GAIN, OCT) * AMP
	local bump = hillBump(worldPos.X, worldPos.Z)
	local h = base + bump
	return worldPos.Y - h
end

return SDF
