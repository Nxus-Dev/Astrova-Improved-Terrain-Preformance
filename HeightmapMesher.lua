-- HeightmapMesher.lua ? one-layer triangulated grid over XZ
-- Generates (nx+1) x (nz+1) vertices; 2 triangles per cell.

local Heightmap = {}

local function idx(i: number, k: number, nx: number): number
	return k * (nx + 1) + i + 1
end

function Heightmap.generate(params)
	local origin: Vector3   = params.origin
	local voxelSize: number = params.voxelSize
	local nx: number        = params.nx
	local nz: number        = params.nz
	local baseY: number     = params.baseY
	local amp: number       = params.amp or 12
	local scale: number     = params.scale or 0.08

	-- vertices
	local verts = table.create((nx + 1) * (nz + 1))
	for k = 0, nz do
		for i = 0, nx do
			local x = origin.X + i * voxelSize
			local z = origin.Z + k * voxelSize
			local h = baseY + math.noise(x * scale, 0, z * scale) * amp
			verts[idx(i, k, nx)] = Vector3.new(x, h, z)
		end
	end

	-- triangles (consistent winding)
	local tris = {}
	for k = 0, nz - 1 do
		for i = 0, nx - 1 do
			local a = idx(i,     k,     nx)
			local b = idx(i + 1, k,     nx)
			local c = idx(i,     k + 1, nx)
			local d = idx(i + 1, k + 1, nx)
			table.insert(tris, {a, c, b})
			table.insert(tris, {b, c, d})
		end
	end

	return verts, tris
end

return Heightmap