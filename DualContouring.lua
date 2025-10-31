-- DualContouring.lua ? Surface Nets DC with 1-cell halo, oriented faces + robust fallbacks.
-- Solid if density < 0. Half-open in X/Z; closed in Y.

local DC = {}

local CORNERS = {
	Vector3.new(0,0,0), Vector3.new(1,0,0), Vector3.new(0,1,0), Vector3.new(1,1,0),
	Vector3.new(0,0,1), Vector3.new(1,0,1), Vector3.new(0,1,1), Vector3.new(1,1,1),
}
local EDGES = {
	{1,2},{1,3},{1,5},{2,4},{2,6},{3,4},{3,7},{4,8},{5,6},{5,7},{6,8},{7,8}
}

local function snapVec3(p: Vector3, step: number)
	local function r(x, s) return math.round(x / s) * s end
	return Vector3.new(r(p.X, step), r(p.Y, step), r(p.Z, step))
end

-- params: origin, cellSize, nx, ny, nz, densityFn
--   snapStep? = 6e-4, signEps? = 0.01, halfOpenXZ? = true, closeY? = true
function DC.generate(params)
	local origin, h = params.origin, params.cellSize
	local nx, ny, nz = params.nx, params.ny, params.nz
	local densityFn  = params.densityFn
	local snapStep   = params.snapStep or 6e-4
	local signEps    = params.signEps  or 0.01
	local halfXZ     = (params.halfOpenXZ ~= false)
	local closeY     = (params.closeY ~= false)

	local minX, minY, minZ = origin.X, origin.Y, origin.Z
	local maxX, maxY, maxZ = origin.X + nx*h, origin.Y + ny*h, origin.Z + nz*h

	-- generous tolerances; Y looser so floor/ceiling never get culled post-snap
	local baseTol = math.max(1e-6, snapStep*4, h*1e-3)
	local xzTol   = baseTol * 6
	local yTol    = baseTol * 10

	local function insideForKeep(p: Vector3)
		local xok = halfXZ and (p.X >= minX - xzTol and p.X <  maxX - xzTol)
			or       (p.X >= minX - xzTol and p.X <= maxX + xzTol)
		local zok = halfXZ and (p.Z >= minZ - xzTol and p.Z <  maxZ - xzTol)
			or       (p.Z >= minZ - xzTol and p.Z <= maxZ + xzTol)
		local yok = (not closeY) or (p.Y >= minY - yTol and p.Y <= maxY + yTol)
		return xok and yok and zok
	end

	-- 1) sample with 1-cell halo
	local cx, cy, cz = nx + 2, ny + 2, nz + 2
	local lx, ly, lz = cx + 1, cy + 1, cz + 1
	local sampleOrigin = origin - Vector3.new(h, h, h)

	local function Gindex(i, j, k) return ((k)*ly + j)*lx + i + 1 end
	local G = table.create(lx * ly * lz)
	local S = table.create(lx * ly * lz)

	for k = 0, lz - 1 do
		for j = 0, ly - 1 do
			for i = 0, lx - 1 do
				local wp = sampleOrigin + Vector3.new(i, j, k) * h
				local d  = densityFn(wp)
				if math.abs(d) < signEps then d = (d <= 0) and -signEps or signEps end
				local idx = Gindex(i,j,k)
				G[idx] = d
				S[idx] = (d < 0)
			end
		end
	end
	local function D(i,j,k) return G[Gindex(i,j,k)] end
	local function Sign(i,j,k) return S[Gindex(i,j,k)] end

	-- 2) one vertex per mixed-sign extended cell
	local function Cindex(i, j, k) return ((k)*cy + j)*cx + i + 1 end
	local cellVertIndex = table.create(cx * cy * cz)
	local Verts = {}

	local function lerpEdge(p1, p2, d1, d2)
		local t = d1 / (d1 - d2)
		if t < 0 then t = 0 elseif t > 1 then t = 1 end
		return p1 + (p2 - p1) * t
	end

	for k = 0, cz - 1 do
		for j = 0, cy - 1 do
			for i = 0, cx - 1 do
				local s0 = Sign(i, j, k)
				local mixed = false
				for c = 2, 8 do
					local off = CORNERS[c]
					if Sign(i + off.X, j + off.Y, k + off.Z) ~= s0 then mixed = true; break end
				end
				if mixed then
					local acc, cnt = Vector3.zero, 0
					for e = 1, #EDGES do
						local a, b = EDGES[e][1], EDGES[e][2]
						local oa, ob = CORNERS[a], CORNERS[b]
						local ia, ib = Vector3.new(i, j, k) + oa, Vector3.new(i, j, k) + ob
						local da, db = D(ia.X, ia.Y, ia.Z), D(ib.X, ib.Y, ib.Z)
						if (da < 0 and db > 0) or (da > 0 and db < 0) then
							local p1 = sampleOrigin + Vector3.new(ia.X, ia.Y, ia.Z) * h
							local p2 = sampleOrigin + Vector3.new(ib.X, ib.Y, ib.Z) * h
							acc += lerpEdge(p1, p2, da, db); cnt += 1
						end
					end
					if cnt > 0 then
						local v = snapVec3(acc / cnt, snapStep)
						Verts[#Verts+1] = v
						cellVertIndex[Cindex(i, j, k)] = #Verts
					end
				end
			end
		end
	end

	-- 3) oriented faces + robust fallbacks
	local Tris = {}
	local function tri(a,b,c) Tris[#Tris+1] = {a,b,c} end
	local function center4(a,b,c,d) return (Verts[a]+Verts[b]+Verts[c]+Verts[d]) * 0.25 end

	local function emitFace(vs, flip, axis)
		local n = 0
		for i=1,4 do if vs[i] then n += 1 end end
		if n == 0 then return end

		if n == 4 then
			if flip then tri(vs[1],vs[3],vs[2]); tri(vs[1],vs[4],vs[3])
			else         tri(vs[1],vs[2],vs[3]); tri(vs[1],vs[3],vs[4]) end
			return
		end
		if n == 3 then
			local w = {}
			for i=1,4 do if vs[i] then w[#w+1]=vs[i] end end
			if flip then tri(w[1],w[3],w[2]) else tri(w[1],w[2],w[3]) end
			return
		end
		if n == 2 then
			local w = {}
			for i=1,4 do if vs[i] then w[#w+1]=vs[i] end end
			local a,b = w[1], w[2]
			local pa,pb = Verts[a], Verts[b]
			local dir = pb - pa
			if dir.Magnitude > 1e-9 then
				dir = dir.Unit
				local t = (axis == "x") and Vector3.new(0,0,1)
					or (axis == "z") and Vector3.new(1,0,0)
					or Vector3.new(1,0,0)
				if math.abs(dir:Dot(t)) > 0.95 then t = Vector3.new(0,0,1) end
				local half = math.max(h*0.5, math.min(h*0.8, (pb-pa).Magnitude*0.49))
				local mid  = (pa + pb) * 0.5
				local m1   = snapVec3(mid + t*half, snapStep)
				local m2   = snapVec3(mid - t*half, snapStep)
				Verts[#Verts+1] = m1; local i1 = #Verts
				Verts[#Verts+1] = m2; local i2 = #Verts
				if flip then tri(a,i2,i1); tri(a,b,i2) else tri(a,i1,i2); tri(a,i2,b) end
			end
			return
		end
		-- n == 1
		local a = vs[1] or vs[2] or vs[3] or vs[4]
		local p0 = Verts[a]
		local off1 = (axis == "y") and Vector3.new(h*0.25,0,0) or Vector3.new(0,0,h*0.25)
		local off2 = (axis == "y") and Vector3.new(0,0,h*0.25) or Vector3.new(h*0.25,0,0)
		local m1 = snapVec3(p0 + off1, snapStep)
		local m2 = snapVec3(p0 + off2, snapStep)
		Verts[#Verts+1] = m1; local i1 = #Verts
		Verts[#Verts+1] = m2; local i2 = #Verts
		if flip then tri(a,i2,i1) else tri(a,i1,i2) end
	end

	-- X planes (default +X; flip if right side is solid) ? no side culling
	for px = 1, nx + 1 do
		for j = 1, ny + 1 do
			for k = 1, nz + 1 do
				local sL, sR = Sign(px-1, j, k), Sign(px, j, k)
				if sL ~= sR then
					local vs = {
						cellVertIndex[Cindex(px-1, j-1, k-1)],
						cellVertIndex[Cindex(px-1, j,   k-1)],
						cellVertIndex[Cindex(px-1, j,   k  )],
						cellVertIndex[Cindex(px-1, j-1, k  )],
					}
					emitFace(vs, sR, "x")
				end
			end
		end
	end

	-- Y planes (default -Y; flip if below is solid ? ground points up)
	for py = 1, ny + 1 do
		for i = 1, nx + 1 do
			for k = 1, nz + 1 do
				local sB, sT = Sign(i, py-1, k), Sign(i, py, k)
				if sB ~= sT then
					local vs = {
						cellVertIndex[Cindex(i-1, py-1, k-1)],
						cellVertIndex[Cindex(i,   py-1, k-1)],
						cellVertIndex[Cindex(i,   py-1, k  )],
						cellVertIndex[Cindex(i-1, py-1, k  )],
					}
					local isBottom = (py == 1)
					local isTop    = (py == ny + 1)
					local keep = false
					if vs[1] and vs[2] and vs[3] and vs[4] then
						if isBottom or isTop then keep = true
						else
							local ctr = center4(vs[1],vs[2],vs[3],vs[4])
							keep = (ctr.Y >= minY - yTol) and (ctr.Y <= maxY + yTol)
						end
					else
						keep = true -- allow fallbacks
					end
					if keep then emitFace(vs, sB, "y") end
				end
			end
		end
	end

	-- Z planes (default +Z; flip if back is solid) ? no side culling
	for pz = 1, nz + 1 do
		for i = 1, nx + 1 do
			for j = 1, ny + 1 do
				local sF, sBk = Sign(i, j, pz-1), Sign(i, j, pz)
				if sF ~= sBk then
					local vs = {
						cellVertIndex[Cindex(i-1, j-1, pz-1)],
						cellVertIndex[Cindex(i,   j-1, pz-1)],
						cellVertIndex[Cindex(i,   j,   pz-1)],
						cellVertIndex[Cindex(i-1, j,   pz-1)],
					}
					emitFace(vs, sBk, "z")
				end
			end
		end
	end

	return Verts, Tris
end

return DC
