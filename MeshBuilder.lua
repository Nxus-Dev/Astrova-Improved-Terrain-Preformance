-- MeshBuilder.lua ? CLIENT ONLY
-- Faceted low-poly terrain with per-triangle vertex colours.
-- Modes:
--   ? "patch"  : cellular patches (rotated + domain-warped) + optional darker micro-spots
--   ? "astro"  : smooth organic mix
-- Returns a table: { Part = MeshPart, MeshContent = Content, TriCount = N }

local RunService = game:GetService("RunService")
if RunService:IsServer() then
	warn("[MeshBuilder] Called on server; visuals won't replicate. No-op.")
	return { buildMeshPart = function() return nil end }
end

local AssetService = game:GetService("AssetService")
local MeshBuilder = {}

local VERT_CAP = 55000 -- conservative guardrail

-- ----------------- utils -----------------
local function aabb(verts)
	local mn = Vector3.new(math.huge, math.huge, math.huge)
	local mx = Vector3.new(-math.huge, -math.huge, -math.huge)
	for _,v in ipairs(verts) do
		mn = Vector3.new(math.min(mn.X,v.X), math.min(mn.Y,v.Y), math.min(mn.Z,v.Z))
		mx = Vector3.new(math.max(mx.X,v.X), math.max(mx.Y,v.Y), math.max(mx.Z,v.Z))
	end
	return mn, mx
end

local function uvPlanar(p, mn, mx)
	local sx = math.max(1e-6, mx.X - mn.X)
	local sz = math.max(1e-6, mx.Z - mn.Z)
	return Vector2.new((p.X - mn.X)/sx, (p.Z - mn.Z)/sz)
end

local function clamp01(x) return (x<0 and 0) or (x>1 and 1) or x end
local function triCentroid(p1,p2,p3) return (p1 + p2 + p3) / 3 end
local function triNormal(p1,p2,p3)
	local n = (p2 - p1):Cross(p3 - p1)
	if n.Magnitude < 1e-9 then return Vector3.new(0,1,0) end
	return n.Unit
end

local function rot2(x, z, deg)
	local r = math.rad(deg or 0)
	local c, s = math.cos(r), math.sin(r)
	return x*c - z*s, x*s + z*c
end

-- deterministic pseudo-random in [0,1] from integer coords
local function randCell(ix, iz, kx, kz)
	return 0.5*(math.noise(ix*0.331+kx, iz*0.479+kz)+1)
end

-- -------------- palette ------------------
local function makeHSVPalette(em, levels, baseHue, hueJitter, sMin, sMax, vMin, vMax)
	levels    = math.max(2, levels or 24)
	baseHue   = (baseHue ~= nil) and baseHue or 0.33
	hueJitter = hueJitter or 0.008
	sMin, sMax = sMin or 0.62, sMax or 0.78  -- tighter S range (closer colours)
	vMin, vMax = vMin or 0.48, vMax or 0.64  -- tighter V range (less contrast)

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

-- -------- colour pickers -----------------

-- Smooth organic
local function astroIndexForTri(p1,p2,p3, mnY, mxY, levels, cfg)
	levels = math.max(2, levels or 24)
	cfg = cfg or {}
	local c    = triCentroid(p1,p2,p3)
	local n    = triNormal(p1,p2,p3)
	local span = math.max(1e-6, mxY - mnY)
	local tH   = clamp01((c.Y - mnY) / span)
	local ny   = clamp01(n.Y)

	local rf   = cfg.RegionFreq or 0.03
	local df   = cfg.DetailFreq or 0.12
	local n0   = 0.5 * (math.noise(c.X*rf, c.Z*rf) + 1)
	local n1   = 0.5 * (math.noise(c.X*df, c.Z*df) + 1)

	local wH   = cfg.HeightWeight or 0.18
	local wR   = cfg.RegionWeight or 0.62
	local wD   = cfg.DetailWeight or 0.20
	local sD   = cfg.SlopeDarken or 0.10

	local score = wR*n0 + wD*n1 + wH*tH
	score = clamp01(score - sD*(1 - ny))
	local function smoothstep(x) return x*x*(3 - 2*x) end
	score = smoothstep(score)

	return math.clamp(1 + math.floor(score * (levels - 1) + 0.5), 1, levels)
end

-- Cellular patch picker with domain warp (avoids bands)
local function patchIndexForTri(p1,p2,p3, levels, cfg)
	levels = math.max(2, levels or 24)
	cfg = cfg or {}

	local c  = triCentroid(p1,p2,p3)
	-- rotate space first
	local rx, rz = rot2(c.X, c.Z, cfg.RotationDeg or 27)

	-- domain warp
	local wf = cfg.WarpFreq or (1/120)
	local wa = cfg.WarpAmp  or 12.0
	local wx = math.noise(rx*wf, rz*wf) * wa
	local wz = math.noise((rx+97)*wf, (rz-53)*wf) * wa
	rx, rz = rx + wx, rz + wz

	-- cellular patches
	local size = math.max(8, cfg.PatchSize or 80.0)
	local cx, cz = math.floor(rx/size), math.floor(rz/size)

	-- jittered cell center
	local jx = randCell(cx, cz, 0.1, 0.2)
	local jz = randCell(cx, cz, 0.7, 0.9)
	local cx0, cz0 = (cx + jx)*size, (cz + jz)*size

	-- choose base shade per cell
	local baseR = randCell(cx, cz, 1.3, 2.1)
	local idx   = math.clamp(1 + math.floor(baseR * (levels - 1) + 0.5), 1, levels)

	-- micro dark spots
	local dx, dz = rx - cx0, rz - cz0
	local dist   = math.sqrt(dx*dx + dz*dz)
	local spotR  = (cfg.SpotRadius or 0.42) * size
	local chance = cfg.SpotChance or 0.12
	if dist < spotR then
		local gate = randCell(cx, cz, 4.7, 5.9)
		if gate > (1 - chance) then
			local strength = math.max(1, math.floor(cfg.SpotStrength or 3))
			idx = math.max(1, idx - strength)
		end
	end

	-- subtle within-patch drift
	local vf = cfg.VariationFreq or (1/90.0)
	local rr = 0.5 * (math.noise((rx+31)*vf, (rz-17)*vf) + 1)
	local vary = math.floor(cfg.VariationSteps or 1)
	if vary > 0 then
		idx = math.clamp(idx + ((rr<0.5) and -1 or 1)*vary, 1, levels)
	end

	return idx
end

-- -------------- builder ------------------
function MeshBuilder.buildMeshPart(meshData)
	local srcV, srcT = meshData and meshData.Vertices, meshData and meshData.Triangles
	if type(srcV) ~= "table" or #srcV == 0 then warn("MeshBuilder: empty vertices"); return nil end
	if type(srcT) ~= "table" or #srcT == 0 then warn("MeshBuilder: empty triangles"); return nil end

	local makeBackfaces = meshData and meshData.DoubleSided == true

	local estVerts = #srcT * 3 * (makeBackfaces and 2 or 1)
	if estVerts > VERT_CAP and makeBackfaces then
		warn(("[MeshBuilder] est %d > cap %d  building single-sided"):format(estVerts, VERT_CAP))
		makeBackfaces = false
		estVerts = #srcT * 3
	end
	if estVerts > VERT_CAP then
		warn(("[MeshBuilder] est %d still > cap %d  aborting build"):format(estVerts, VERT_CAP))
		return nil
	end

	-- create editable
	local em
	do
		local ok,res = pcall(function() return AssetService:CreateEditableMesh({FixedSize=false}) end)
		if not ok or not res then warn("CreateEditableMesh failed:", res); return nil end
		em = res
	end

	-- vertex colours
	local useVC = meshData and meshData.Colors ~= nil
	local canFaceColors, palette = false, nil
	local cfg  = meshData and meshData.Colors or {}
	local mode = (cfg.Mode or "patch")

	if useVC then
		pcall(function() canFaceColors = (em.SetFaceColors ~= nil) and (em.AddColor ~= nil) end)
		if canFaceColors then
			palette = makeHSVPalette(
				em,
				cfg.Levels or 24,
				cfg.Hue, cfg.HueJitter,
				cfg.SMin, cfg.SMax,
				cfg.VMin, cfg.VMax
			)
			if not palette then
				warn("[MeshBuilder] AddColor failed; disabling vertex colors")
				useVC = false
			end
		else
			useVC = false
		end
	end

	local canSetNormal, canSetUV, canLayerUV = false, false, false
	pcall(function() canSetNormal = (em.SetVertexNormal ~= nil) end)
	pcall(function() canSetUV     = (em.SetVertexUV     ~= nil) end)
	pcall(function() canLayerUV   = (em.CreateUVLayer   ~= nil and em.SetVertexUVInLayer ~= nil) end)

	local uvLayerId
	if (not canSetUV) and canLayerUV then
		pcall(function() uvLayerId = em:CreateUVLayer("uv0") end)
	end

	local mn,mx = aabb(srcV)
	local center = (mn + mx) * 0.5

	local function setUV(v, uv)
		if canSetUV then pcall(function() em:SetVertexUV(v, uv) end)
		elseif uvLayerId then pcall(function() em:SetVertexUVInLayer(uvLayerId, v, uv) end) end
	end

	local function colorFace(fid, p1,p2,p3)
		if not (useVC and canFaceColors and palette) then return end
		local idx
		if mode == "patch" then
			idx = patchIndexForTri(p1,p2,p3, #palette, cfg)
		else
			idx = astroIndexForTri(p1,p2,p3, mn.Y, mx.Y, #palette, cfg)
		end
		local cid = palette[idx] or palette[#palette]
		pcall(function() em:SetFaceColors(fid, {cid, cid, cid}) end)
	end

	local triCount = 0
	local function addTri(p1,p2,p3, makeBackface)
		local area2 = (p2 - p1):Cross(p3 - p1).Magnitude
		if area2 < 5e-10 then return false end

		local v1 = em:AddVertex(p1 - center)
		local v2 = em:AddVertex(p2 - center)
		local v3 = em:AddVertex(p3 - center)

		if canSetNormal then
			local n = triNormal(p1,p2,p3)
			pcall(function()
				em:SetVertexNormal(v1, n); em:SetVertexNormal(v2, n); em:SetVertexNormal(v3, n)
			end)
		end

		local uv1,uv2,uv3 = uvPlanar(p1,mn,mx), uvPlanar(p2,mn,mx), uvPlanar(p3,mn,mx)
		setUV(v1, uv1); setUV(v2, uv2); setUV(v3, uv3)

		local fid = em:AddTriangle(v1, v2, v3)
		colorFace(fid, p1,p2,p3)
		triCount += 1

		if makeBackfaces then
			local vb1 = em:AddVertex(p1 - center)
			local vb2 = em:AddVertex(p2 - center)
			local vb3 = em:AddVertex(p3 - center)
			local fidb = em:AddTriangle(vb3, vb2, vb1)
			colorFace(fidb, p1,p2,p3)
			triCount += 1
		end
		return true
	end

	for _,t in ipairs(srcT) do
		local a,b,c = t[1], t[2], t[3]
		local p1,p2,p3 = srcV[a], srcV[b], srcV[c]
		if p1 and p2 and p3 then addTri(p1,p2,p3, makeBackfaces) end
	end

	-- build MeshPart
	local meshContent = Content.fromObject(em)
	local part
	do
		local ok,res = pcall(function() return AssetService:CreateMeshPartAsync(meshContent) end)
		if not ok or not res then warn("CreateMeshPartAsync failed:", res); return nil end
		part = res
	end

	part.Anchored    = true
	part.Material    = (meshData and meshData.Material) or Enum.Material.SmoothPlastic
	part.Reflectance = 0
	if useVC then
		part.Color = Color3.new(1,1,1)
		pcall(function() part.UsePartColor = false end)
	else
		part.Color = (meshData and meshData.PartColor) or Color3.fromRGB(180,205,255)
		pcall(function() part.UsePartColor = (meshData and meshData.UsePartColor ~= false) end)
	end
	part.CastShadow = (meshData and meshData.CastShadow ~= nil) and meshData.CastShadow or false
	pcall(function() part.LocalTransparencyModifier = 0 end)
	part.CFrame = CFrame.new(center)

	print(string.format("[MeshBuilder] tris=%d mode=%s vertexColors=%s", triCount, mode, tostring(useVC)))
	return { Part = part, MeshContent = meshContent, TriCount = triCount }
end

return MeshBuilder
