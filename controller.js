// battle.training — "Hoocy" v4 controller (Armor, Season 2 s2.0.0)
//
// Preserves v3's survival & weighted Dijkstra pathfinding core, upgrading
// hill control and direct-fire accuracy against top Cup opponents:
//   1. EXACT ELEVATION FIRE & TRAJECTORY CLEARANCE: Pass [fx, fy] aim points
//      for direct guns (with post-turn/post-move tolerance check) so elevatedFire
//      pitches shells to target height, paired with exact shell-step lane
//      checks and per-unit target fallback when focus is blocked.
//   2. ANTI-WHIPLASH & APC-HILL PRIORITY: Keep MBTs committed near active sieges
//      (hysteresis + inferred APC-farm priority), plus stall-breaking pushes and
//      blind-ambush HP-drop counter-spotting.
//   3. BIDIRECTIONAL FULL-SPEED DRONE EVASION & HOLD DISCIPLINE: Hysteresis-gated
//      forward/reverse full-speed escape with sticky wall-safe orbit tangents,
//      opening leash, and non-abandoning hill hold on Comeback/Anchor/Flex.

const FP = 65536;
const FULL = 4096;
const TWO_PI = Math.PI * 2;
const ANG_TO_RAD = TWO_PI / FULL;

// Per-match static map & precomputed flow data
let rules, map, side, W, H, N;
let terrainSpeedArr, passableGrid, heightsArr, terrainArr, fogArr;
let objFields = [];
let enemySpawnField = null;
let homeIdx = 0, farIdx = 0, centreIdx = -1;
let totalWeight = 1;
let mySpawn = [0, 0], enemySpawn = [0, 0], mapCentre = [0, 0];

// Dynamic tick state
let mem = {};
let lastScore = [0, 0];
let myRate = 0, enRate = 0;
let rateHistMy = [], rateHistEn = [];
let focusId = 0;
let blockedCnt = {};
let backoffState = {};
let forestGoal = {};
let committedStrikeIdx = -1;
let droneOrbitSign = {};
let droneFlipTick = {};
let comebackObj = {};
let mbtStallTicks = {};
let mbtAdvanceUntil = {};
let lastDamageTick = -999;
let prevUnitHp = {};
let blindHitTick = -999;
let blindHitPos = null;
let blindUnitTick = {};

const DRAFT_PICK = ["mbt", "mbt", "drone", "drone"];

function dist(ax, ay, bx, by) { return Math.hypot(bx - ax, by - ay); }
function angleTo(ax, ay, bx, by) {
  return Math.round(Math.atan2(by - ay, bx - ax) / ANG_TO_RAD) & (FULL - 1);
}
function angDiff(a, b) {
  const d = (b - a) & (FULL - 1);
  return d > FULL / 2 ? d - FULL : d;
}
function clampCoord(x, y) {
  const pad = FP;
  return [
    Math.max(pad, Math.min(W * FP - pad, Math.round(x))),
    Math.max(pad, Math.min(H * FP - pad, Math.round(y))),
  ];
}
function tileAt(x, y) {
  const tx = Math.floor(x / FP), ty = Math.floor(y / FP);
  if (tx < 0 || ty < 0 || tx >= W || ty >= H) return -1;
  return terrainArr[ty * W + tx];
}
function heightAtTile(tx, ty) {
  if (tx < 0) tx = 0; else if (tx >= W) tx = W - 1;
  if (ty < 0) ty = 0; else if (ty >= H) ty = H - 1;
  return heightsArr[ty * W + tx];
}
function heightAt(x, y) {
  return heightAtTile(Math.floor(x / FP), Math.floor(y / FP));
}
function isTilePassable(tx, ty) {
  if (tx < 0 || ty < 0 || tx >= W || ty >= H) return false;
  return passableGrid[ty * W + tx] === 1;
}
function passable(x, y) {
  return isTilePassable(Math.floor(x / FP), Math.floor(y / FP));
}
function tileMoveCost(t) {
  if (t === 5) return 6;   // road x1.6
  if (t === 3) return 17;  // ford x0.6
  if (t === 1) return 20;  // forest x0.5
  return 10;               // plain / bridge x1.0
}

/** Binary min-heap weighted 8-neighbor Dijkstra in hello() over flat Int32Arrays. */
function buildExactDijkstraField(seedIndices) {
  const dArr = new Int32Array(N);
  dArr.fill(0x3fffffff);
  const heapDist = new Int32Array(N * 2);
  const heapNode = new Int32Array(N * 2);
  let heapLen = 0;

  for (let i = 0; i < seedIndices.length; i++) {
    const idx = seedIndices[i];
    if (dArr[idx] === 0) continue;
    dArr[idx] = 0;
    let c = heapLen++;
    heapDist[c] = 0;
    heapNode[c] = idx;
    while (c > 0) {
      const p = (c - 1) >> 1;
      if (heapDist[p] <= heapDist[c]) break;
      const td = heapDist[p], tn = heapNode[p];
      heapDist[p] = heapDist[c]; heapNode[p] = heapNode[c];
      heapDist[c] = td; heapNode[c] = tn;
      c = p;
    }
  }

  const dxArr = [1, -1, 0, 0, 1, 1, -1, -1];
  const dyArr = [0, 0, 1, -1, 1, -1, 1, -1];
  const baseArr = [10, 10, 10, 10, 14, 14, 14, 14];

  while (heapLen > 0) {
    const du = heapDist[0];
    const u = heapNode[0];
    heapLen--;
    if (heapLen > 0) {
      heapDist[0] = heapDist[heapLen];
      heapNode[0] = heapNode[heapLen];
      let p = 0;
      while (true) {
        let best = p;
        const l = p * 2 + 1, r = l + 1;
        if (l < heapLen && heapDist[l] < heapDist[best]) best = l;
        if (r < heapLen && heapDist[r] < heapDist[best]) best = r;
        if (best === p) break;
        const td = heapDist[p], tn = heapNode[p];
        heapDist[p] = heapDist[best]; heapNode[p] = heapNode[best];
        heapDist[best] = td; heapNode[best] = tn;
        p = best;
      }
    }
    if (du !== dArr[u]) continue;
    const ux = u % W, uy = (u / W) | 0;
    const hu = heightsArr[u];
    const costU = tileMoveCost(terrainArr[u]);

    for (let k = 0; k < 8; k++) {
      const dx = dxArr[k], dy = dyArr[k];
      const nx = ux + dx, ny = uy + dy;
      if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
      const v = ny * W + nx;
      if (!passableGrid[v]) continue;
      if (dx !== 0 && dy !== 0) {
        if (!passableGrid[uy * W + nx] || !passableGrid[ny * W + ux]) continue;
      }
      const hv = heightsArr[v];
      const dh = Math.max(0, hu - hv);
      const upPen = dh > 0 ? Math.min(18, dh >> 1) : 0;
      const stepCost = Math.max(1, ((baseArr[k] * (costU + tileMoveCost(terrainArr[v]))) / 20 | 0) + upPen);
      const alt = du + stepCost;
      if (alt < dArr[v]) {
        dArr[v] = alt;
        let c = heapLen++;
        heapDist[c] = alt;
        heapNode[c] = v;
        while (c > 0) {
          const p = (c - 1) >> 1;
          if (heapDist[p] <= heapDist[c]) break;
          const td = heapDist[p], tn = heapNode[p];
          heapDist[p] = heapDist[c]; heapNode[p] = heapNode[c];
          heapDist[c] = td; heapNode[c] = tn;
          c = p;
        }
      }
    }
  }
  return dArr;
}

function nearestPassableTileCoords(gx, gy) {
  if (isTilePassable(gx, gy)) return [gx, gy];
  for (let r = 1; r <= 12; r++) {
    for (let dy = -r; dy <= r; dy++) {
      for (let dx = -r; dx <= r; dx++) {
        if (Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue;
        if (isTilePassable(gx + dx, gy + dy)) return [gx + dx, gy + dy];
      }
    }
  }
  return [gx, gy];
}

function segmentDistSq(ax, ay, bx, by, px, py) {
  const dx = bx - ax, dy = by - ay;
  const len2 = dx * dx + dy * dy;
  if (len2 <= 1) return (px - ax) * (px - ax) + (py - ay) * (py - ay);
  const t = Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / len2));
  const cx = ax + dx * t - px, cy = ay + dy * t - py;
  return cx * cx + cy * cy;
}

function exactShellClears(sx, sy, spec, tx, ty, tgtRadius) {
  if (!spec || !spec.gun || spec.gun.mode !== "direct") return false;
  const dx = tx - sx, dy = ty - sy;
  const d = Math.hypot(dx, dy);
  if (d < 1) return true;
  const ux = dx / d, uy = dy / d;
  const speed = spec.gun.shellSpeed || 3 * FP;
  const startOff = (spec.radius || 0.75 * FP) + 0.2 * FP;
  const hitR = (tgtRadius || 0.75 * FP) + 0.15 * FP;
  if (d <= startOff + hitR) return true;
  let x = sx + ux * startOff, y = sy + uy * startOff;
  let z = heightAt(sx, sy) + spec.eyeHeight;
  const cx = Math.max(0, Math.min(W * FP - 1, tx));
  const cy = Math.max(0, Math.min(H * FP - 1, ty));
  const remD = Math.max(1, Math.hypot(cx - x, cy - y));
  const zt = heightAt(cx, cy) + 3;
  const dz = rules.elevatedFire ? Math.round(((zt - z) * speed) / remD) : 0;
  const vx = ux * speed, vy = uy * speed;
  const hitR2 = hitR * hitR;
  const maxForest = rules.forestStopsShellsAfter ?? 4;
  const maxTicks = Math.min(35, Math.ceil((remD + hitR) / speed) + 1);
  let forest = 0;

  for (let t = 0; t < maxTicks; t++) {
    const ox = x, oy = y;
    x += vx; y += vy; z += dz;
    if (segmentDistSq(ox, oy, x, y, tx, ty) <= hitR2) return true;
    if (x < 0 || y < 0 || x >= W * FP || y >= H * FP) return false;
    const ntx = Math.floor(x / FP), nty = Math.floor(y / FP);
    const otx = Math.floor(ox / FP), oty = Math.floor(oy / FP);
    const ter = terrainArr[nty * W + ntx];
    if (ter === 1 && (ntx !== otx || nty !== oty)) {
      forest++;
      if (maxForest > 0 && forest >= maxForest) return false;
    }
    if (heightsArr[nty * W + ntx] > z || ter === 6) return false;
  }
  return false;
}

function hasClearShot(sx, sy, eyeH, tx, ty) {
  const dx = tx - sx, dy = ty - sy;
  const dTiles = Math.hypot(dx, dy) / FP;
  const steps = Math.max(2, Math.ceil(dTiles * 1.4));
  const z0 = heightAt(sx, sy) + eyeH;
  const z1 = heightAt(tx, ty) + 3;
  const maxForest = rules.forestStopsShellsAfter ?? 4;
  let forestCount = 0;
  let prevTile = Math.floor(sy / FP) * W + Math.floor(sx / FP);

  for (let i = 1; i < steps; i++) {
    const t = i / steps;
    const ptx = Math.floor((sx + dx * t) / FP), pty = Math.floor((sy + dy * t) / FP);
    if (ptx < 0 || pty < 0 || ptx >= W || pty >= H) return false;
    const idx = pty * W + ptx;
    const ter = terrainArr[idx];
    if (ter === 4 || ter === 6) return false;
    if (idx !== prevTile) {
      if (ter === 1 && ++forestCount >= maxForest) return false;
      prevTile = idx;
    }
    if (heightsArr[idx] > z0 + (z1 - z0) * t) return false;
  }
  return true;
}

function linePassable(ax, ay, bx, by) {
  const steps = Math.max(2, Math.ceil(dist(ax, ay, bx, by) / (FP * 0.55)));
  for (let i = 1; i <= steps; i++) {
    const t = i / steps;
    if (!passable(ax + (bx - ax) * t, ay + (by - ay) * t)) return false;
  }
  return true;
}

function effectiveMaxRange(u, spec, tx, ty) {
  let maxR = spec.gun.maxRange;
  const ha = rules.heightAdvantage;
  if (ha && maxR > 0) {
    const ang = Math.atan2(ty - u.y, tx - u.x);
    const fx0 = Math.max(0, Math.min(W * FP - 1, u.x + Math.cos(ang) * maxR));
    const fy0 = Math.max(0, Math.min(H * FP - 1, u.y + Math.sin(ang) * maxR));
    if (heightAt(u.x, u.y) - heightAt(fx0, fy0) >= ha.minDelta) {
      maxR = Math.floor((maxR * ha.rangeBonus) / FP);
    }
  }
  return maxR;
}

function predict(c, leadTicks) {
  if (!c.speed) return [c.x, c.y];
  const rad = c.heading * ANG_TO_RAD;
  return clampCoord(c.x + Math.cos(rad) * c.speed * leadTicks, c.y + Math.sin(rad) * c.speed * leadTicks);
}

function computeObjectiveSpots(o) {
  const ox = o.x, oy = o.y, rad = o.radius;
  const innerCombat = Math.max(FP, rad - 1.35 * FP);
  const innerSafe = Math.max(FP, rad - 2.0 * FP);
  const tx0 = Math.max(0, Math.floor((ox - rad) / FP));
  const tx1 = Math.min(W - 1, Math.floor((ox + rad) / FP));
  const ty0 = Math.max(0, Math.floor((oy - rad) / FP));
  const ty1 = Math.min(H - 1, Math.floor((oy + rad) / FP));

  const refX = (enemySpawn[0] + mapCentre[0]) * 0.5;
  const refY = (enemySpawn[1] + mapCentre[1]) * 0.5;
  const awayAng = Math.atan2(oy - refY, ox - refX);

  const cands = [];
  for (let ty = ty0; ty <= ty1; ty++) {
    for (let tx = tx0; tx <= tx1; tx++) {
      if (!isTilePassable(tx, ty)) continue;
      const cx = tx * FP + FP / 2, cy = ty * FP + FP / 2;
      const dC = dist(cx, cy, ox, oy);
      if (dC > innerCombat) continue;
      const ter = terrainArr[ty * W + tx];
      const h = heightsArr[ty * W + tx];
      const clearToCentre = hasClearShot(cx, cy, 5, mapCentre[0], mapCentre[1]) ? 1 : 0;
      const clearToEnemy = hasClearShot(cx, cy, 5, enemySpawn[0], enemySpawn[1]) ? 1 : 0;
      const safeAlign = Math.cos(Math.atan2(cy - oy, cx - ox) - awayAng) * (dC / Math.max(1, innerCombat));
      cands.push({ x: cx, y: cy, ter, h, dC, clearToCentre, clearToEnemy, safeAlign });
    }
  }
  if (!cands.length) {
    const np = nearestPassableTileCoords(Math.floor(ox / FP), Math.floor(oy / FP));
    const p = [np[0] * FP + FP / 2, np[1] * FP + FP / 2];
    return { combatSpot: p, anchorSpot: p, flankSpot: p };
  }

  let bestCombat = cands[0], bestCS = -1e9;
  for (const c of cands) {
    const s = (c.ter === 1 ? 35 : 0) + c.clearToCentre * 25 + c.clearToEnemy * 15 + c.h * 0.25 - (c.dC / FP) * 2;
    if (s > bestCS) { bestCS = s; bestCombat = c; }
  }

  let bestAnchor = cands[0], bestAS = -1e9;
  for (const c of cands) {
    if (c.dC > innerSafe && cands.some((x) => x.dC <= innerSafe)) continue;
    const sep = dist(c.x, c.y, bestCombat.x, bestCombat.y) / FP;
    const s = c.safeAlign * 24 + (c.ter === 1 ? 12 : 0) + (sep >= 2.5 ? 14 : sep * 4) - (c.dC / FP) * 2.5;
    if (s > bestAS) { bestAS = s; bestAnchor = c; }
  }

  let bestFlank = cands[0], bestFS = -1e9;
  for (const c of cands) {
    const minS = Math.min(dist(c.x, c.y, bestCombat.x, bestCombat.y), dist(c.x, c.y, bestAnchor.x, bestAnchor.y)) / FP;
    const s = minS * 12 + (c.ter === 1 ? 10 : 0) + c.clearToCentre * 8 + c.h * 0.15;
    if (s > bestFS) { bestFS = s; bestFlank = c; }
  }

  return {
    combatSpot: [bestCombat.x, bestCombat.y],
    anchorSpot: [bestAnchor.x, bestAnchor.y],
    flankSpot: [bestFlank.x, bestFlank.y],
  };
}

function flowTarget(u, field, exactGoal, alive) {
  const tx = Math.floor(u.x / FP), ty = Math.floor(u.y / FP);
  if (tx < 0 || ty < 0 || tx >= W || ty >= H) return exactGoal;
  const dHere = field[ty * W + tx];
  if (dHere <= 0 || dHere >= 0x3ffffff0) return exactGoal;
  if (dist(u.x, u.y, exactGoal[0], exactGoal[1]) < 6.0 * FP && linePassable(u.x, u.y, exactGoal[0], exactGoal[1])) {
    return exactGoal;
  }

  const pickBestNb = (cx, cy, withUnitSep) => {
    let bScore = 0x3fffffff, bx = cx, by = cy;
    for (let dy = -1; dy <= 1; dy++) {
      for (let dx = -1; dx <= 1; dx++) {
        if (dx === 0 && dy === 0) continue;
        const nx = cx + dx, ny = cy + dy;
        if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
        if (!passableGrid[ny * W + nx]) continue;
        if (dx !== 0 && dy !== 0 && (!passableGrid[cy * W + nx] || !passableGrid[ny * W + cx])) continue;
        let sc = field[ny * W + nx];
        if (withUnitSep) {
          for (let i = 0; i < alive.length; i++) {
            const f = alive[i];
            if (f.id === u.id || rules.units[f.kind].air) continue;
            if (Math.floor(f.x / FP) === nx && Math.floor(f.y / FP) === ny) sc += 25;
          }
        }
        if (sc < bScore) { bScore = sc; bx = nx; by = ny; }
      }
    }
    return [bx, by];
  };

  let cx = tx, cy = ty;
  let bestPt = null;
  for (let step = 0; step < 6; step++) {
    const nb = pickBestNb(cx, cy, step === 0);
    if (nb[0] === cx && nb[1] === cy) break;
    cx = nb[0]; cy = nb[1];
    const px = cx * FP + FP / 2, py = cy * FP + FP / 2;
    if (step === 0 || linePassable(u.x, u.y, px, py)) {
      bestPt = [px, py];
    } else {
      break;
    }
    if (field[cy * W + cx] === 0) break;
  }
  return bestPt || exactGoal;
}

function steerTo(u, gx, gy, spec, alive, throttleMul, exactStop) {
  const dGoal = dist(u.x, u.y, gx, gy);
  if (exactStop) {
    const stopR = spec.air ? 1.0 * FP : 0.7 * FP;
    if (dGoal <= stopR) return { steer: 0, throttle: 0 };
  }

  let want0 = angleTo(u.x, u.y, gx, gy);

  if (!spec.air) {
    let rx = 0, ry = 0;
    for (let i = 0; i < alive.length; i++) {
      const f = alive[i];
      if (f.id === u.id || rules.units[f.kind].air) continue;
      const dx = u.x - f.x, dy = u.y - f.y;
      const d = Math.hypot(dx, dy);
      if (d > 0 && d < 2.2 * FP) {
        const w = (2.2 * FP - d) / (2.2 * FP);
        rx += (dx / d) * w;
        ry += (dy / d) * w;
      }
    }
    if (rx !== 0 || ry !== 0) {
      const rad0 = want0 * ANG_TO_RAD;
      want0 = Math.round(Math.atan2(Math.sin(rad0) + ry * 1.4, Math.cos(rad0) + rx * 1.4) / ANG_TO_RAD) & (FULL - 1);
    }
  }

  let want = want0;
  if (!spec.air) {
    const offsets = [0, 341, -341, 683, -683, 1024, -1024, 1365, -1365];
    for (let i = 0; i < offsets.length; i++) {
      const a = (want0 + offsets[i]) & (FULL - 1);
      const rad = a * ANG_TO_RAD;
      if (passable(u.x + Math.cos(rad) * FP * 1.35, u.y + Math.sin(rad) * FP * 1.35)) { want = a; break; }
    }
  }

  const d = angDiff(u.heading, want);
  const absD = Math.abs(d);
  let th = absD > 600 ? 0.0 : absD > 300 ? 0.25 : 1.0;

  if (exactStop) {
    const brakeR = spec.air ? 4.8 * FP : 2.5 * FP;
    if (dGoal < brakeR) {
      const ratio = Math.max(0, (dGoal - 0.6 * FP) / (brakeR - 0.6 * FP));
      if (ratio < th) th = ratio;
    }
  }

  return {
    steer: Math.max(-FP, Math.min(FP, Math.round((d / spec.turnRate) * FP))),
    throttle: Math.round(FP * th * (throttleMul ?? 1)),
  };
}

function getEnemyThreatRange(kind, ex, ey, ux, uy) {
  const sp = rules.units[kind];
  if (!sp || !sp.gun) return 0;
  let r = 0;
  if (sp.gun.mode === "direct") r = sp.gun.maxRange;
  else if (sp.secondary) r = sp.secondary.maxRange;
  const ha = rules.heightAdvantage;
  if (r > 0 && ha && heightAt(ex, ey) - heightAt(ux, uy) >= ha.minDelta) {
    r = Math.floor((r * ha.rangeBonus) / FP);
  }
  return r;
}

function droneSafeRadiusFor(c, tx, ty) {
  const tr = getEnemyThreatRange(c.kind, c.x, c.y, tx, ty);
  if (tr <= 0) return 0;
  const buf = (c.kind === "mbt" ? 3.6 : c.kind === "scout" ? 3.5 : c.kind === "apc" ? 3.0 : c.kind === "missile" ? 1.8 : 2.8) * FP;
  const ha = rules.heightAdvantage;
  const maxCap = (ha && heightAt(c.x, c.y) - heightAt(tx, ty) >= ha.minDelta) ? 36.0 * FP : 35.2 * FP;
  return Math.min(maxCap, tr + buf);
}

function areaForestOrFogAhead(x, y, gx, gy) {
  const dx = gx - x, dy = gy - y;
  const d = Math.hypot(dx, dy);
  if (d < 1) return false;
  const ux = dx / d, uy = dy / d;
  let f = 0, fg = 0;
  for (let step = 8; step <= 26; step += 4) {
    const tx = Math.floor((x + ux * step * FP) / FP);
    const ty = Math.floor((y + uy * step * FP) / FP);
    if (tx < 0 || ty < 0 || tx >= W || ty >= H) break;
    const idx = ty * W + tx;
    if (terrainArr[idx] === 1) f++;
    if (fogArr[idx]) fg++;
  }
  return f >= 2 || fg >= 1;
}

globalThis.controller = {
  draft(h) {
    const d = h.draft;
    if (!d) return undefined;
    const cost = DRAFT_PICK.reduce((c, k) => c + (d.costs[k] ?? 99), 0);
    return cost <= d.budget && DRAFT_PICK.every((k) => d.roster.includes(k)) ? DRAFT_PICK.slice() : undefined;
  },

  hello(h) {
    rules = h.rules;
    map = h.map;
    side = h.side;
    W = map.width;
    H = map.height;
    N = W * H;

    terrainSpeedArr = rules.terrainSpeed;
    terrainArr = Int32Array.from(map.terrain);
    heightsArr = Int32Array.from(map.heights);
    fogArr = map.fog && map.fog.length === N ? Uint8Array.from(map.fog) : new Uint8Array(N);
    passableGrid = new Uint8Array(N);
    for (let i = 0; i < N; i++) {
      passableGrid[i] = (terrainSpeedArr[terrainArr[i]] ?? 0) > 0 ? 1 : 0;
    }

    mySpawn = [map.spawns[side][0] * FP + FP / 2, map.spawns[side][1] * FP + FP / 2];
    enemySpawn = [map.spawns[1 - side][0] * FP + FP / 2, map.spawns[1 - side][1] * FP + FP / 2];
    mapCentre = [Math.floor(W / 2) * FP + FP / 2, Math.floor(H / 2) * FP + FP / 2];

    mem = {};
    lastScore = [0, 0];
    myRate = 0; enRate = 0;
    rateHistMy = []; rateHistEn = [];
    focusId = 0;
    blockedCnt = {};
    backoffState = {};
    forestGoal = {};
    objFields = [];
    committedStrikeIdx = -1;
    droneOrbitSign = {};
    droneFlipTick = {};
    comebackObj = {};
    mbtStallTicks = {};
    mbtAdvanceUntil = {};
    lastDamageTick = -999;
    prevUnitHp = {};
    blindHitTick = -999;
    blindHitPos = null;
    blindUnitTick = {};

    const myTile = nearestPassableTileCoords(map.spawns[side][0], map.spawns[side][1]);
    const enTile = nearestPassableTileCoords(map.spawns[1 - side][0], map.spawns[1 - side][1]);
    const myTileIdx = myTile[1] * W + myTile[0];
    const enTileIdx = enTile[1] * W + enTile[0];

    const objs = h.objectives && h.objectives.length
      ? h.objectives
      : [{ x: mapCentre[0], y: mapCentre[1], radius: rules.hill.radius, weight: 1 }];

    totalWeight = 0;
    for (let i = 0; i < objs.length; i++) {
      const o = objs[i];
      totalWeight += o.weight || 1;
      const seeds = [];
      const seedRad = Math.min(o.radius * 0.55, Math.max(1.5 * FP, o.radius - 1.8 * FP));
      const tx0 = Math.max(0, Math.floor((o.x - seedRad) / FP));
      const tx1 = Math.min(W - 1, Math.floor((o.x + seedRad) / FP));
      const ty0 = Math.max(0, Math.floor((o.y - seedRad) / FP));
      const ty1 = Math.min(H - 1, Math.floor((o.y + seedRad) / FP));
      for (let ty = ty0; ty <= ty1; ty++) {
        for (let tx = tx0; tx <= tx1; tx++) {
          if (!isTilePassable(tx, ty)) continue;
          if (dist(tx * FP + FP / 2, ty * FP + FP / 2, o.x, o.y) <= seedRad) seeds.push(ty * W + tx);
        }
      }
      if (!seeds.length) {
        const np = nearestPassableTileCoords(Math.floor(o.x / FP), Math.floor(o.y / FP));
        seeds.push(np[1] * W + np[0]);
      }
      const field = buildExactDijkstraField(seeds);
      const spots = computeObjectiveSpots(o);
      objFields.push({
        idx: i,
        x: o.x,
        y: o.y,
        radius: o.radius,
        weight: o.weight || 1,
        field,
        homeCost: field[myTileIdx],
        enemyCost: field[enTileIdx],
        isCentre: dist(o.x, o.y, mapCentre[0], mapCentre[1]) < 3 * FP,
        ...spots,
      });
    }

    centreIdx = objFields.length >= 3 ? objFields.findIndex((o) => o.isCentre) : -1;
    let minAdv = Infinity, maxAdv = -Infinity;
    homeIdx = 0; farIdx = objFields.length - 1;
    for (let i = 0; i < objFields.length; i++) {
      if (i === centreIdx) continue;
      const adv = (objFields[i].homeCost - objFields[i].enemyCost) * 1000 + objFields[i].homeCost;
      if (adv < minAdv) { minAdv = adv; homeIdx = i; }
      if (adv > maxAdv) { maxAdv = adv; farIdx = i; }
    }
    if (objFields.length >= 3 && centreIdx < 0) {
      for (let i = 0; i < objFields.length; i++) {
        if (i !== homeIdx && i !== farIdx) { centreIdx = i; break; }
      }
    }

    enemySpawnField = buildExactDijkstraField([enTileIdx]);
  },

  tick(o) {
    // --- 1. Score telemetry & urgency ---
    const dMy = o.score[side] - lastScore[side];
    const dEn = o.score[1 - side] - lastScore[1 - side];
    lastScore[side] = o.score[side];
    lastScore[1 - side] = o.score[1 - side];
    rateHistMy.push(dMy); if (rateHistMy.length > 6) rateHistMy.shift();
    rateHistEn.push(dEn); if (rateHistEn.length > 6) rateHistEn.shift();
    myRate = rateHistMy.reduce((a, b) => a + b, 0) / rateHistMy.length;
    enRate = rateHistEn.reduce((a, b) => a + b, 0) / rateHistEn.length;

    const lead = o.score[side] - o.score[1 - side];
    const ticksLeft = Math.max(0, rules.maxTicks - o.tick);
    const maxRemaining = ticksLeft * totalWeight;
    const projectedLead = lead + (myRate - enRate) * ticksLeft;
    const emergency = o.tick >= 400 && (
      (lead < 0 && -lead > maxRemaining * 0.35) ||
      (enRate > myRate + 0.5 && projectedLead < -250)
    );
    const behind = enRate > myRate + 0.1 || lead < -30 || projectedLead < 80;

    // --- 2. Update contact memory & purge cleared ghosts ---
    const alive = [], mbts = [], drones = [], scouts = [], apcs = [];
    for (let i = 0; i < o.units.length; i++) {
      const u = o.units[i];
      if (!u.alive) continue;
      alive.push(u);
      if (u.kind === "mbt") mbts.push(u);
      else if (u.kind === "drone") drones.push(u);
      else if (u.kind === "scout") scouts.push(u);
      else if (u.kind === "apc") apcs.push(u);
      if (u.kind === "mbt" && prevUnitHp[u.id] !== undefined && u.hp < prevUnitHp[u.id] &&
          !o.contacts.some((c) => c.kind !== "drone" && dist(u.x, u.y, c.x, c.y) <= 34 * FP)) {
        blindHitTick = o.tick;
        blindHitPos = [u.x, u.y];
        blindUnitTick[u.id] = o.tick;
      }
      prevUnitHp[u.id] = u.hp;
      blockedCnt[u.id] = u.blocked ? (blockedCnt[u.id] || 0) + 2 : Math.max(0, (blockedCnt[u.id] || 0) - 1);
    }

    for (let i = 0; i < o.contacts.length; i++) {
      const c = o.contacts[i];
      if (mem[c.id] && c.hpFrac < mem[c.id].hpFrac) lastDamageTick = o.tick;
      mem[c.id] = {
        id: c.id, kind: c.kind, x: c.x, y: c.y,
        heading: c.heading, speed: c.speed, hpFrac: c.hpFrac,
        tick: o.tick, seenBy: c.seenBy,
      };
    }
    let enemyHasMissile = false;
    let enemyHasSpotter = false;
    for (const idStr in mem) {
      const m = mem[idStr];
      if (o.tick - m.tick > 450) { delete mem[idStr]; continue; }
      if (m.kind === "missile") enemyHasMissile = true;
      if ((m.kind === "drone" || m.kind === "scout") && o.tick - m.tick <= 320) enemyHasSpotter = true;
      if (m.tick < o.tick) {
        for (let i = 0; i < alive.length; i++) {
          const u = alive[i];
          const sp = rules.units[u.kind];
          if (dist(u.x, u.y, m.x, m.y) <= sp.sensorRange * 0.65 && hasClearShot(u.x, u.y, sp.eyeHeight, m.x, m.y)) {
            delete mem[idStr];
            break;
          }
        }
      }
    }

    // --- 3. Analyze objective states, safety for drones & local combat power ---
    const objs = o.objectives && o.objectives.length
      ? o.objectives
      : [{ x: mapCentre[0], y: mapCentre[1], radius: rules.hill.radius, weight: 1, owner: o.hillOwner, state: "empty" }];

    const objStatus = [];
    let enemyOwnedWeight = 0;
    for (let i = 0; i < objFields.length; i++) {
      const of = objFields[i];
      const cur = objs[i] || objs[0];
      if (cur.owner === 1 - side && cur.state === "held") enemyOwnedWeight += of.weight;
      let enemyInside = 0, enemyNear = 0, armedNear = 0, allyInside = 0, enemyPower = 0;
      let hasApcInside = false, hasHeavyNear = false, safeForDrone = true;
      const sx = of.anchorSpot[0], sy = of.anchorSpot[1];

      for (let j = 0; j < o.contacts.length; j++) {
        const c = o.contacts[j];
        const d = dist(c.x, c.y, of.x, of.y);
        if (d <= of.radius) {
          enemyInside++;
          if (c.kind === "apc") hasApcInside = true;
        }
        if (d <= of.radius + 14 * FP) {
          enemyNear++;
          if (c.kind !== "drone") armedNear++;
          if (c.kind === "mbt" || c.kind === "missile") { hasHeavyNear = true; enemyPower += 2; }
          else if (c.kind === "apc") { hasHeavyNear = true; enemyPower += 1; }
          else if (c.kind === "scout") enemyPower += 0.5;
        }
        const sr = droneSafeRadiusFor(c, sx, sy);
        if (sr > 0 && dist(c.x, c.y, sx, sy) < sr + 1.5 * FP) safeForDrone = false;
      }
      for (const idStr in mem) {
        const m = mem[idStr];
        if (m.tick === o.tick || o.tick - m.tick > 180) continue;
        const d = dist(m.x, m.y, of.x, of.y);
        if (d <= of.radius) enemyInside++;
        if (d <= of.radius + 12 * FP) {
          if (m.kind !== "drone") armedNear++;
          if (m.kind === "mbt" || m.kind === "missile") { hasHeavyNear = true; enemyPower += 1.5; }
          else if (m.kind === "apc") { hasHeavyNear = true; enemyPower += 0.8; }
        }
        if (o.tick - m.tick <= 150) {
          const sr = droneSafeRadiusFor(m, sx, sy);
          if (sr > 0 && dist(m.x, m.y, sx, sy) < sr + 1.5 * FP) safeForDrone = false;
        }
      }
      for (let j = 0; j < alive.length; j++) {
        if (dist(alive[j].x, alive[j].y, of.x, of.y) <= of.radius) allyInside++;
      }
      objStatus.push({
        idx: i, x: of.x, y: of.y, radius: of.radius, weight: of.weight, field: of.field,
        homeCost: of.homeCost, enemyCost: of.enemyCost,
        combatSpot: of.combatSpot, anchorSpot: of.anchorSpot, flankSpot: of.flankSpot,
        owner: cur.owner, state: cur.state,
        enemyInside, enemyNear, armedNear, allyInside, enemyPower, hasApcInside, hasHeavyNear, safeForDrone,
      });
    }
    const enemyHasApcCap = o.tick >= 120 && enRate > enemyOwnedWeight + 0.4;

    // --- 4. Shared Focus Fire (1-shot drone > APC on hill > low-HP > missile/spotter) ---
    let focus = null;
    if (o.contacts.length) {
      let bestFocusScore = -1e9;
      for (let i = 0; i < o.contacts.length; i++) {
        const c = o.contacts[i];
        const tRad = rules.units[c.kind]?.radius;
        let clearMbtCount = 0, minMbtDist = Infinity;
        for (let j = 0; j < mbts.length; j++) {
          const m = mbts[j];
          const dm = dist(m.x, m.y, c.x, c.y);
          if (dm < minMbtDist) minMbtDist = dm;
          const effR = effectiveMaxRange(m, rules.units.mbt, c.x, c.y);
          if (dm <= effR && exactShellClears(m.x, m.y, rules.units.mbt, c.x, c.y, tRad)) clearMbtCount++;
        }
        const clearByMbt = clearMbtCount >= 1;
        let sc = (1 - c.hpFrac / FP) * 90;
        if (clearByMbt) sc += 100;
        if (clearMbtCount >= 2) sc += 35;
        const uMaxHp = rules.units[c.kind]?.hp || 100;
        if (clearByMbt && (c.hpFrac / FP) * uMaxHp <= 45 * Math.min(2, clearMbtCount) + 5) sc += 50;
        if (c.kind === "drone" && clearByMbt) sc += 100;
        if (c.kind === "scout" && clearByMbt) sc += enemyHasMissile ? 52 : (clearMbtCount >= 2 ? 48 : 35);
        if (c.kind === "missile") sc += clearByMbt ? 65 : 45;
        else if (c.kind === "artillery") sc += 45;
        if (c.kind === "apc") {
          const onObj = objStatus.some((ob) => dist(c.x, c.y, ob.x, ob.y) <= ob.radius + 3 * FP);
          sc += (onObj && clearByMbt) ? 110 : onObj ? 70 : 25;
        }
        for (let k = 0; k < objStatus.length; k++) {
          if (dist(c.x, c.y, objStatus[k].x, objStatus[k].y) <= objStatus[k].radius) {
            sc += 25 * objStatus[k].weight;
            break;
          }
        }
        if (c.id === focusId) sc += 14;
        if (minMbtDist < Infinity) sc -= (minMbtDist / FP) * 0.6;
        if (sc > bestFocusScore) { bestFocusScore = sc; focus = c; }
      }
      if (focus) focusId = focus.id;
    }

    // --- 5. Team Role & Anti-Whiplash Objective Coordinator ---
    let mbtCx = mySpawn[0], mbtCy = mySpawn[1];
    if (mbts.length) {
      let sx = 0, sy = 0;
      for (let i = 0; i < mbts.length; i++) { sx += mbts[i].x; sy += mbts[i].y; }
      mbtCx = sx / mbts.length; mbtCy = sy / mbts.length;
    }

    const homeOb = objStatus[homeIdx];
    const farOb = objStatus[farIdx];
    const homeThreatened =
      homeOb.owner === 1 - side ||
      homeOb.state === "contested" ||
      homeOb.armedNear > 0;

    // Anti-Whiplash: only divert MBTs back home if far is already ours, OR home is significantly closer
    // (don't abort a siege within 40 tiles of enemy-held farIdx to chase one raider across the map!)
    const mbtDistHome = dist(mbtCx, mbtCy, homeOb.x, homeOb.y);
    const mbtDistFar = dist(mbtCx, mbtCy, farOb.x, farOb.y);
    const shouldDefendHome =
      (homeThreatened || (!drones.length && !scouts.length && !apcs.length && homeOb.owner !== side)) && (
        farOb.owner === side ||
        homeOb.weight > farOb.weight ||
        (mbtDistHome <= mbtDistFar + 8 * FP && mbtDistFar >= 34 * FP && farOb.owner !== 1 - side) ||
        (mbtDistHome <= 28 * FP && homeOb.armedNear > 0 && farOb.owner !== 1 - side)
      );

    const soloHeld = alive.length === 1 && mbts.length === 1 && enRate <= myRate + 0.1 && lead >= 0
      ? objStatus.find((ob) => ob.owner === side && dist(mbts[0].x, mbts[0].y, ob.x, ob.y) <= ob.radius + 4 * FP)
      : null;
    let strikeIdx = farIdx;
    if (soloHeld) {
      strikeIdx = soloHeld.idx;
    } else if (shouldDefendHome && (homeOb.armedNear > 0 || homeOb.owner === 1 - side || (!drones.length && !scouts.length && !apcs.length) || (!enemyHasApcCap && enRate <= myRate))) {
      strikeIdx = homeIdx;
    } else {
      const pushUrgent = enemyHasApcCap && enRate > myRate + 0.3;
      let bestScore = -1e9;
      for (let i = 0; i < objStatus.length; i++) {
        const ob = objStatus[i];
        if (i === homeIdx && !shouldDefendHome && (drones.length || scouts.length || apcs.length)) continue;
        if (ob.owner === side && ob.state === "held" && ob.enemyNear === 0) continue;
        let s = ob.weight * 40;
        if (ob.owner === 1 - side) {
          const inferredApc = enemyHasApcCap && !ob.hasApcInside && i === farIdx && enRate > myRate + 0.5 && ob.enemyPower <= 2;
          s += 65 + (ob.hasApcInside ? 40 : inferredApc ? 40 : 0);
          if (pushUrgent && ob.weight >= 2) s += 35;
        } else if (ob.state === "contested") s += 55;
        else if (ob.owner === null) s += 28;
        if (ob.enemyPower > 0) s -= ob.enemyPower * (pushUrgent ? 6 : 12);
        if (i === centreIdx && ob.weight === 1 && farOb.weight >= 2 && farOb.owner === 1 - side && enRate > myRate) {
          s -= 28;
        }
        // Strike hysteresis: keep MBTs committed when within 38 tiles of an active siege
        if (i === committedStrikeIdx && (ob.owner !== side || ob.state === "contested" || ob.enemyNear > 0) &&
            mbts.length && dist(mbtCx, mbtCy, ob.x, ob.y) < 38 * FP) {
          s += 45;
        }
        if (mbts.length) {
          let sumD = 0;
          for (let j = 0; j < mbts.length; j++) sumD += dist(mbts[j].x, mbts[j].y, ob.x, ob.y);
          s -= (sumD / mbts.length / FP) * 0.45;
        }
        if (s > bestScore) { bestScore = s; strikeIdx = i; }
      }
      if (bestScore === -1e9) {
        strikeIdx = centreIdx >= 0 ? centreIdx : farIdx;
      }
    }
    committedStrikeIdx = strikeIdx;

    // Assign Anchor + Flex (with Dynamic Drone Reassignment & Endgame Comeback)
    const unitRoles = {};
    let anchorUnit = null;
    if (apcs.length) {
      anchorUnit = apcs[0];
    } else if (mbts.length === 0 && drones.length > 0) {
      // Zero-MBT Endgame Comeback: sticky hold-discipline across highest-weight SAFE objectives
      const ranked = objStatus.slice().sort((a, b) => {
        if (a.safeForDrone !== b.safeForDrone) return a.safeForDrone ? -1 : 1;
        if (a.weight !== b.weight) return b.weight - a.weight;
        const aHeld = a.owner === side ? 1 : 0;
        const bHeld = b.owner === side ? 1 : 0;
        if (aHeld !== bHeld) return bHeld - aHeld;
        return a.homeCost - b.homeCost;
      });
      const used = new Set();
      for (let i = 0; i < drones.length; i++) {
        const d = drones[i];
        let pick = null;
        const prevIdx = comebackObj[d.id];
        if (prevIdx !== undefined && !used.has(prevIdx)) {
          const prevOb = objStatus[prevIdx];
          if (prevOb && prevOb.safeForDrone) {
            const better = ranked.find((ob) => !used.has(ob.idx) && ob.safeForDrone && ob.weight > prevOb.weight && ob.owner !== side);
            if (!better) pick = prevOb;
          }
        }
        if (!pick) pick = ranked.find((ob) => !used.has(ob.idx)) || ranked[0];
        used.add(pick.idx);
        comebackObj[d.id] = pick.idx;
        unitRoles[d.id] = { role: "comeback", objIdx: pick.idx, spot: pick.anchorSpot };
      }
    } else {
      const woundedMbt = mbts.find((m) => m.hp < 70);
      const healthyMbt = mbts.find((m) => m.hp >= 100);
      if (drones.length) {
        let bestD = Infinity;
        for (const d of drones) {
          const dd = dist(d.x, d.y, homeOb.x, homeOb.y);
          if (dd < bestD) { bestD = dd; anchorUnit = d; }
        }
      } else if (scouts.length) {
        let bestD = Infinity;
        for (const s of scouts) {
          const dd = dist(s.x, s.y, homeOb.x, homeOb.y);
          if (dd < bestD) { bestD = dd; anchorUnit = s; }
        }
      } else if (woundedMbt && healthyMbt && mbts.length >= 2) {
        anchorUnit = woundedMbt;
      } else if (mbts.length >= 2 && !behind && lead >= 0) {
        anchorUnit = mbts[0].hp <= mbts[1].hp ? mbts[0] : mbts[1];
      }
    }

    let anchorIdx = homeIdx;
    const blindAmbushActive = blindHitPos && o.tick - blindHitTick <= 180 && mbts.length > 0 &&
      !o.contacts.some((c) => c.kind !== "drone" && dist(blindHitPos[0], blindHitPos[1], c.x, c.y) <= 33 * FP);
    if (anchorUnit) {
      let anchorRecon = null;
      // Dynamic Anchor Reassignment: stay if already holding a safe hill; else counter-spot blind ambush or take safe hill
      if (anchorUnit.kind === "drone" && !homeOb.safeForDrone && objStatus.length >= 2) {
        const holdingAlt = objStatus.find((ob) => ob.idx !== homeIdx && ob.safeForDrone && dist(anchorUnit.x, anchorUnit.y, ob.x, ob.y) <= ob.radius + 4 * FP);
        if (holdingAlt) {
          anchorIdx = holdingAlt.idx;
        } else if (blindAmbushActive) {
          anchorIdx = strikeIdx;
          const angB = Math.atan2(mySpawn[1] - blindHitPos[1], mySpawn[0] - blindHitPos[0]);
          anchorRecon = clampCoord(blindHitPos[0] + Math.cos(angB) * 7 * FP, blindHitPos[1] + Math.sin(angB) * 7 * FP);
        } else {
          const altSafe = objStatus
            .filter((ob) => ob.idx !== homeIdx && ob.safeForDrone)
            .sort((a, b) => (b.weight - a.weight) || ((a.owner === side ? 1 : 0) - (b.owner === side ? 1 : 0)))[0];
          if (altSafe) anchorIdx = altSafe.idx;
        }
      }
      unitRoles[anchorUnit.id] = {
        role: "anchor",
        objIdx: anchorIdx,
        spot: anchorRecon || (anchorUnit.kind === "mbt" ? objStatus[anchorIdx].combatSpot : objStatus[anchorIdx].anchorSpot),
        reconTarget: anchorRecon,
      };
    }

    const flexUnits = [];
    for (let i = 0; i < alive.length; i++) {
      const u = alive[i];
      if (unitRoles[u.id]) continue;
      if (u.kind === "drone" || u.kind === "scout" || u.kind === "apc") {
        flexUnits.push(u);
      }
    }

    let flexObjIdx = farIdx;
    if (objStatus.length >= 3) {
      const midOb = objStatus[centreIdx];
      if (midOb.owner !== side && !midOb.hasHeavyNear && midOb.safeForDrone && anchorIdx !== centreIdx) flexObjIdx = centreIdx;
      else if (farOb.owner === 1 - side && !farOb.hasHeavyNear && farOb.safeForDrone && anchorIdx !== farIdx) flexObjIdx = farIdx;
      else if (farOb.weight >= 2 && farOb.owner === 1 - side && anchorIdx !== farIdx) flexObjIdx = farIdx;
      else if (midOb.owner !== side && anchorIdx !== centreIdx) flexObjIdx = centreIdx;
      else flexObjIdx = anchorIdx === farIdx ? centreIdx : farIdx;
    }
    const strikeOb = objStatus[strikeIdx];
    const mbtNearStrike = mbts.length > 0 && dist(mbtCx, mbtCy, strikeOb.x, strikeOb.y) < 48 * FP;
    const strikeUnseenEnemy = strikeOb.owner === 1 - side && strikeOb.enemyInside === 0 && strikeOb.armedNear === 0;

    for (let i = 0; i < flexUnits.length; i++) {
      const fu = flexUnits[i];
      let idx = i === 0 ? flexObjIdx : (objStatus.length >= 3 ? (flexObjIdx === centreIdx ? farIdx : centreIdx) : farIdx);
      let spotForFlex = objStatus[idx].anchorSpot;
      let reconTarget = null;

      // Stay on a safe objective already held by this flex drone instead of abandoning it when owner flips to side
      const curHeld = objStatus.find((ob) => ob.idx !== homeIdx && ob.idx !== anchorIdx && ob.safeForDrone && dist(fu.x, fu.y, ob.x, ob.y) <= ob.radius + 3 * FP);
      if (fu.kind === "drone" && curHeld) {
        idx = curHeld.idx;
        spotForFlex = curHeld.anchorSpot;
      } else if (fu.kind === "drone" && i === 0 && blindAmbushActive) {
        idx = strikeIdx;
        const angB = Math.atan2(mySpawn[1] - blindHitPos[1], mySpawn[0] - blindHitPos[0]);
        spotForFlex = clampCoord(blindHitPos[0] + Math.cos(angB) * 7 * FP, blindHitPos[1] + Math.sin(angB) * 7 * FP);
        reconTarget = spotForFlex;
      } else {
        const holdingSafeNow = objStatus[idx].safeForDrone && dist(fu.x, fu.y, objStatus[idx].x, objStatus[idx].y) <= objStatus[idx].radius + 3 * FP;
        if (fu.kind === "drone" && i === 0 && mbtNearStrike && strikeUnseenEnemy && !holdingSafeNow) {
          idx = strikeIdx;
          const ang = Math.atan2(mbtCy - strikeOb.y, mbtCx - strikeOb.x);
          spotForFlex = clampCoord(strikeOb.x + Math.cos(ang) * 32.5 * FP, strikeOb.y + Math.sin(ang) * 32.5 * FP);
          reconTarget = spotForFlex;
        } else if (fu.kind === "drone" && !objStatus[idx].safeForDrone) {
          const altSafe = objStatus
            .filter((ob) => ob.idx !== idx && ob.idx !== homeIdx && ob.idx !== anchorIdx && ob.safeForDrone &&
              (ob.owner !== side || dist(fu.x, fu.y, ob.x, ob.y) <= ob.radius + 4 * FP))
            .sort((a, b) => b.weight - a.weight)[0];
          if (altSafe) {
            idx = altSafe.idx;
            spotForFlex = altSafe.anchorSpot;
          } else if (mbtNearStrike) {
            idx = strikeIdx;
            const ang = Math.atan2(mbtCy - strikeOb.y, mbtCx - strikeOb.x);
            spotForFlex = clampCoord(strikeOb.x + Math.cos(ang) * 32.5 * FP, strikeOb.y + Math.sin(ang) * 32.5 * FP);
            reconTarget = spotForFlex;
          }
        }
      }

      unitRoles[fu.id] = { role: "flex", objIdx: idx, spot: spotForFlex, reconTarget };
    }

    let strikeSlot = 0;
    for (let i = 0; i < alive.length; i++) {
      const u = alive[i];
      if (unitRoles[u.id]) continue;
      if (u.kind === "artillery") {
        unitRoles[u.id] = { role: "arty", objIdx: strikeIdx, spot: strikeOb.combatSpot };
      } else {
        const sp = strikeSlot === 0 ? strikeOb.combatSpot : strikeOb.flankSpot;
        strikeSlot++;
        unitRoles[u.id] = { role: "strike", objIdx: strikeIdx, spot: sp };
      }
    }

    // --- 6. Generate orders per unit ---
    const orders = [];
    for (let i = 0; i < o.units.length; i++) {
      const u = o.units[i];
      if (!u.alive) continue;
      const spec = rules.units[u.kind];
      const order = { id: u.id };
      const roleInfo = unitRoles[u.id] || { role: "strike", objIdx: homeIdx, spot: homeOb.combatSpot };
      const myObj = objStatus[roleInfo.objIdx];

      let nearest = null, bestD = Infinity;
      for (let j = 0; j < o.contacts.length; j++) {
        const c = o.contacts[j];
        const d = dist(u.x, u.y, c.x, c.y);
        if (d < bestD) { bestD = d; nearest = c; }
      }
      let memTarget = null, memBestD = Infinity;
      if (!nearest) {
        for (const idStr in mem) {
          const m = mem[idStr];
          const d = dist(u.x, u.y, m.x, m.y);
          if (d < memBestD) { memBestD = d; memTarget = m; }
        }
      }

      let shoot = null, shootDist = Infinity;
      if (focus && u.kind !== "drone") {
        const fd = dist(u.x, u.y, focus.x, focus.y);
        const fEffR = effectiveMaxRange(u, spec, focus.x, focus.y);
        const fRad = rules.units[focus.kind]?.radius;
        if (u.kind === "scout") {
          const soft = focus.kind === "scout" || focus.kind === "drone" || focus.hpFrac < 0.4 * FP;
          if (soft && fd <= fEffR * 1.15) { shoot = focus; shootDist = fd; }
          else if (nearest) { shoot = nearest; shootDist = bestD; }
        } else if (fd <= fEffR && exactShellClears(u.x, u.y, spec, focus.x, focus.y, fRad)) {
          shoot = focus; shootDist = fd;
        } else {
          // Focus is out of range or terrain-blocked for this unit: switch to best clear reachable target
          let alt = null, altSc = -1e9, altD = Infinity;
          for (let j = 0; j < o.contacts.length; j++) {
            const c = o.contacts[j];
            const cd = dist(u.x, u.y, c.x, c.y);
            if (cd > effectiveMaxRange(u, spec, c.x, c.y)) continue;
            if (!exactShellClears(u.x, u.y, spec, c.x, c.y, rules.units[c.kind]?.radius)) continue;
            let sc = (1 - c.hpFrac / FP) * 70 - (cd / FP) * 0.6;
            if (c.kind === "drone") sc += 90;
            else if (c.kind === "apc") {
              const onObj = objStatus.some((ob) => dist(c.x, c.y, ob.x, ob.y) <= ob.radius + 3 * FP);
              sc += onObj ? 70 : 25;
            } else if (c.kind === "missile") sc += 50;
            if (sc > altSc) { altSc = sc; alt = c; altD = cd; }
          }
          if (alt) { shoot = alt; shootDist = altD; }
          else if (fd <= fEffR) { shoot = focus; shootDist = fd; }
          else if (nearest) { shoot = nearest; shootDist = bestD; }
        }
      } else if (nearest && u.kind !== "drone") {
        shoot = nearest; shootDist = bestD;
      }
      const aimTgt = shoot || nearest || memTarget;

      let ax = 0, ay = 0;
      if (aimTgt && spec.gun.mode !== "none") {
        const dAim = dist(u.x, u.y, aimTgt.x, aimTgt.y);
        const leadT = spec.gun.shellSpeed ? Math.min(50, Math.max(0, dAim / spec.gun.shellSpeed)) : 0;
        const p = (shoot || nearest) ? predict(aimTgt, leadT) : [aimTgt.x, aimTgt.y];
        ax = p[0]; ay = p[1];
      }

      // A. Artillery dodge
      let dodgeGoal = null;
      for (let j = 0; j < (o.incoming || []).length; j++) {
        const inc = o.incoming[j];
        if (inc.ticks <= 55 && dist(u.x, u.y, inc.x, inc.y) < 4.2 * FP) {
          const ang = Math.atan2(u.y - inc.y, u.x - inc.x);
          dodgeGoal = clampCoord(u.x + Math.cos(ang) * 6 * FP, u.y + Math.sin(ang) * 6 * FP);
          break;
        }
      }

      if (dodgeGoal && o.canMove) {
        const mv = steerTo(u, dodgeGoal[0], dodgeGoal[1], spec, alive, 1, false);
        order.steer = mv.steer; order.throttle = mv.throttle;
      } else if (u.kind === "drone") {
        // B. WALL-SAFE DRONE EVASION, STANDOFF SPOTTING & CAPPING
        if (o.canMove) {
          let repX = 0, repY = 0, threatCount = 0, closestThreat = null, closestThreatRatio = 0;
          const considerThreat = (c) => {
            const safeR = droneSafeRadiusFor(c, u.x, u.y);
            if (safeR <= 0) return;
            const d = dist(u.x, u.y, c.x, c.y);
            if (d < safeR) {
              threatCount++;
              const ratio = safeR / Math.max(1, d);
              repX += ((u.x - c.x) / Math.max(1, d)) * ratio;
              repY += ((u.y - c.y) / Math.max(1, d)) * ratio;
              if (ratio > closestThreatRatio) { closestThreatRatio = ratio; closestThreat = { c, safeR, d }; }
            }
          };

          for (let j = 0; j < o.contacts.length; j++) considerThreat(o.contacts[j]);
          for (const idStr in mem) {
            const m = mem[idStr];
            if (m.tick !== o.tick && o.tick - m.tick <= 140) considerThreat(m);
          }

          if (threatCount > 0 && closestThreat) {
            const wallPad = 14 * FP;
            if (u.x < wallPad) repX += ((wallPad - u.x) / wallPad) * 1.1;
            else if (u.x > W * FP - wallPad) repX -= ((u.x - (W * FP - wallPad)) / wallPad) * 1.1;
            if (u.y < wallPad) repY += ((wallPad - u.y) / wallPad) * 1.1;
            else if (u.y > H * FP - wallPad) repY -= ((u.y - (H * FP - wallPad)) / wallPad) * 1.1;

            const awayAng = Math.atan2(repY, repX);
            const orbitBlend = closestThreat.d > closestThreat.safeR * 0.87 ? 0.95 : 0.25;

            if (!droneOrbitSign[u.id]) droneOrbitSign[u.id] = (u.id & 1) ? 1 : -1;
            const curSign = droneOrbitSign[u.id];
            const marginAt = (px, py) => Math.min(px, W * FP - px, py, H * FP - py) / FP;
            const curX = u.x + Math.cos(awayAng + curSign * orbitBlend) * 9 * FP;
            const curY = u.y + Math.sin(awayAng + curSign * orbitBlend) * 9 * FP;
            const oppX = u.x + Math.cos(awayAng - curSign * orbitBlend) * 9 * FP;
            const oppY = u.y + Math.sin(awayAng - curSign * orbitBlend) * 9 * FP;
            const curMargin = marginAt(curX, curY);
            const oppMargin = marginAt(oppX, oppY);
            if (curMargin < 12 && oppMargin > curMargin + 4 && o.tick - (droneFlipTick[u.id] || -999) >= 40) {
              droneOrbitSign[u.id] = -curSign;
              droneFlipTick[u.id] = o.tick;
            }
            const escAng = awayAng + droneOrbitSign[u.id] * orbitBlend;
            const escA = Math.round(escAng / ANG_TO_RAD) & (FULL - 1);
            const diffEsc = Math.abs(angDiff(u.heading, escA));
            const useReverse = u.speed < -2000 ? diffEsc > 850 : (u.speed > 2000 ? diffEsc > 1200 : diffEsc > 1024);

            if (useReverse) {
              const escTailA = (escA + 2048) & (FULL - 1);
              const dTail = angDiff(u.heading, escTailA);
              order.steer = Math.max(-FP, Math.min(FP, Math.round((dTail / spec.turnRate) * FP)));
              order.throttle = -FP;
            } else {
              const dEsc = angDiff(u.heading, escA);
              order.steer = Math.max(-FP, Math.min(FP, Math.round((dEsc / spec.turnRate) * FP)));
              order.throttle = FP;
            }
          } else {
            let dGoal = roleInfo.spot;
            let exactStop = !roleInfo.reconTarget;
            let thMul = 1.0;

            if (roleInfo.role === "flex") {
              if (roleInfo.reconTarget) {
                dGoal = roleInfo.reconTarget;
                exactStop = false;
              } else if (nearest && nearest.kind !== "drone" && bestD < 34 * FP && (myObj.owner === side || myObj.hasHeavyNear)) {
                const ang = Math.atan2(u.y - nearest.y, u.x - nearest.x);
                dGoal = clampCoord(nearest.x + Math.cos(ang) * 32.8 * FP, nearest.y + Math.sin(ang) * 32.8 * FP);
                exactStop = false;
              } else if (mbts.length && o.contacts.length === 0 &&
                (dist(u.x, u.y, enemySpawn[0], enemySpawn[1]) < 56 * FP ||
                 (o.tick < 260 && dist(u.x, u.y, enemySpawn[0], enemySpawn[1]) < 64 * FP) ||
                 (o.tick < 340 && dist(u.x, u.y, mbtCx, mbtCy) > 24 * FP && dGoal && areaForestOrFogAhead(u.x, u.y, dGoal[0], dGoal[1])))) {
              const dEnSpawn = dist(u.x, u.y, enemySpawn[0], enemySpawn[1]);
              if ((dEnSpawn < 48 * FP || dist(u.x, u.y, mbtCx, mbtCy) > 20 * FP) && dist(u.x, u.y, myObj.x, myObj.y) > myObj.radius + 6 * FP) {
                const ang = Math.atan2(strikeOb.y - mbtCy, strikeOb.x - mbtCx);
                dGoal = clampCoord(mbtCx + Math.cos(ang) * 16 * FP, mbtCy + Math.sin(ang) * 16 * FP);
              }
            }
            if (dGoal && o.contacts.length === 0 && areaForestOrFogAhead(u.x, u.y, dGoal[0], dGoal[1])) {
              thMul = 0.6;
            }
          } else if (roleInfo.role === "anchor") {
            if (roleInfo.reconTarget) { dGoal = roleInfo.reconTarget; exactStop = false; }
            else if (o.contacts.length === 0 && myObj.homeCost > myObj.enemyCost * 0.96 && dGoal && areaForestOrFogAhead(u.x, u.y, dGoal[0], dGoal[1])) {
              thMul = 0.72;
            }
          }

            if (dGoal) {
              const mv = steerTo(u, dGoal[0], dGoal[1], spec, alive, thMul, exactStop);
              order.steer = mv.steer; order.throttle = mv.throttle;
            }
          }
        }
        orders.push(order);
        continue;
      } else {
        // C. GROUND UNITS
        let retreating = false;

        if (u.kind === "scout" && u.hp < 40 && nearest && bestD < 14 * FP &&
            (nearest.kind === "mbt" || nearest.kind === "missile" || nearest.kind === "artillery")) {
          const backPt = mbts.length ? [mbts[0].x, mbts[0].y] : mySpawn;
          if (o.canMove) {
            const mv = steerTo(u, backPt[0], backPt[1], spec, alive, 1, false);
            order.steer = mv.steer; order.throttle = mv.throttle;
          }
          retreating = true;
        }

        // Compute threatInFire + healthy wingman status to avoid hp<55 paralysis behind cover
        let threatInFire = false;
        let healthyWingNearby = false;
        let spottedByEnemy = false;
        if (u.kind === "mbt") {
          for (let j = 0; j < o.contacts.length; j++) {
            const c = o.contacts[j];
            const dc = dist(u.x, u.y, c.x, c.y);
            if ((c.kind === "drone" && dc < 36.5 * FP) || (c.kind === "scout" && dc < 19 * FP) || (c.kind !== "drone" && dc < 21 * FP)) {
              spottedByEnemy = true;
            }
            if (c.kind === "drone") continue;
            const tr = getEnemyThreatRange(c.kind, c.x, c.y, u.x, u.y);
            if (tr > 0 && dc <= tr + 2.5 * FP &&
                exactShellClears(c.x, c.y, rules.units[c.kind], u.x, u.y, spec.radius)) {
              threatInFire = true;
            }
          }
          for (let j = 0; j < mbts.length; j++) {
            const m = mbts[j];
            if (m.id !== u.id && m.hp >= 100 && dist(u.x, u.y, m.x, m.y) <= 18 * FP) {
              healthyWingNearby = true;
              break;
            }
          }
        }

        const distToObj = dist(u.x, u.y, myObj.x, myObj.y);
        const insideObj = distToObj <= myObj.radius - 0.8 * FP;
        const desperateClock = ticksLeft < 420 && lead <= 0 && myObj.owner === 1 - side && distToObj < 16 * FP;

        // Narrow MBT reverse retreat (ONLY when threatInFire is real; never freeze behind trees)
        if (!retreating && u.kind === "mbt" && nearest && threatInFire) {
          let foesNear = 0, friendsNear = 0;
          for (let j = 0; j < o.contacts.length; j++) {
            const c = o.contacts[j];
            if (c.kind !== "drone" && dist(u.x, u.y, c.x, c.y) <= 30 * FP) foesNear++;
          }
          for (let j = 0; j < alive.length; j++) {
            const f = alive[j];
            if (f.id !== u.id && f.kind !== "drone" && dist(u.x, u.y, f.x, f.y) <= 30 * FP) friendsNear++;
          }
          const anyHealthyMbt = mbts.some((m) => m.hp >= 55);
          const hpThresh = healthyWingNearby ? 65 : 55;
          const critical = u.hp < hpThresh && !(emergency && insideObj && u.hp >= 20) &&
            (healthyWingNearby || anyHealthyMbt || bestD < 22 * FP || (!behind && !emergency));
          const outnumbered = u.hp < 85 && foesNear >= friendsNear + 2 && !(emergency && insideObj);
          if ((critical || outnumbered) && o.canMove) {
            const angBack = Math.atan2(u.y - nearest.y, u.x - nearest.x);
            if (passable(u.x + Math.cos(angBack) * 1.4 * FP, u.y + Math.sin(angBack) * 1.4 * FP)) {
              const want = angleTo(u.x, u.y, nearest.x, nearest.y);
              const d = angDiff(u.heading, want);
              order.steer = Math.max(-FP, Math.min(FP, Math.round((d / spec.turnRate) * FP)));
              order.throttle = -FP;
              retreating = true;
            }
          }
        }

        const effR = shoot ? effectiveMaxRange(u, spec, shoot.x, shoot.y) : spec.gun.maxRange;
        const shootRad = shoot ? rules.units[shoot.kind]?.radius : undefined;
        const canShootTarget = !!shoot && shootDist <= effR && exactShellClears(u.x, u.y, spec, shoot.x, shoot.y, shootRad);
        const stalled = o.tick < (mbtAdvanceUntil[u.id] || 0);

        // Anti-APC spacing: ONLY step back from an unguarded APC inside 15 tiles when not pressing onto hill
        if (!retreating && u.kind === "mbt" && !insideObj && !desperateClock && canShootTarget &&
            nearest && nearest.kind === "apc" && bestD < 15 * FP && bestD > 5 * FP &&
            distToObj > myObj.radius + 4 * FP && o.canMove &&
            !o.contacts.some((c) => c.kind === "mbt" && dist(u.x, u.y, c.x, c.y) < 22 * FP)) {
          const angBack = Math.atan2(u.y - nearest.y, u.x - nearest.x);
          if (passable(u.x + Math.cos(angBack) * 1.4 * FP, u.y + Math.sin(angBack) * 1.4 * FP)) {
            const want = angleTo(u.x, u.y, nearest.x, nearest.y);
            const d = angDiff(u.heading, want);
            order.steer = Math.max(-FP, Math.min(FP, Math.round((d / spec.turnRate) * FP)));
            order.throttle = -FP;
            retreating = true;
          }
        }

        if (!retreating) {
          const distToSpot = dist(u.x, u.y, roleInfo.spot[0], roleInfo.spot[1]);

          let goal = roleInfo.spot;
          let useFlow = true;
          let exactStop = insideObj || distToObj < myObj.radius + 3 * FP;

          if (u.kind === "artillery") {
            goal = (nearest && bestD < spec.gun.minRange * 1.4)
              ? clampCoord(u.x * 2 - nearest.x, u.y * 2 - nearest.y)
              : null;
            useFlow = false;
          } else if (roleInfo.role === "anchor") {
            if (insideObj && distToSpot < 1.2 * FP) goal = null;
          } else {
            const dangerousTarget = shoot && (shoot.kind === "mbt" || shoot.kind === "missile" || shoot.kind === "apc" || (shoot.kind === "scout" && shootDist < 18 * FP));
            let clearContestant = null;
            if (distToObj <= myObj.radius + 4 * FP && (myObj.state === "contested" || myObj.owner !== side)) {
              for (let j = 0; j < o.contacts.length; j++) {
                const c = o.contacts[j];
                if (dist(c.x, c.y, myObj.x, myObj.y) <= myObj.radius + 3 * FP &&
                    !exactShellClears(u.x, u.y, spec, c.x, c.y, rules.units[c.kind]?.radius)) {
                  clearContestant = c; break;
                }
              }
            }

            if (clearContestant) {
              goal = [clearContestant.x, clearContestant.y];
              useFlow = false;
              exactStop = false;
            } else if (insideObj && distToSpot < 1.3 * FP) {
              goal = null;
            } else if (u.kind === "mbt" && !insideObj && !desperateClock && !stalled && canShootTarget && dangerousTarget) {
              const freeBlindSnipe = !spottedByEnemy && !enemyHasSpotter &&
                shootDist >= 21.0 * FP && shootDist <= effR * 0.96 && bestD >= 21.0 * FP && (myRate >= enRate || !emergency);
              const snipeApc = shoot.kind === "apc" && shootDist >= 15.5 * FP && shootDist <= effR * 0.95 &&
                bestD >= 15.5 * FP && !emergency;
              const midApproach = distToObj > myObj.radius + 9 * FP && shootDist < effR * 0.85 && !emergency;
              if (freeBlindSnipe || snipeApc || midApproach) goal = null;
            }

            // Cohesive 2-MBT wingman rule: wait if wingman is actively fighting/healthy nearby (matching v3 !emergency guard)
            if (u.kind === "mbt" && goal && nearest && (nearest.kind === "mbt" || nearest.kind === "missile") &&
                bestD < 28 * FP && distToObj > myObj.radius + 7 * FP && !emergency && !stalled) {
              let wingD = Infinity;
              for (let j = 0; j < mbts.length; j++) {
                const m = mbts[j];
                if (m.id === u.id || m.hp < 75) continue;
                const dm = dist(u.x, u.y, m.x, m.y);
                if (dm < wingD) wingD = dm;
              }
              if (wingD > 14 * FP && wingD < 38 * FP) goal = null;
            }
          }

          const unitBlindHit = u.kind === "mbt" && o.tick - (blindUnitTick[u.id] || -999) <= 100 &&
            !o.contacts.some((c) => c.kind !== "drone" && dist(u.x, u.y, c.x, c.y) <= 33 * FP);
          if (unitBlindHit && (!goal || dist(u.x, u.y, goal[0], goal[1]) < 4 * FP)) {
            const probeForward = mbts.length >= 2 && u.hp >= 90;
            const angProbe = probeForward
              ? Math.atan2(enemySpawn[1] - u.y, enemySpawn[0] - u.x)
              : Math.atan2(mySpawn[1] - u.y, mySpawn[0] - u.x);
            goal = clampCoord(u.x + Math.cos(angProbe) * 8 * FP, u.y + Math.sin(angProbe) * 8 * FP);
            useFlow = false;
            exactStop = false;
          }

          if (u.kind === "mbt") {
            if (!insideObj && goal === null && !stalled) {
              if (o.tick - lastDamageTick <= 100) {
                mbtStallTicks[u.id] = 0;
              } else {
                mbtStallTicks[u.id] = (mbtStallTicks[u.id] || 0) + 1;
                if (mbtStallTicks[u.id] >= 180 && (enRate > myRate + 0.1 || myObj.owner === 1 - side)) {
                  mbtAdvanceUntil[u.id] = o.tick + 100;
                  mbtStallTicks[u.id] = 0;
                  goal = roleInfo.spot;
                }
              }
            } else {
              mbtStallTicks[u.id] = 0;
            }
          }

          if (!goal && u.kind === "mbt" && shoot && !insideObj && tileAt(u.x, u.y) !== 1) {
            const fg = forestGoal[u.id];
            const stale = !fg || fg.targetId !== shoot.id || o.tick - fg.tick > 250 || dist(u.x, u.y, fg.x, fg.y) < 1.5 * FP;
            if (stale) {
              let found = null;
              outer: for (let r = 1; r <= 3; r++) {
                for (let k = 0; k < 16; k++) {
                  const a = (k / 16) * TWO_PI;
                  const cx = u.x + Math.cos(a) * FP * r, cy = u.y + Math.sin(a) * FP * r;
                  if (tileAt(cx, cy) !== 1 || !passable(cx, cy)) continue;
                  if (dist(cx, cy, shoot.x, shoot.y) > dist(u.x, u.y, shoot.x, shoot.y) + FP) continue;
                  if (dist(cx, cy, shoot.x, shoot.y) > spec.gun.maxRange * 0.95) continue;
                  if (!exactShellClears(cx, cy, spec, shoot.x, shoot.y, shootRad)) continue;
                  found = [cx, cy]; break outer;
                }
              }
              forestGoal[u.id] = found
                ? { x: found[0], y: found[1], tick: o.tick, targetId: shoot.id }
                : { x: 0, y: 0, tick: o.tick, targetId: shoot.id };
            }
            const f2 = forestGoal[u.id];
            if (f2.x) { goal = [f2.x, f2.y]; useFlow = false; exactStop = true; }
          }

          if (o.canMove) {
            const bo = backoffState[u.id];
            if (bo && o.tick < bo.until) {
              order.throttle = -Math.round(FP * 0.75);
              order.steer = bo.steer;
            } else if ((blockedCnt[u.id] || 0) >= 5) {
              const sDir = (u.id + (o.tick >> 3)) & 1 ? FP : -FP;
              backoffState[u.id] = { until: o.tick + 12, steer: sDir };
              blockedCnt[u.id] = 0;
              order.throttle = -Math.round(FP * 0.75);
              order.steer = sDir;
            } else if (goal) {
              const wp = useFlow ? flowTarget(u, myObj.field, roleInfo.spot, alive) : goal;
              const isFinal = !useFlow || (wp[0] === roleInfo.spot[0] && wp[1] === roleInfo.spot[1]);
              const mv = steerTo(u, wp[0], wp[1], spec, alive, 1, exactStop && isFinal);
              order.steer = mv.steer; order.throttle = mv.throttle;
            } else if (aimTgt && (u.kind === "mbt" || u.kind === "apc" || u.kind === "missile" || u.kind === "scout")) {
              const want = angleTo(u.x, u.y, ax || aimTgt.x, ay || aimTgt.y);
              const d = angDiff(u.heading, want);
              order.steer = Math.max(-FP, Math.min(FP, Math.round((d / spec.turnRate) * FP)));
              order.throttle = 0;
            } else if (insideObj && (u.kind === "mbt" || u.kind === "apc")) {
              const want = angleTo(u.x, u.y, enemySpawn[0], enemySpawn[1]);
              const d = angDiff(u.heading, want);
              order.steer = Math.max(-FP, Math.min(FP, Math.round((d / spec.turnRate) * FP)));
              order.throttle = 0;
            }
          }
        }
      }

      // --- 7. Weapons ---
      if (aimTgt && spec.gun.mode !== "none") {
        const aimD = dist(u.x, u.y, ax, ay);
        const effR = effectiveMaxRange(u, spec, ax, ay);
        if (spec.gun.mode === "direct") {
          const fx = Math.round(ax), fy = Math.round(ay);
          order.aimAt = [fx, fy];
          if (u.reload === 0 && (u.ammo === -1 || u.ammo > 0)) {
            const wantFireAng = angleTo(u.x, u.y, fx, fy);
            const curDiff = Math.abs(angDiff(u.turret, wantFireAng));
            const liveToShoot = shoot || nearest;
            if (curDiff <= spec.gun.aimTolerance && liveToShoot && aimD <= effR) {
              const tRad = rules.units[liveToShoot.kind]?.radius;
              if (exactShellClears(u.x, u.y, spec, fx, fy, tRad) ||
                  (dist(fx, fy, liveToShoot.x, liveToShoot.y) < 1.2 * FP && exactShellClears(u.x, u.y, spec, liveToShoot.x, liveToShoot.y, tRad))) {
                const tStep = Math.max(-spec.turretRate, Math.min(spec.turretRate, angDiff(u.turret, wantFireAng)));
                const turretAfter = (u.turret + tStep) & (FULL - 1);
                const maxMove = Math.abs(u.speed) + spec.accel;
                const maxShiftSteps = Math.ceil((maxMove / Math.max(1, aimD)) * (FULL / TWO_PI)) + 3;
                if (!spec.fixedGun && u.kind !== "scout" && aimD >= 5 * FP &&
                    Math.abs(angDiff(turretAfter, wantFireAng)) + maxShiftSteps <= spec.gun.aimTolerance) {
                  order.fire = [fx, fy];
                } else {
                  order.fire = true;
                }
              }
            }
          }
        } else if (spec.gun.mode === "indirect") {
          if (u.reload === 0 && (u.ammo === -1 || u.ammo > 0) && aimD >= spec.gun.minRange && aimD <= effR) {
            order.fire = [Math.round(ax), Math.round(ay)];
          }
        }
      } else if (nearest && spec.gun.mode === "none" && spec.secondary) {
        if (u.reload2 === 0 && bestD <= spec.secondary.maxRange) {
          if (Math.abs(angDiff(u.turret, angleTo(u.x, u.y, nearest.x, nearest.y))) <= spec.secondary.aimTolerance) order.fire = true;
        }
      }

      orders.push(order);
    }
    return { units: orders };
  },
};
