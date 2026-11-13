/* Hito: elige la mejor parada para repostar a lo largo de una ruta. */
'use strict';

const API = {
  snapshot: 'data/estaciones.json',
  ministerio: 'https://sedeaplicaciones.minetur.gob.es/ServiciosRESTCarburantes/PreciosCarburantes/EstacionesTerrestres/',
  osrm: 'https://router.project-osrm.org',
  photon: 'https://photon.komoot.io/api/',
};
// Registro compacto de estación: [id, lat, lon, rótulo, dirección, localidad, municipio, provincia, horario, g95, g98, gA, gA+, GLP]
const FUELS = [
  { k: 'g95', n: 'Gasolina 95', i: 9 },
  { k: 'g98', n: 'Gasolina 98', i: 10 },
  { k: 'gA', n: 'Diésel', i: 11 },
  { k: 'gAp', n: 'Diésel Premium', i: 12 },
  { k: 'glp', n: 'GLP', i: 13 },
];
const SNAPSHOT_MAX_AGE_H = 36;
const MAX_REFINE = 24;      // candidatas a las que se mide el desvío real
const SPAN_KM = 3;          // tramo de ruta antes y después de la estación para medir el desvío
const ON_ROUTE_KM = 0.4;    // "a pie de ruta"

const $ = (id) => document.getElementById(id);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = (n, d = 2) => n.toLocaleString('es-ES', { minimumFractionDigits: d, maximumFractionDigits: d });
const eur = (n) => fmt(n, 2) + ' €';
const nice = (s) => String(s).toLowerCase().replace(/(^|[\s\-/.(])([a-záéíóúñü])/g, (m, a, b) => a + b.toUpperCase());

const state = { fuel: 'g95', origin: null, dest: null, stations: null, dataDate: '', plan: null, sort: 'score', map: null, layer: null };

/* ---------- Geometría ---------- */
function hav(aLat, aLon, bLat, bLon) {
  const R = 6371, r = Math.PI / 180;
  const dLat = (bLat - aLat) * r, dLon = (bLon - aLon) * r;
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(aLat * r) * Math.cos(bLat * r) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(h));
}

/* Convierte la geometría de OSRM en puntos {lat, lon, km} cada ~0,4 km como mucho. */
function buildRoute(coords, distKm, durMin) {
  let raw = 0;
  const cum = [0];
  for (let i = 1; i < coords.length; i++) {
    raw += hav(coords[i - 1][1], coords[i - 1][0], coords[i][1], coords[i][0]);
    cum.push(raw);
  }
  const k = raw > 0 ? distKm / raw : 1;
  const pts = [];
  const STEP = 0.4;
  for (let i = 0; i < coords.length; i++) {
    if (i > 0) {
      const seg = cum[i] - cum[i - 1];
      const n = Math.floor(seg / STEP);
      for (let j = 1; j <= n; j++) {
        const t = j / (n + 1);
        pts.push({
          lat: coords[i - 1][1] + (coords[i][1] - coords[i - 1][1]) * t,
          lon: coords[i - 1][0] + (coords[i][0] - coords[i - 1][0]) * t,
          km: (cum[i - 1] + seg * t) * k,
        });
      }
    }
    pts.push({ lat: coords[i][1], lon: coords[i][0], km: cum[i] * k });
  }
  return { pts, distKm, durMin, coords };
}

function pointAtKm(route, km) {
  const p = route.pts;
  let lo = 0, hi = p.length - 1;
  while (lo < hi) { const m = (lo + hi) >> 1; if (p[m].km < km) lo = m + 1; else hi = m; }
  return p[lo];
}

/* Estaciones a menos de corridorKm de la ruta, con su km sobre la ruta. */
function stationsNearRoute(route, stations, fuelIdx, corridorKm) {
  const cell = corridorKm / 75 + 0.005;
  const grid = new Map();
  const key = (a, b) => a + ':' + b;
  route.pts.forEach((p, i) => {
    const kk = key(Math.floor(p.lat / cell), Math.floor(p.lon / cell));
    let arr = grid.get(kk);
    if (!arr) grid.set(kk, (arr = []));
    arr.push(i);
  });
  const out = [];
  for (const s of stations) {
    const price = s[fuelIdx];
    if (!price) continue;
    const cy = Math.floor(s[1] / cell), cx = Math.floor(s[2] / cell);
    let best = Infinity, bi = -1;
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      const arr = grid.get(key(cy + dy, cx + dx));
      if (!arr) continue;
      for (const i of arr) {
        const p = route.pts[i];
        const d = hav(s[1], s[2], p.lat, p.lon);
        if (d < best) { best = d; bi = i; }
      }
    }
    if (bi >= 0 && best <= corridorKm) {
      out.push({ s, price, offKm: best, km: route.pts[bi].km, lat: s[1], lon: s[2] });
    }
  }
  return out;
}

const median = (a) => { const b = [...a].sort((x, y) => x - y); const m = b.length >> 1; return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2; };

/* ---------- Plan de repostaje (función pura) ---------- */
function computeEconomics(c, car, ref) {
  const arrive = car.fuelNow - (c.km + c.detourKm / 2) * car.cons / 100;
  c.litres = Math.max(0, Math.min(car.tank, car.tank - arrive));
  c.detourCost = c.detourKm * car.cons / 100 * c.price;
  c.gross = (ref - c.price) * c.litres;
  c.net = c.gross - c.detourCost;
  c.breakEven = c.price < ref ? c.detourCost / (ref - c.price) : null;
  c.score = c.net - c.detourMin * car.timeValue / 60;
}

function makePlan(route, near, car) {
  const D = route.distKm;
  const need = D * car.cons / 100;
  const rangeKm = Math.max(0, (car.fuelNow - car.reserve) / car.cons * 100);
  const fullRangeKm = Math.max(0, (car.tank - car.reserve) / car.cons * 100);
  const mustRefuel = car.fuelNow - need < car.reserve;
  const reachKm = mustRefuel ? Math.min(D, rangeKm) : D;

  let pool = near.filter((c) => c.km + c.offKm <= reachKm + 0.01);
  let outOfReach = false;
  if (mustRefuel && pool.length === 0) {
    outOfReach = true; // no llega a ninguna: se enseñan las primeras de la ruta
    pool = [...near].sort((a, b) => a.km - b.km).slice(0, 6);
  }
  // Si una sola parada basta para llegar, descarta las que obligarían a parar otra vez
  if (mustRefuel) {
    const enough = pool.filter((c) => D - c.km <= fullRangeKm);
    if (enough.length) pool = enough;
  }
  const onRoute = pool.filter((c) => c.offKm <= ON_ROUTE_KM);
  const refFrom = onRoute.length >= 3 ? 'ruta' : 'tramo';
  const ref = pool.length ? median((onRoute.length >= 3 ? onRoute : pool).map((c) => c.price)) : 0;

  for (const c of pool) {
    c.detourKm = c.offKm * 2 * 1.4;         // estimación hasta medir el desvío real
    c.detourMin = c.detourKm / 40 * 60;
    c.exact = false;
    computeEconomics(c, car, ref);
  }
  pool.sort((a, b) => b.score - a.score);
  return { D, need, rangeKm, fullRangeKm, mustRefuel, reachKm, outOfReach, pool, ref, refFrom, near, car, route,
    secondStop: mustRefuel && D - reachKm > fullRangeKm };
}

function rank(plan) {
  for (const c of plan.pool) computeEconomics(c, plan.car, plan.ref);
  plan.pool.sort((a, b) => b.score - a.score);
}

/* ---------- Red ---------- */
async function getJSON(url, opts = {}, ms = 30000) {
  const ctl = new AbortController();
  const t = setTimeout(() => ctl.abort(), ms);
  try {
    const r = await fetch(url, { ...opts, signal: ctl.signal });
    if (!r.ok) throw new Error('HTTP ' + r.status);
    return await r.json();
  } finally { clearTimeout(t); }
}

function compactMinisterio(json) {
  const num = (v) => { if (v == null || v === '') return null; const n = parseFloat(String(v).replace(',', '.')); return Number.isFinite(n) ? n : null; };
  const e = [];
  for (const s of json.ListaEESSPrecio || []) {
    if (s['Tipo Venta'] && s['Tipo Venta'] !== 'P') continue;
    const lat = num(s['Latitud']), lon = num(s['Longitud (WGS84)']);
    if (lat == null || lon == null) continue;
    e.push([s['IDEESS'], lat, lon, s['Rótulo'] || '', s['Dirección'] || '', s['Localidad'] || '', s['Municipio'] || '', s['Provincia'] || '', s['Horario'] || '',
      num(s['Precio Gasolina 95 E5']), num(s['Precio Gasolina 98 E5']), num(s['Precio Gasoleo A']), num(s['Precio Gasoleo Premium']), num(s['Precio Gases licuados del petróleo'])]);
  }
  return { fecha: json.Fecha || '', ts: Date.now(), e };
}

async function loadStations() {
  if (state.stations) return;
  let snap = null;
  try { snap = await getJSON(API.snapshot, { cache: 'no-cache' }, 20000); } catch (_) { /* sin copia */ }
  const fresh = snap && snap.e && snap.e.length > 1000 && (Date.now() - snap.ts) / 36e5 < SNAPSHOT_MAX_AGE_H;
  if (!fresh) {
    try {
      const live = compactMinisterio(await getJSON(API.ministerio, { headers: { Accept: 'application/json' } }, 60000));
      if (live.e.length > 1000) snap = live;
    } catch (_) { /* nos quedamos con la copia si existe */ }
  }
  if (!snap || !snap.e || !snap.e.length) throw new Error('No he podido descargar los precios del Ministerio. Prueba otra vez en un minuto.');
  state.stations = snap.e;
  state.dataDate = snap.fecha;
  $('data-date').textContent = 'Precios actualizados: ' + snap.fecha + ' · ' + fmt(snap.e.length, 0) + ' estaciones';
}

async function geocode(q, limit = 5) {
  const u = API.photon + '?q=' + encodeURIComponent(q) + '&limit=' + limit + '&lat=40.2&lon=-3.7&bbox=-18.5,27.4,4.7,44';
  const j = await getJSON(u, {}, 12000);
  return (j.features || []).map((f) => {
    const p = f.properties || {};
    const name = p.name || [p.street, p.housenumber].filter(Boolean).join(' ') || p.city || q;
    const sub = [p.city && p.city !== name ? p.city : '', p.county && p.county !== name ? p.county : '', p.state].filter(Boolean);
    return { name, sub: [...new Set(sub)].join(', '), lat: f.geometry.coordinates[1], lon: f.geometry.coordinates[0] };
  });
}

async function fetchRoute(a, b) {
  const u = `${API.osrm}/route/v1/driving/${a.lon.toFixed(5)},${a.lat.toFixed(5)};${b.lon.toFixed(5)},${b.lat.toFixed(5)}?overview=full&geometries=geojson`;
  const j = await getJSON(u, {}, 30000);
  if (j.code !== 'Ok' || !j.routes || !j.routes.length) throw new Error('No encuentro una ruta en coche entre esos dos puntos.');
  const r = j.routes[0];
  return buildRoute(r.geometry.coordinates, r.distance / 1000, r.duration / 60);
}

/* Mide el desvío real (km y minutos) de las mejores candidatas con una sola consulta a OSRM. */
async function refineDetours(plan) {
  const cands = plan.pool.slice(0, MAX_REFINE);
  if (!cands.length) return;
  const coords = [], src = [], dst = [];
  cands.forEach((c, i) => {
    const prev = pointAtKm(plan.route, Math.max(0, c.km - SPAN_KM));
    const next = pointAtKm(plan.route, Math.min(plan.D, c.km + SPAN_KM));
    coords.push(prev, { lat: c.lat, lon: c.lon }, next);
    src.push(3 * i, 3 * i + 1);
    dst.push(3 * i + 1, 3 * i + 2);
  });
  const u = `${API.osrm}/table/v1/driving/${coords.map((p) => p.lon.toFixed(5) + ',' + p.lat.toFixed(5)).join(';')}?sources=${src.join(';')}&destinations=${dst.join(';')}&annotations=duration,distance`;
  const j = await getJSON(u, {}, 30000);
  if (j.code !== 'Ok' || !j.durations) return;
  cands.forEach((c, i) => {
    const rp = 2 * i, rs = 2 * i + 1, cs = 2 * i, cn = 2 * i + 1;
    const du = j.durations, di = j.distances;
    const a = du[rp][cs], b = du[rs][cn], base = du[rp][cn];
    if (a == null || b == null || base == null) return;
    c.detourMin = Math.max(0, (a + b - base) / 60);
    if (di && di[rp][cs] != null && di[rs][cn] != null && di[rp][cn] != null) {
      c.detourKm = Math.max(0, (di[rp][cs] + di[rs][cn] - di[rp][cn]) / 1000);
    } else {
      c.detourKm = Math.max(c.offKm * 2, c.detourMin / 60 * 50);
    }
    c.exact = true;
  });
  // Las que no se han medido quedan por detrás de las medidas
  plan.pool = [...cands, ...plan.pool.slice(MAX_REFINE)];
  rank(plan);
}

/* ---------- Interfaz: formulario ---------- */
function readCar() {
  const v = (id, def) => { const n = parseFloat(String($(id).value).replace(',', '.')); return Number.isFinite(n) ? n : def; };
  const tank = Math.max(5, v('deposito', 45));
  return {
    cons: Math.max(1, v('consumo', 5.8)), tank,
    fuelNow: tank * v('nivel', 50) / 100,
    reserve: Math.min(tank * 0.8, Math.max(0, v('reserva', 6))),
    corridor: Math.min(10, Math.max(1, v('pasillo', 4))),
    timeValue: Math.max(0, v('tiempo', 6)),
  };
}

function updateGauge() {
  const car = readCar();
  const km = Math.max(0, (car.fuelNow - car.reserve) / car.cons * 100);
  $('nivel-out').textContent = `${fmt(car.fuelNow, 0)} L · unos ${fmt(km, 0)} km`;
}

function save() {
  try {
    localStorage.setItem('hito', JSON.stringify({
      fuel: state.fuel, consumo: $('consumo').value, deposito: $('deposito').value, nivel: $('nivel').value,
      reserva: $('reserva').value, pasillo: $('pasillo').value, tiempo: $('tiempo').value,
      origin: state.origin && !state.origin.gps ? state.origin : null, dest: state.dest,
    }));
  } catch (_) { /* sin almacenamiento */ }
}

function restore() {
  try {
    const d = JSON.parse(localStorage.getItem('hito') || 'null');
    if (!d) return;
    if (FUELS.some((f) => f.k === d.fuel)) state.fuel = d.fuel;
    for (const k of ['consumo', 'deposito', 'nivel', 'reserva', 'pasillo', 'tiempo']) if (d[k] != null && d[k] !== '') $(k).value = d[k];
    if (d.origin) { state.origin = d.origin; $('origen').value = d.origin.name; }
    if (d.dest) { state.dest = d.dest; $('destino').value = d.dest.name; }
  } catch (_) { /* sin almacenamiento */ }
}

function renderFuels() {
  $('fuels').innerHTML = FUELS.map((f) => `<button type="button" class="chip" role="radio" aria-checked="${f.k === state.fuel}" data-k="${f.k}">${f.n}</button>`).join('');
}

function setupPlace(inputId, suggId, slot) {
  const input = $(inputId), list = $(suggId);
  let timer = 0, seq = 0, items = [];
  const close = () => { list.hidden = true; list.innerHTML = ''; };
  const pick = (it) => { state[slot] = it; input.value = it.name; close(); };
  input.addEventListener('input', () => {
    state[slot] = null;
    clearTimeout(timer);
    const q = input.value.trim();
    if (q.length < 3) return close();
    timer = setTimeout(async () => {
      const my = ++seq;
      try {
        const r = await geocode(q);
        if (my !== seq || document.activeElement !== input) return;
        items = r;
        list.innerHTML = r.map((it, i) => `<li data-i="${i}">${esc(it.name)}<small>${esc(it.sub)}</small></li>`).join('');
        list.hidden = !r.length;
      } catch (_) { close(); }
    }, 280);
  });
  list.addEventListener('pointerdown', (e) => {
    const li = e.target.closest('li');
    if (li) { e.preventDefault(); pick(items[+li.dataset.i]); }
  });
  input.addEventListener('blur', () => { seq++; clearTimeout(timer); setTimeout(close, 150); });
}

async function resolvePlace(slot, inputId, label) {
  if (state[slot]) return state[slot];
  const q = $(inputId).value.trim();
  if (!q) throw new Error(`Dime ${label}.`);
  const r = await geocode(q, 1);
  if (!r.length) throw new Error(`No encuentro "${q}". Prueba con el nombre del municipio.`);
  state[slot] = r[0];
  return r[0];
}

function status(msg, err = false) {
  const el = $('status');
  el.textContent = msg;
  el.classList.toggle('err', err);
}

/* ---------- Interfaz: resultados ---------- */
const gmaps = (c) => {
  const o = state.origin, d = state.dest;
  return `https://www.google.com/maps/dir/?api=1&origin=${o.lat.toFixed(5)},${o.lon.toFixed(5)}&destination=${d.lat.toFixed(5)},${d.lon.toFixed(5)}&waypoints=${c.lat.toFixed(5)},${c.lon.toFixed(5)}&travelmode=driving`;
};
const stName = (c) => nice(c.s[3] || 'Gasolinera');
const stPlace = (c) => [nice(c.s[4]), nice(c.s[5] || c.s[6])].filter(Boolean).join(' · ');
const approx = (c) => (c.exact ? '' : '≈ ');
const mins = (m) => (m < 0.5 ? 'sin desvío' : '+' + fmt(m, 0) + ' min');

function renderChart(plan, best) {
  const W = 340, H = 150, L = 34, R = 8, T = 10, B = 24;
  const all = plan.near;
  if (!all.length) return '';
  const prices = all.map((c) => c.price).sort((a, b) => a - b);
  const lo = prices[Math.floor(prices.length * 0.01)], hi = prices[Math.min(prices.length - 1, Math.ceil(prices.length * 0.99))];
  const pad = Math.max(0.02, (hi - lo) * 0.12);
  const y0 = lo - pad, y1 = hi + pad;
  const x = (km) => L + (km / plan.D) * (W - L - R);
  const y = (p) => T + (1 - (Math.min(y1, Math.max(y0, p)) - y0) / (y1 - y0)) * (H - T - B);
  const inPool = new Set(plan.pool);
  let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Precio de las gasolineras a lo largo de la ruta">`;
  s += `<rect x="${x(0)}" y="${T}" width="${x(plan.reachKm) - x(0)}" height="${H - T - B}" fill="var(--blue-soft)" rx="4"/>`;
  s += `<line x1="${L}" x2="${W - R}" y1="${H - B}" y2="${H - B}" stroke="var(--line)"/>`;
  const step = plan.D > 600 ? 200 : plan.D > 250 ? 100 : plan.D > 100 ? 50 : plan.D > 40 ? 20 : 10;
  for (let k = 0; k <= plan.D; k += step) s += `<line x1="${x(k)}" x2="${x(k)}" y1="${H - B}" y2="${H - B + 4}" stroke="var(--muted)"/><text x="${x(k)}" y="${H - 6}" text-anchor="middle">${k === 0 ? 'km 0' : k}</text>`;
  s += `<text x="${L - 5}" y="${y(hi) + 3}" text-anchor="end">${fmt(hi, 2)}</text><text x="${L - 5}" y="${y(lo) + 3}" text-anchor="end">${fmt(lo, 2)}</text>`;
  if (plan.ref) s += `<line x1="${L}" x2="${W - R}" y1="${y(plan.ref)}" y2="${y(plan.ref)}" stroke="var(--muted)" stroke-dasharray="3 3"/>`;
  for (const c of all) if (!inPool.has(c)) s += `<circle cx="${x(c.km).toFixed(1)}" cy="${y(c.price).toFixed(1)}" r="2" fill="var(--muted)" opacity=".35"/>`;
  for (const c of plan.pool) if (c !== best) s += `<circle cx="${x(c.km).toFixed(1)}" cy="${y(c.price).toFixed(1)}" r="2.6" fill="var(--blue)" opacity=".8"/>`;
  if (best) s += `<line x1="${x(best.km)}" x2="${x(best.km)}" y1="${y(best.price)}" y2="${H - B}" stroke="var(--red)" stroke-width="1.5"/><circle cx="${x(best.km)}" cy="${y(best.price)}" r="5.5" fill="var(--red)" stroke="var(--surface)" stroke-width="2"/>`;
  s += '</svg>';
  return `<section class="card chart"><h3>Precio a lo largo de tu ruta (€/L)</h3>${s}
    <div class="legend"><span><i style="background:var(--red)"></i>Tu parada</span><span><i style="background:var(--blue)"></i>A tu alcance</span><span><i style="background:var(--muted);opacity:.5"></i>Fuera de alcance</span><span>Zona azul: hasta donde llegas${plan.ref ? ' · Línea: precio habitual' : ''}</span></div></section>`;
}

function renderList(plan, best) {
  const pool = plan.pool;
  const cheapest = pool.reduce((a, c) => (c.price < a.price ? c : a), pool[0]);
  const measured = pool.filter((c) => c.exact);
  const quick = (measured.length ? measured : pool).reduce((a, c) => (c.detourMin < a.detourMin ? c : a));
  let items = [...pool];
  if (state.sort === 'price') items.sort((a, b) => a.price - b.price || a.detourMin - b.detourMin);
  else if (state.sort === 'detour') items.sort((a, b) => a.detourMin - b.detourMin || a.price - b.price);
  items = items.slice(0, 8);
  const li = items.map((c) => {
    const tags = [c === best ? '<span class="tag">Recomendada</span>' : '', c === cheapest ? '<span class="tag">Más barata</span>' : '', c === quick ? '<span class="tag">Menos desvío</span>' : ''].join('');
    const cls = c.net > 0.005 ? 'pos' : c.net < -0.005 ? 'negv' : '';
    return `<li>
      <div class="kmtag">km<b>${fmt(c.km, 0)}</b></div>
      <div class="st">${tags}<b>${esc(stName(c))}</b><small>${esc(stPlace(c))}</small><small>${fmt(c.price, 3)} €/L · ${approx(c)}${mins(c.detourMin)} · ${fmt(c.litres, 0)}&nbsp;L</small><a href="${gmaps(c)}" target="_blank" rel="noopener">Ruta con esta parada</a></div>
      <div class="amt"><b class="${cls}">${c.net >= 0 ? '+' : '−'}${fmt(Math.abs(c.net), 2)} €</b><small>neto</small></div>
    </li>`;
  }).join('');
  const btn = (k, t) => `<button type="button" data-sort="${k}" aria-pressed="${state.sort === k}">${t}</button>`;
  return `<section class="card"><h3>Otras paradas a tu alcance</h3>
    <div class="sorter">${btn('score', 'Mejor')}${btn('price', 'Más barata')}${btn('detour', 'Menos desvío')}</div>
    <ul class="list">${li}</ul></section>`;
}

function renderResults() {
  const plan = state.plan, car = plan.car, best = plan.pool[0];
  const fuelName = FUELS.find((f) => f.k === state.fuel).n;
  const h = Math.floor(plan.route.durMin / 60), m = Math.round(plan.route.durMin % 60);
  let html = `<div class="trip"><span><b>${fmt(plan.D, 0)} km</b></span><span><b>${h ? h + ' h ' : ''}${m} min</b></span><span>Gastarás <b>${fmt(plan.need, 1)} L</b></span><span>Con lo que llevas llegas al <b>km ${fmt(Math.min(plan.D, plan.rangeKm), 0)}</b></span></div>`;

  if (!plan.near.length) {
    html += `<p class="note warn">No hay gasolineras con ${esc(fuelName)} a menos de ${fmt(car.corridor, 0)} km de esta ruta. Amplía la búsqueda en Ajustes finos.</p>`;
    $('results').innerHTML = html; $('results').hidden = false; return;
  }
  if (plan.outOfReach) html += `<p class="note warn">Con ese nivel no llegas a ninguna gasolinera de la ruta sin bajar de ${fmt(car.reserve, 0)} L. Estas son las primeras que encontrarás: reposta cuanto antes.</p>`;
  else if (!plan.mustRefuel) html += `<p class="note ok">Llegas sin repostar y te sobran ${fmt(car.fuelNow - plan.need, 0)} L. Si aun así quieres llenar por el camino, esta es la mejor parada.</p>`;
  if (plan.secondStop) html += `<p class="note warn">El viaje es más largo que un depósito: necesitarás una segunda parada. Vuelve a calcular desde la primera.</p>`;

  const savingLabel = best.net >= 0 ? 'Ahorro neto' : 'Sobrecoste';
  let why;
  if (best.detourMin < 0.5) why = 'Te pilla de camino: no pierdes tiempo.';
  else if (best.breakEven != null && best.breakEven < best.litres) why = `El desvío compensa a partir de ${fmt(Math.max(0.1, best.breakEven), 1)} L, y vas a echar ${fmt(best.litres, 0)}.`;
  else why = 'Es la opción con mejor equilibrio entre precio y desvío en el tramo al que llegas.';

  html += `<article class="card best">
    <div class="best-head">
      <div class="hito" aria-label="Kilómetro ${fmt(best.km, 0)} de tu ruta"><i>KM</i><b>${fmt(best.km, 0)}</b></div>
      <div class="best-id"><span class="eyebrow">Tu parada</span><h2>${esc(stName(best))}</h2><p>${esc(stPlace(best))}${best.s[8] ? ' · ' + esc(best.s[8]) : ''}</p></div>
      <div class="price"><b>${fmt(best.price, 3)}</b><span>€/L · ${esc(fuelName)}</span></div>
    </div>
    <dl class="rows">
      <div><dt>Precio habitual a pie de ruta</dt><dd>${fmt(plan.ref, 3)} €/L</dd></div>
      <div><dt>Diferencia por litro</dt><dd>${best.price <= plan.ref ? '−' : '+'}${fmt(Math.abs(plan.ref - best.price), 3)} €</dd></div>
      <div><dt>Litros que echarás</dt><dd>${fmt(best.litres, 0)} L</dd></div>
      <div><dt>Desvío</dt><dd class="${best.detourMin >= 0.5 ? 'neg' : ''}">${approx(best)}${fmt(best.detourKm, 1)} km · ${mins(best.detourMin)}</dd></div>
      <div><dt>Coste del desvío</dt><dd class="${best.detourCost >= 0.005 ? 'neg' : ''}">−${eur(best.detourCost)}</dd></div>
    </dl>
    <div class="net ${best.net > 0.005 ? '' : 'zero'}"><span>${savingLabel}</span><b>${eur(Math.abs(best.net))}</b></div>
    <p class="why">${why}</p>
    <a class="go" href="${gmaps(best)}" target="_blank" rel="noopener">Ir con esta parada en Google Maps</a>
  </article>`;

  html += renderChart(plan, best);
  html += '<section class="card"><h3>Mapa</h3><div id="map"></div></section>';
  if (plan.pool.length > 1) html += `<div id="list">${renderList(plan, best)}</div>`;

  $('results').innerHTML = html;
  $('results').hidden = false;
  $('intro').hidden = true;
  renderMap(plan, best);
}

function renderMap(plan, best) {
  if (!window.L) return;
  if (state.map) { state.map.remove(); state.map = null; }
  const dark = matchMedia('(prefers-color-scheme: dark)').matches;
  const map = L.map('map', { zoomControl: false, attributionControl: true });
  map.attributionControl.setPrefix(false);
  L.tileLayer(`https://{s}.basemaps.cartocdn.com/${dark ? 'dark_all' : 'rastertiles/voyager'}/{z}/{x}/{y}{r}.png`, {
    maxZoom: 19, subdomains: 'abcd', attribution: '© OpenStreetMap, © CARTO',
  }).addTo(map);
  const css = getComputedStyle(document.documentElement);
  const line = L.polyline(plan.route.coords.map((c) => [c[1], c[0]]), { color: css.getPropertyValue('--blue').trim() || '#0B4EA2', weight: 4, opacity: 0.9 }).addTo(map);
  for (const c of plan.pool.slice(1, 6).reverse()) {
    L.marker([c.lat, c.lon], { icon: L.divIcon({ className: '', html: `<div class="pin">${fmt(c.price, 3)}</div>`, iconSize: [0, 0] }) }).addTo(map);
  }
  if (best) L.marker([best.lat, best.lon], { zIndexOffset: 1000, icon: L.divIcon({ className: '', html: `<div class="pin top">${fmt(best.price, 3)} €</div>`, iconSize: [0, 0] }) }).addTo(map);
  const end = (p, t) => L.circleMarker([p.lat, p.lon], { radius: 6, color: '#fff', weight: 2, fillColor: '#10202E', fillOpacity: 1 }).addTo(map).bindTooltip(t);
  end(state.origin, 'Salida'); end(state.dest, 'Destino');
  map.fitBounds(line.getBounds(), { padding: [24, 24] });
  state.map = map;
}

/* ---------- Flujo principal ---------- */
async function run() {
  const btn = $('btn-go');
  btn.disabled = true;
  try {
    status('Buscando los lugares…');
    const a = await resolvePlace('origin', 'origen', 'de dónde sales');
    const b = await resolvePlace('dest', 'destino', 'a dónde vas');
    save();
    status('Trazando la ruta y descargando precios…');
    const [route] = await Promise.all([fetchRoute(a, b), loadStations()]);
    const car = readCar();
    const fuel = FUELS.find((f) => f.k === state.fuel);
    const near = stationsNearRoute(route, state.stations, fuel.i, car.corridor);
    const plan = makePlan(route, near, car);
    state.plan = plan;
    if (plan.pool.length) {
      status('Midiendo el desvío real de las mejores paradas…');
      try { await refineDetours(plan); } catch (_) { /* seguimos con la estimación */ }
    }
    renderResults();
    status(plan.pool.some((c) => !c.exact) && plan.pool[0] && !plan.pool[0].exact ? 'No he podido medir los desvíos exactos: los minutos son aproximados.' : '');
    $('results').scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'start' });
  } catch (e) {
    status(e && e.name === 'AbortError' ? 'El servidor tarda demasiado. Prueba otra vez.' : (e && e.message) || 'Algo ha fallado. Prueba otra vez.', true);
  } finally {
    btn.disabled = false;
  }
}

function init() {
  restore();
  renderFuels();
  updateGauge();
  setupPlace('origen', 'sugg-origen', 'origin');
  setupPlace('destino', 'sugg-destino', 'dest');

  $('fuels').addEventListener('click', (e) => {
    const b = e.target.closest('.chip');
    if (!b) return;
    state.fuel = b.dataset.k; renderFuels(); save();
  });
  for (const id of ['consumo', 'deposito', 'nivel', 'reserva', 'pasillo', 'tiempo']) $(id).addEventListener('input', () => { updateGauge(); save(); });
  $('btn-swap').addEventListener('click', () => {
    [state.origin, state.dest] = [state.dest, state.origin];
    const o = $('origen').value; $('origen').value = $('destino').value; $('destino').value = o;
  });
  $('btn-geo').addEventListener('click', () => {
    if (!navigator.geolocation) return status('Este navegador no da la ubicación.', true);
    const b = $('btn-geo'); b.classList.add('busy');
    navigator.geolocation.getCurrentPosition((p) => {
      b.classList.remove('busy');
      state.origin = { name: 'Mi ubicación', sub: '', lat: p.coords.latitude, lon: p.coords.longitude, gps: true };
      $('origen').value = 'Mi ubicación'; status('');
    }, () => { b.classList.remove('busy'); status('No he podido leer tu ubicación. Escribe el origen.', true); }, { enableHighAccuracy: false, timeout: 10000, maximumAge: 60000 });
  });
  $('form').addEventListener('submit', (e) => { e.preventDefault(); run(); });
  $('results').addEventListener('click', (e) => {
    const b = e.target.closest('[data-sort]');
    if (!b || !state.plan) return;
    state.sort = b.dataset.sort;
    $('list').innerHTML = renderList(state.plan, state.plan.pool[0]);
  });
}

if (typeof document !== 'undefined') init();
if (typeof module !== 'undefined') module.exports = { hav, buildRoute, stationsNearRoute, makePlan, rank, computeEconomics, pointAtKm };
