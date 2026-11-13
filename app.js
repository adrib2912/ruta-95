/* Ruta 95: elige dónde repostar a lo largo de una ruta. */
'use strict';

const API = {
  snapshot: 'data/estaciones.json',
  ministerio: 'https://sedeaplicaciones.minetur.gob.es/ServiciosRESTCarburantes/PreciosCarburantes/EstacionesTerrestres/',
  osrm: ['https://router.project-osrm.org', 'https://routing.openstreetmap.de/routed-car'],
  photon: 'https://photon.komoot.io/api/',
  nominatim: 'https://nominatim.openstreetmap.org/search',
};
// Registro compacto de estación: [id, lat, lon, rótulo, dirección, localidad, municipio, provincia, horario, g95, g98, gA, gA+, GLP]
const FUELS = [
  { k: 'g95', n: 'Gasolina 95', i: 9 },
  { k: 'g98', n: 'Gasolina 98', i: 10 },
  { k: 'gA', n: 'Diésel', i: 11 },
  { k: 'gAp', n: 'Diésel Premium', i: 12 },
  { k: 'glp', n: 'GLP', i: 13 },
];
const BRANDS = [
  { k: 'repsol', n: 'Repsol', re: /REPSOL|CAMPSA|PETRONOR/i },
  { k: 'moeve', n: 'Moeve / Cepsa', re: /MOEVE|CEPSA/i },
  { k: 'bp', n: 'BP', re: /(^|[^A-Z])BP([^A-Z]|$)/i },
  { k: 'galp', n: 'Galp', re: /GALP/i },
  { k: 'shell', n: 'Shell', re: /SHELL/i },
  { k: 'carrefour', n: 'Carrefour', re: /CARREFOUR/i },
  { k: 'alcampo', n: 'Alcampo', re: /ALCAMPO/i },
];
const SNAPSHOT_MAX_AGE_H = 36;
const SHORTLIST = 30;       // candidatas por tramo a las que se mide el desvío real
const SPAN_KM = 10;         // tramo de ruta antes y después de la estación para medir el desvío
const ON_ROUTE_KM = 0.4;    // "a pie de ruta"
const STOP_MIN = 6;         // minutos que cuesta una parada (repostar y pagar)
const MIN_LITRES = 5;       // no se propone echar menos
const MAX_STOPS = 5;

const $ = (id) => document.getElementById(id);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = (n, d = 2) => n.toLocaleString('es-ES', { minimumFractionDigits: d, maximumFractionDigits: d });
const eur = (n) => fmt(n, 2) + ' €';
const nice = (s) => String(s).toLowerCase().replace(/(^|[\s\-/.(])([a-záéíóúñü])/g, (m, a, b) => a + b.toUpperCase());

const state = { fuel: 'g95', origin: null, dest: null, stops: [], discounts: {}, stations: null, dataNote: '', plan: null, sort: 'score', map: null, markers: new Map() };

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

/* ---------- Horarios ---------- */
const DAYS = { L: 0, M: 1, X: 2, J: 3, V: 4, S: 5, D: 6 };
function parseHorario(h) {
  if (!h) return null;
  const out = Array.from({ length: 7 }, () => []);
  for (const part of String(h).split(';')) {
    if (!part.trim()) continue;
    const m = part.trim().match(/^([LMXJVSD])(?:\s*-\s*([LMXJVSD]))?\s*:\s*(.+)$/i);
    if (!m) return null;
    const a = DAYS[m[1].toUpperCase()], b = m[2] ? DAYS[m[2].toUpperCase()] : a;
    const days = [];
    for (let d = a; ; d = (d + 1) % 7) { days.push(d); if (d === b) break; }
    const spec = m[3];
    let ranges = [];
    if (/24\s*H/i.test(spec)) ranges = [[0, 1440]];
    else {
      const re = /(\d{1,2}):(\d{2})\s*-\s*(\d{1,2}):(\d{2})/g;
      let r;
      while ((r = re.exec(spec))) {
        const s = +r[1] * 60 + +r[2];
        let e = +r[3] * 60 + +r[4];
        if (e === 1439) e = 1440;
        if (e <= s) e += 1440;
        ranges.push([s, e]);
      }
      if (!ranges.length) return null;
    }
    for (const d of days) out[d].push(...ranges);
  }
  return out;
}
/* true: abierta, false: cerrada, null: horario ilegible */
function isOpenAt(h, date) {
  const sched = parseHorario(h);
  if (!sched) return null;
  const dow = (date.getDay() + 6) % 7, min = date.getHours() * 60 + date.getMinutes();
  if (sched[dow].some(([s, e]) => min >= s && min < e)) return true;
  return sched[(dow + 6) % 7].some(([s, e]) => e > 1440 && min + 1440 < e);
}

/* ---------- Estaciones cerca de la ruta ---------- */
function effectivePrice(s, listPrice) {
  for (const b of BRANDS) {
    const cts = state.discounts[b.k];
    if (cts > 0 && b.re.test(s[3] || '')) return { price: Math.max(0.1, listPrice - cts / 100), disc: cts };
  }
  return { price: listPrice, disc: 0 };
}

function stationsNearRoute(route, stations, fuelIdx, corridorKm, depart) {
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
    const listPrice = s[fuelIdx];
    if (!listPrice) continue;
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
    if (bi < 0 || best > corridorKm) continue;
    const km = route.pts[bi].km;
    const eta = new Date(depart.getTime() + (km / route.distKm) * route.durMin * 60000);
    const o1 = isOpenAt(s[8], eta), o2 = isOpenAt(s[8], new Date(eta.getTime() + 15 * 60000));
    const ep = effectivePrice(s, listPrice);
    out.push({ s, id: s[0], price: ep.price, listPrice, disc: ep.disc, offKm: best, km, lat: s[1], lon: s[2], eta,
      open: o1 === null ? null : o1 && o2 !== false,
      detourKm: best * 2 * 1.4, detourMin: best * 2 * 1.4 / 40 * 60, exact: false });
  }
  return out;
}

const median = (a) => { const b = [...a].sort((x, y) => x - y); const m = b.length >> 1; return b.length % 2 ? b[m] : (b[m - 1] + b[m]) / 2; };

/* ---------- Plan de repostaje ---------- */
/* Simula un plan. modes[i]: 'full' llena el depósito, 'min' echa lo justo para llegar a la siguiente parada.
   Lleva dos niveles de depósito: el esperado (consumo medio) y el prudente (consumo con margen). */
function evalPlan(stops, modes, P, strict = true) {
  const car = P.car, c = car.cons / 100, cs = car.consSafe / 100;
  let fuel = car.fuelNow, safe = car.fuelNow, pos = 0, prevDet = 0;
  let gross = 0, detCost = 0, detMin = 0, litres = 0;
  const legs = [];
  for (let i = 0; i < stops.length; i++) {
    const s = stops[i];
    const dist = Math.max(0, s.km - pos) + prevDet / 2 + s.detourKm / 2;
    fuel -= dist * c; safe -= dist * cs;
    if (strict && safe < car.reserve - 0.01) return null;
    const nextDist = (i < stops.length - 1 ? stops[i + 1].km - s.km + stops[i + 1].detourKm / 2 : P.D - s.km) + s.detourKm / 2;
    const room = car.tank - Math.max(0, fuel);
    let L;
    if (modes[i] === 'full') L = room;
    else {
      const needed = car.reserve + nextDist * cs - safe;
      if (needed <= 0.5) return null;            // parada innecesaria
      L = Math.min(room, Math.max(needed, MIN_LITRES));
    }
    if (L < 1) return null;
    fuel = Math.max(0, fuel) + L; safe = Math.min(car.tank, Math.max(0, safe) + L);
    const cost = s.detourKm * c * s.price;
    gross += (P.ref - s.price) * L; detCost += cost; detMin += s.detourMin; litres += L;
    legs.push({ s, L, full: L >= room - 0.5, detCost: cost });
    pos = s.km; prevDet = s.detourKm;
  }
  const last = Math.max(0, P.D - pos) + prevDet / 2;
  const endSafe = safe - last * cs;
  const complete = endSafe >= car.reserve - 0.01;
  if (strict && !complete) return null;
  const net = gross - detCost;
  return { legs, stops, gross, detCost, detMin, litres, net, complete,
    score: net - (detMin + STOP_MIN * stops.length) * car.timeValue / 60 };
}

function preparePlan(route, near, car) {
  const D = route.distKm;
  const need = D * car.cons / 100;
  const rangeKm = Math.max(0, (car.fuelNow - car.reserve) / car.consSafe * 100);
  const fullRangeKm = Math.max(0, (car.tank - car.reserve) / car.consSafe * 100);
  const mustRefuel = car.fuelNow - D * car.consSafe / 100 < car.reserve;
  const reachKm = mustRefuel ? Math.min(D, rangeKm) : D;
  const cands = near.filter((c) => c.open !== false);
  const closed = near.length - cands.length;

  // Precio de referencia: gasolineras a pie de carretera, sin contar los tramos urbanos de salida y llegada
  const edge = Math.min(15, D * 0.15);
  const onRoute = cands.filter((c) => c.offKm <= ON_ROUTE_KM);
  const road = onRoute.filter((c) => c.km >= edge && c.km <= D - edge);
  const refSet = road.length >= 3 ? road : onRoute.length >= 3 ? onRoute : cands;
  const ref = refSet.length ? median(refSet.map((c) => c.price)) : 0;

  const P = { D, need, rangeKm, fullRangeKm, mustRefuel, reachKm, closed, ref, near, cands, car, route,
    refKind: road.length >= 3 ? 'carretera' : 'ruta' };
  const est = (c) => {
    const L = Math.min(car.tank, car.tank - Math.max(0, car.fuelNow - c.km * car.cons / 100));
    return (ref - c.price) * L - c.detourKm * car.cons / 100 * c.price - c.detourMin * car.timeValue / 60;
  };
  let first = cands.filter((c) => c.km + c.offKm <= reachKm + 0.01);
  P.outOfReach = mustRefuel && first.length === 0;
  if (P.outOfReach) first = [...cands].sort((a, b) => a.km - b.km).slice(0, 6);
  P.first = first.sort((a, b) => est(b) - est(a)).slice(0, SHORTLIST);
  const inFirst = new Set(P.first);
  P.later = !mustRefuel ? [] : cands
    .filter((c) => !inFirst.has(c) && c.km > reachKm && c.km <= rangeKm + fullRangeKm)
    .sort((a, b) => ((ref - b.price) * car.tank * 0.7 - b.detourMin * car.timeValue / 60) - ((ref - a.price) * car.tank * 0.7 - a.detourMin * car.timeValue / 60))
    .slice(0, SHORTLIST);
  P.short = [...P.first, ...P.later];
  return P;
}

function solve(P) {
  const strict = !P.outOfReach;
  let singles = P.first.map((s) => evalPlan([s], ['full'], P, strict)).filter(Boolean);
  let pairs = [];
  if (P.mustRefuel && strict && !singles.length) {
    const pool2 = P.short;
    for (const a of P.first) for (const b of pool2) {
      if (b === a || b.km < a.km + 20) continue;
      // Aquí ya se sabe que con una parada no se llega: en la cara se echa lo justo y en la barata se llena.
      const modes = b.price < a.price ? ['min', 'full'] : ['full', b.price < P.ref ? 'full' : 'min'];
      const pl = evalPlan([a, b], modes, P, true);
      if (pl) pairs.push(pl);
    }
  }
  P.incomplete = false;
  if (!singles.length && !pairs.length) {
    // Ni con dos paradas se llega: se enseña la mejor primera parada y se avisa
    singles = P.first.map((s) => evalPlan([s], ['full'], P, false)).filter(Boolean);
    P.incomplete = true;
  }
  singles.sort((x, y) => y.score - x.score);
  pairs.sort((x, y) => y.score - x.score);
  const s1 = singles[0], p2 = pairs[0];
  P.singles = singles;
  P.chosen = s1 || p2;
  return P;
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

async function osrm(path, ms = 30000) {
  let err;
  for (const base of API.osrm) {
    try {
      const j = await getJSON(base + path, {}, ms);
      if (j && j.code === 'Ok') return j;
      err = new Error((j && j.code) || 'sin respuesta');
      if (j && j.code === 'NoRoute') break;
    } catch (e) { err = e; }
  }
  throw err;
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
  return { fecha: json.Fecha || '', ts: Date.now(), e, live: true };
}

async function loadStations() {
  if (state.stations) return;
  let snap = null;
  try { snap = await getJSON(API.snapshot, { cache: 'no-cache' }, 20000); } catch (_) { /* sin copia */ }
  const ageH = snap && snap.ts ? (Date.now() - snap.ts) / 36e5 : Infinity;
  const fresh = snap && snap.e && snap.e.length > 1000 && ageH < SNAPSHOT_MAX_AGE_H;
  if (!fresh) {
    try {
      const live = compactMinisterio(await getJSON(API.ministerio, { headers: { Accept: 'application/json' } }, 60000));
      if (live.e.length > 1000) snap = live;
    } catch (_) { /* nos quedamos con la copia si existe */ }
  }
  if (!snap || !snap.e || !snap.e.length) throw new Error('No he podido descargar los precios del Ministerio. Prueba otra vez en un minuto.');
  state.stations = snap.e;
  const src = snap.live ? 'descargados ahora del Ministerio' : ageH < 1 ? 'copia de hace menos de 1 h' : `copia de hace ${fmt(ageH, 0)} h`;
  $('data-date').textContent = `Precios del ${snap.fecha} (${src}) · ${fmt(snap.e.length, 0)} estaciones`;
}

async function geocode(q, limit = 5) {
  try {
    const u = API.photon + '?q=' + encodeURIComponent(q) + '&limit=' + limit + '&lat=40.2&lon=-3.7&bbox=-18.5,27.4,4.7,44';
    const j = await getJSON(u, {}, 10000);
    const r = (j.features || []).map((f) => {
      const p = f.properties || {};
      const name = p.name || [p.street, p.housenumber].filter(Boolean).join(' ') || p.city || q;
      const sub = [p.city && p.city !== name ? p.city : '', p.county && p.county !== name ? p.county : '', p.state].filter(Boolean);
      return { name, sub: [...new Set(sub)].join(', '), lat: f.geometry.coordinates[1], lon: f.geometry.coordinates[0] };
    });
    if (r.length) return r;
  } catch (_) { /* probamos el otro buscador */ }
  const j = await getJSON(`${API.nominatim}?format=jsonv2&limit=${limit}&countrycodes=es,pt,fr,ad&accept-language=es&q=${encodeURIComponent(q)}`, {}, 12000);
  return (j || []).map((x) => {
    const parts = String(x.display_name || q).split(',').map((t) => t.trim());
    return { name: parts[0], sub: parts.slice(1, 3).join(', '), lat: +x.lat, lon: +x.lon };
  });
}

async function fetchRoute(points) {
  let j;
  try {
    j = await osrm(`/route/v1/driving/${points.map((p) => p.lon.toFixed(5) + ',' + p.lat.toFixed(5)).join(';')}?overview=full&geometries=geojson&steps=true${points.length === 2 ? '&alternatives=3' : ''}`);
  } catch (e) {
    throw new Error(e && e.message === 'NoRoute' ? 'No encuentro una ruta en coche entre esos puntos.' : 'El servicio de rutas no responde. Prueba otra vez en un momento.');
  }
  return j.routes.slice(0, 3).map((r) => {
    const route = buildRoute(r.geometry.coordinates, r.distance / 1000, r.duration / 60);
    let acc = 0;
    route.stopKm = (r.legs || []).slice(0, -1).map((l) => (acc += l.distance / 1000));
    route.name = [...new Set((r.legs || []).flatMap((l) => String(l.summary || '').split(',').map((t) => t.trim()).filter(Boolean)))].slice(0, 3).join(', ');
    return route;
  });
}

/* Mide el desvío real (km y minutos) de un grupo de candidatas con una consulta a OSRM. */
async function refineBatch(P, cands) {
  if (!cands.length) return;
  const coords = [], src = [], dst = [];
  cands.forEach((c, i) => {
    coords.push(pointAtKm(P.route, Math.max(0, c.km - SPAN_KM)), { lat: c.lat, lon: c.lon }, pointAtKm(P.route, Math.min(P.D, c.km + SPAN_KM)));
    src.push(3 * i, 3 * i + 1);
    dst.push(3 * i + 1, 3 * i + 2);
  });
  const j = await osrm(`/table/v1/driving/${coords.map((p) => p.lon.toFixed(5) + ',' + p.lat.toFixed(5)).join(';')}?sources=${src.join(';')}&destinations=${dst.join(';')}&annotations=duration,distance`);
  if (!j.durations) return;
  cands.forEach((c, i) => {
    const rp = 2 * i, rs = 2 * i + 1, cs = 2 * i, cn = 2 * i + 1;
    const du = j.durations, di = j.distances;
    const a = du[rp][cs], b = du[rs][cn], base = du[rp][cn];
    if (a == null || b == null || base == null) return;
    c.detourMin = Math.max(0, (a + b - base) / 60);
    if (di && di[rp][cs] != null && di[rs][cn] != null && di[rp][cn] != null) c.detourKm = Math.max(0, (di[rp][cs] + di[rs][cn] - di[rp][cn]) / 1000);
    else c.detourKm = Math.max(c.offKm * 2, c.detourMin / 60 * 50);
    c.exact = true;
  });
}
async function refineDetours(P) {
  await refineBatch(P, P.first);
  if (P.later.length) {
    await new Promise((r) => setTimeout(r, 1100)); // el servidor público pide no pasar de una consulta por segundo
    await refineBatch(P, P.later);
  }
}

/* ---------- Interfaz: formulario ---------- */
function readCar() {
  const v = (id, def) => { const n = parseFloat(String($(id).value).replace(',', '.')); return Number.isFinite(n) ? n : def; };
  const tank = Math.max(5, v('deposito', 45));
  const cons = Math.max(1, v('consumo', 5.8));
  return {
    cons, tank, consSafe: cons * (1 + Math.min(50, Math.max(0, v('margen', 10))) / 100),
    fuelNow: tank * v('nivel', 50) / 100,
    reserve: Math.min(tank * 0.8, Math.max(0, v('reserva', 6))),
    corridor: Math.min(10, Math.max(1, v('pasillo', 4))),
    timeValue: Math.max(0, v('tiempo', 6)),
  };
}

function readDepart() {
  const v = $('salida').value;
  const d = v ? new Date(v) : new Date();
  return Number.isNaN(d.getTime()) ? new Date() : d;
}

function updateGauge() {
  const car = readCar();
  const km = Math.max(0, (car.fuelNow - car.reserve) / car.consSafe * 100);
  $('nivel-out').textContent = `${fmt(car.fuelNow, 0)} L · unos ${fmt(km, 0)} km`;
}

const FIELDS = ['consumo', 'deposito', 'nivel', 'reserva', 'pasillo', 'tiempo', 'margen'];
function save() {
  try {
    localStorage.setItem('ruta95', JSON.stringify({
      fuel: state.fuel, ...Object.fromEntries(FIELDS.map((k) => [k, $(k).value])),
      discounts: state.discounts,
      origin: state.origin && !state.origin.gps ? state.origin : null, dest: state.dest,
      stops: state.stops.filter((x) => x.place).map((x) => x.place),
    }));
  } catch (_) { /* sin almacenamiento */ }
}

function restore() {
  try {
    const d = JSON.parse(localStorage.getItem('ruta95') || 'null');
    if (!d) return;
    if (FUELS.some((f) => f.k === d.fuel)) state.fuel = d.fuel;
    for (const k of FIELDS) if (d[k] != null && d[k] !== '') $(k).value = d[k];
    if (d.discounts && typeof d.discounts === 'object') state.discounts = d.discounts;
    if (d.origin) { state.origin = d.origin; $('origen').value = d.origin.name; }
    if (d.dest) { state.dest = d.dest; $('destino').value = d.dest.name; }
    if (Array.isArray(d.stops)) state.stops = d.stops.slice(0, MAX_STOPS).map((pl) => ({ place: pl, text: pl.name }));
  } catch (_) { /* sin almacenamiento */ }
}

function renderFuels() {
  $('fuels').innerHTML = FUELS.map((f) => `<button type="button" class="chip" role="radio" aria-checked="${f.k === state.fuel}" data-k="${f.k}">${f.n}</button>`).join('');
}

function renderDiscounts() {
  $('discounts').innerHTML = BRANDS.map((b) => `<div class="numfield"><label for="d-${b.k}">${b.n}</label>
    <div class="unit"><input id="d-${b.k}" data-brand="${b.k}" type="number" inputmode="decimal" step="1" min="0" max="50" value="${state.discounts[b.k] || ''}" placeholder="0"><span>cts/L</span></div></div>`).join('');
}

function setupPlace(input, list, onSet) {
  let timer = 0, seq = 0, items = [];
  const close = () => { list.hidden = true; list.innerHTML = ''; };
  const pick = (it) => { onSet(it, it.name); input.value = it.name; close(); save(); };
  input.addEventListener('input', () => {
    onSet(null, input.value);
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

function renderStops() {
  const box = $('stops');
  box.innerHTML = state.stops.map((st, i) => `<div class="field">
      <label for="stop-${i}">Paso por</label>
      <div class="inrow">
        <input id="stop-${i}" type="text" placeholder="Ciudad o dirección" inputmode="search" value="${esc(st.text || '')}">
        <button type="button" class="iconbtn" data-del="${i}" title="Quitar esta parada" aria-label="Quitar esta parada">
          <svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true"><path d="M6 6l12 12M18 6 6 18" stroke="currentColor" stroke-width="2.4" stroke-linecap="round"/></svg>
        </button>
      </div>
      <ul class="sugg" id="sugg-stop-${i}" hidden></ul>
    </div>`).join('');
  state.stops.forEach((st, i) => setupPlace($('stop-' + i), $('sugg-stop-' + i), (pl, text) => { st.place = pl; st.text = text; }));
  $('btn-add').hidden = state.stops.length >= MAX_STOPS;
}

async function resolvePlace(place, text, label) {
  if (place) return place;
  const q = (text || '').trim();
  if (!q) throw new Error(`Dime ${label}.`);
  const r = await geocode(q, 1);
  if (!r.length) throw new Error(`No encuentro "${q}". Prueba con el nombre del municipio.`);
  return r[0];
}

function status(msg, err = false) {
  const el = $('status');
  el.textContent = msg;
  el.classList.toggle('err', err);
}

function locate() {
  return new Promise((res, rej) => {
    if (!navigator.geolocation) return rej(new Error('Este navegador no da la ubicación.'));
    navigator.geolocation.getCurrentPosition(
      (p) => res({ name: 'Mi ubicación', sub: '', lat: p.coords.latitude, lon: p.coords.longitude, gps: true }),
      () => rej(new Error('No he podido leer tu ubicación. Escribe el origen.')),
      { enableHighAccuracy: false, timeout: 10000, maximumAge: 60000 });
  });
}

/* ---------- Interfaz: resultados ---------- */
const gmaps = (cands) => {
  const o = state.origin, d = state.dest, ll = (p) => p.lat.toFixed(5) + ',' + p.lon.toFixed(5);
  const via = state.plan.stopPlaces.map((p, i) => ({ p, km: state.plan.route.stopKm[i] || 0 }));
  for (const c of cands) via.push({ p: c, km: c.km });
  via.sort((x, y) => x.km - y.km);
  return `https://www.google.com/maps/dir/?api=1&origin=${ll(o)}&destination=${ll(d)}&waypoints=${via.map((v) => ll(v.p)).join('%7C')}&travelmode=driving`;
};
const stName = (c) => nice(c.s[3] || 'Gasolinera');
const stTown = (c) => nice(c.s[5] || c.s[6] || '');
const stPlace = (c) => [nice(c.s[4]), stTown(c)].filter(Boolean).join(' · ');
const approx = (c) => (c.exact ? '' : '≈ ');
const mins = (m) => (m < 0.5 ? 'menos de 1 min' : '+' + fmt(m, 0) + ' min');
const hhmm = (d) => d.toLocaleTimeString('es-ES', { hour: '2-digit', minute: '2-digit' });
const priceTxt = (c) => `${fmt(c.price, 3)} €/L${c.disc ? ` (con tu descuento de ${fmt(c.disc, 0)} cts)` : ''}`;

function renderChart(P) {
  const W = 340, H = 150, L = 34, R = 8, T = 10, B = 24;
  const all = P.cands;
  if (!all.length) return '';
  const prices = all.map((c) => c.price).sort((a, b) => a - b);
  const lo = prices[Math.floor(prices.length * 0.01)], hi = prices[Math.min(prices.length - 1, Math.ceil(prices.length * 0.99))];
  const pad = Math.max(0.02, (hi - lo) * 0.12);
  const y0 = lo - pad, y1 = hi + pad;
  const x = (km) => L + (km / P.D) * (W - L - R);
  const y = (p) => T + (1 - (Math.min(y1, Math.max(y0, p)) - y0) / (y1 - y0)) * (H - T - B);
  const short = new Set(P.short), chosen = new Set(P.chosen ? P.chosen.stops : []);
  const tip = (c) => `<title>${esc(stName(c))}, ${esc(stTown(c))}: ${fmt(c.price, 3)} €/L, km ${fmt(c.km, 0)}</title>`;
  let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Precio de las gasolineras a lo largo de la ruta">`;
  s += `<rect x="${x(0)}" y="${T}" width="${x(P.reachKm) - x(0)}" height="${H - T - B}" fill="var(--blue-soft)" rx="4"/>`;
  s += `<line x1="${L}" x2="${W - R}" y1="${H - B}" y2="${H - B}" stroke="var(--line)"/>`;
  const step = P.D > 600 ? 200 : P.D > 250 ? 100 : P.D > 100 ? 50 : P.D > 40 ? 20 : 10;
  for (let k = 0; k <= P.D; k += step) s += `<line x1="${x(k)}" x2="${x(k)}" y1="${H - B}" y2="${H - B + 4}" stroke="var(--muted)"/><text x="${x(k)}" y="${H - 6}" text-anchor="middle">${k === 0 ? 'km 0' : k}</text>`;
  s += `<text x="${L - 5}" y="${y(hi) + 3}" text-anchor="end">${fmt(hi, 2)}</text><text x="${L - 5}" y="${y(lo) + 3}" text-anchor="end">${fmt(lo, 2)}</text>`;
  if (P.ref) s += `<line x1="${L}" x2="${W - R}" y1="${y(P.ref)}" y2="${y(P.ref)}" stroke="var(--muted)" stroke-dasharray="3 3"/>`;
  for (const c of all) if (!short.has(c)) s += `<circle cx="${x(c.km).toFixed(1)}" cy="${y(c.price).toFixed(1)}" r="2" fill="var(--muted)" opacity=".35"/>`;
  for (const c of P.short) if (!chosen.has(c)) s += `<circle class="dot" data-id="${esc(c.id)}" cx="${x(c.km).toFixed(1)}" cy="${y(c.price).toFixed(1)}" r="3.2" fill="var(--blue)" opacity=".85">${tip(c)}</circle>`;
  for (const c of chosen) s += `<line x1="${x(c.km)}" x2="${x(c.km)}" y1="${y(c.price)}" y2="${H - B}" stroke="var(--red)" stroke-width="1.5"/><circle class="dot" data-id="${esc(c.id)}" cx="${x(c.km)}" cy="${y(c.price)}" r="5.5" fill="var(--red)" stroke="var(--surface)" stroke-width="2">${tip(c)}</circle>`;
  s += '</svg>';
  return `<section class="card chart"><h3>Precio a lo largo de tu ruta (€/L)</h3>${s}
    <div class="legend"><span><i style="background:var(--red)"></i>Tu parada</span><span><i style="background:var(--blue)"></i>Candidatas (toca una para verla en el mapa)</span><span><i style="background:var(--muted);opacity:.5"></i>Resto</span><span>Zona azul: hasta donde llegas sin repostar${P.ref ? ' · Línea: precio habitual' : ''}</span></div></section>`;
}

function renderList(P) {
  const all = P.singles;
  if (all.length < 2) return '';
  const st = (pl) => pl.stops[0];
  const cheapest = all.reduce((a, c) => (st(c).price < st(a).price ? c : a));
  const measured = all.filter((c) => st(c).exact);
  const quick = (measured.length ? measured : all).reduce((a, c) => (st(c).detourMin < st(a).detourMin ? c : a));
  let items = [...all];
  if (state.sort === 'price') items.sort((a, b) => st(a).price - st(b).price || st(a).detourMin - st(b).detourMin);
  else if (state.sort === 'detour') items.sort((a, b) => st(a).detourMin - st(b).detourMin || st(a).price - st(b).price);
  // Una fila por zona: la mejor de cada pueblo o área de servicio
  const groups = new Map();
  for (const pl of items) {
    const c = st(pl), key = (stTown(c) || '?') + ':' + Math.round(c.km / 6);
    if (!groups.has(key)) groups.set(key, { pl, more: 0 }); else groups.get(key).more++;
  }
  const rows = [...groups.values()].slice(0, 8);
  const li = rows.map(({ pl, more }) => {
    const c = st(pl);
    const tags = [P.chosen === pl ? '<span class="tag">Recomendada</span>' : '', pl === cheapest ? '<span class="tag">Más barata</span>' : '', pl === quick ? '<span class="tag">Menos desvío</span>' : ''].join('');
    const cls = pl.net > 0.005 ? 'pos' : pl.net < -0.005 ? 'negv' : '';
    return `<li>
      <div class="kmtag">km<b>${fmt(c.km, 0)}</b></div>
      <div class="st">${tags}<b>${esc(stName(c))}</b><small>${esc(stPlace(c))}</small><small>${fmt(c.price, 3)} €/L · ${approx(c)}${mins(c.detourMin)} · ${fmt(pl.litres, 0)}&nbsp;L${c.open === null && c.s[8] ? ' · horario sin confirmar' : ''}</small>
        ${more ? `<small class="more">y ${more} más en la zona</small>` : ''}
        <a href="${gmaps([c])}" target="_blank" rel="noopener">Ruta con esta parada</a> · <a href="#map" data-show="${esc(c.id)}">Ver en el mapa</a></div>
      <div class="amt"><b class="${cls}">${pl.net >= 0 ? '+' : '−'}${fmt(Math.abs(pl.net), 2)} €</b><small>neto</small></div>
    </li>`;
  }).join('');
  const btn = (k, t) => `<button type="button" data-sort="${k}" aria-pressed="${state.sort === k}">${t}</button>`;
  return `<section class="card"><h3>Otras paradas a tu alcance</h3>
    <div class="sorter">${btn('score', 'Mejor')}${btn('price', 'Más barata')}${btn('detour', 'Menos desvío')}</div>
    <ul class="list">${li}</ul></section>`;
}

function renderStopBlock(leg, n, total) {
  const c = leg.s;
  const what = leg.full ? `Llena el depósito: <b>${fmt(leg.L, 0)} L</b>` : `Echa solo <b>${fmt(leg.L, 0)} L</b>, lo justo para llegar a la siguiente`;
  return `<div class="best-head">
      <div class="hito" aria-label="Kilómetro ${fmt(c.km, 0)} de tu ruta"><i>KM</i><b>${fmt(c.km, 0)}</b></div>
      <div class="best-id"><span class="eyebrow">${total > 1 ? `Parada ${n} de ${total}` : 'Tu parada'} · hacia las ${hhmm(c.eta)}</span><h2>${esc(stName(c))}</h2>
        <p>${esc(stPlace(c))}${c.s[8] ? ' · ' + esc(c.s[8]) : ''}${c.open === null && c.s[8] ? ' (horario sin confirmar)' : ''}</p>
        <p class="what">${what} · desvío ${approx(c)}${fmt(c.detourKm, 1)} km, ${mins(c.detourMin)}</p></div>
      <div class="price"><b>${fmt(c.price, 3)}</b><span>€/L${c.disc ? ' con descuento' : ''}</span></div>
    </div>`;
}

function renderResults() {
  const P = state.plan, car = P.car, ch = P.chosen;
  const fuelName = FUELS.find((f) => f.k === state.fuel).n;
  const h = Math.floor(P.route.durMin / 60), m = Math.round(P.route.durMin % 60);
  let html = `<div class="trip"><span><b>${fmt(P.D, 0)} km</b></span><span><b>${h ? h + ' h ' : ''}${m} min</b> sin tráfico</span><span>Gastarás <b>${fmt(P.need, 1)} L</b></span><span>Sin repostar llegas al <b>km ${fmt(Math.min(P.D, P.rangeKm), 0)}</b></span></div>
    <button type="button" class="linkbtn" id="btn-here">Ya estoy en ruta: recalcular desde donde estoy</button>`;
  if (P.routes.length > 1) {
    html += `<div class="alts" role="group" aria-label="Elige tu ruta">${P.routes.map((r, i) => `<button type="button" data-alt="${i}" aria-pressed="${i === P.alt}"><b>${esc(r.name || 'Ruta ' + (i + 1))}</b><small>${fmt(r.distKm, 0)} km · ${Math.floor(r.durMin / 60)} h ${Math.round(r.durMin % 60)} min</small></button>`).join('')}</div>`;
  }

  if (!P.cands.length || !ch) {
    html += `<p class="note warn">${P.closed && !P.cands.length ? `Las ${P.closed} gasolineras de esta ruta están cerradas a la hora a la que pasarías.` : `No hay gasolineras con ${esc(fuelName)} a menos de ${fmt(car.corridor, 0)} km de esta ruta. Amplía la búsqueda en Ajustes finos.`}</p>`;
    $('results').innerHTML = html; $('results').hidden = false; return;
  }
  if (P.outOfReach) html += `<p class="note warn">Con ese nivel no llegas a ninguna gasolinera de la ruta sin bajar de ${fmt(car.reserve, 0)} L. Estas son las primeras que encontrarás: reposta cuanto antes.</p>`;
  else if (!P.mustRefuel) html += `<p class="note ok">Llegas sin repostar y te sobran unos ${fmt(car.fuelNow - P.need, 0)} L. Si aun así quieres llenar por el camino, esta es la mejor parada.</p>`;
  if (P.incomplete && !P.outOfReach) html += '<p class="note warn">El viaje pide más de dos repostajes. Te doy la mejor primera parada; vuelve a calcular desde allí.</p>';
  if (P.closed) html += `<p class="note info">He descartado ${P.closed} ${P.closed === 1 ? 'gasolinera que estará cerrada' : 'gasolineras que estarán cerradas'} cuando pases.</p>`;

  const n = ch.stops.length;
  let why;
  if (n > 1) why = 'Con un solo repostaje no llegas. ' + (ch.legs[0].full ? 'Llenas donde es más barato y completas después lo que falte.' : 'En la primera echas lo justo para alcanzar la segunda, que es más barata.');
  else if (ch.detMin < 0.5) why = 'Te pilla de camino: no pierdes tiempo.';
  else {
    const c = ch.stops[0], be = c.price < P.ref ? ch.detCost / (P.ref - c.price) : null;
    why = be != null && be < ch.litres ? `El desvío compensa a partir de ${fmt(Math.max(0.1, be), 1)} L, y vas a echar ${fmt(ch.litres, 0)}.` : 'Es la opción con mejor equilibrio entre precio y desvío en el tramo al que llegas.';
  }
  const refLabel = P.refKind === 'carretera' ? 'Precio habitual a pie de carretera' : 'Precio habitual en la ruta';
  html += `<article class="card best">
    ${ch.legs.map((l, i) => renderStopBlock(l, i + 1, n)).join('<hr class="sep">')}
    <dl class="rows">
      <div><dt>${refLabel}</dt><dd>${fmt(P.ref, 3)} €/L</dd></div>
      <div><dt>Litros en total</dt><dd>${fmt(ch.litres, 0)} L</dd></div>
      <div><dt>Ahorro en el surtidor</dt><dd>${ch.gross >= 0 ? '' : '−'}${eur(Math.abs(ch.gross))}</dd></div>
      <div><dt>Desvío${n > 1 ? 's' : ''}</dt><dd class="${ch.detMin >= 0.5 ? 'neg' : ''}">${mins(ch.detMin)} · −${eur(ch.detCost)}</dd></div>
    </dl>
    <div class="net ${ch.net > 0.005 ? '' : 'zero'}"><span>${ch.net >= 0 ? 'Ahorro neto' : 'Sobrecoste'}</span><b>${eur(Math.abs(ch.net))}</b></div>
    <p class="why">${why}</p>
    <a class="go" href="${gmaps(ch.stops)}" target="_blank" rel="noopener">Ir con ${n > 1 ? 'estas paradas' : 'esta parada'} en Google Maps</a>
  </article>`;

  html += renderChart(P);
  html += '<section class="card"><h3>Mapa</h3><div id="map"></div></section>';
  html += `<div id="list">${renderList(P)}</div>`;

  $('results').innerHTML = html;
  $('results').hidden = false;
  $('intro').hidden = true;
  renderMap(P);
}

function renderMap(P) {
  if (!window.L) return;
  if (state.map) { state.map.remove(); state.map = null; }
  state.markers = new Map();
  const dark = matchMedia('(prefers-color-scheme: dark)').matches;
  const map = L.map('map', { zoomControl: false, attributionControl: true });
  map.attributionControl.setPrefix(false);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19, attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>', className: dark ? 'tiles-dark' : '',
  }).addTo(map);
  const css = getComputedStyle(document.documentElement);
  const line = L.polyline(P.route.coords.map((c) => [c[1], c[0]]), { color: css.getPropertyValue('--blue').trim() || '#0B4EA2', weight: 4, opacity: 0.9 }).addTo(map);
  const chosen = new Set(P.chosen.stops);
  const popup = (c) => `<b>${esc(stName(c))}</b><br>${esc(stPlace(c))}<br>${priceTxt(c)} · ${approx(c)}${mins(c.detourMin)}<br><a href="${gmaps([c])}" target="_blank" rel="noopener">Ruta con esta parada</a>`;
  const top = new Set(P.singles.slice(0, 5).map((pl) => pl.stops[0]));
  for (const c of P.short) {
    if (chosen.has(c)) continue;
    const mk = top.has(c)
      ? L.marker([c.lat, c.lon], { icon: L.divIcon({ className: '', html: `<div class="pin">${fmt(c.price, 3)}</div>`, iconSize: [0, 0] }) })
      : L.circleMarker([c.lat, c.lon], { radius: 5, color: '#fff', weight: 1.5, fillColor: css.getPropertyValue('--blue').trim() || '#0B4EA2', fillOpacity: 0.9 });
    state.markers.set(String(c.id), mk.addTo(map).bindPopup(popup(c)));
  }
  for (const c of chosen) {
    state.markers.set(String(c.id), L.marker([c.lat, c.lon], { zIndexOffset: 1000, icon: L.divIcon({ className: '', html: `<div class="pin top">${fmt(c.price, 3)} €</div>`, iconSize: [0, 0] }) }).addTo(map).bindPopup(popup(c)));
  }
  const end = (p, t) => L.circleMarker([p.lat, p.lon], { radius: 6, color: '#fff', weight: 2, fillColor: '#10202E', fillOpacity: 1 }).addTo(map).bindTooltip(t);
  end(state.origin, 'Salida'); end(state.dest, 'Destino');
  for (const p of P.stopPlaces) L.circleMarker([p.lat, p.lon], { radius: 5, color: '#10202E', weight: 2, fillColor: '#fff', fillOpacity: 1 }).addTo(map).bindTooltip(p.name);
  map.fitBounds(line.getBounds(), { padding: [24, 24] });
  state.map = map;
}

function showOnMap(id) {
  const mk = state.markers.get(String(id));
  if (!mk || !state.map) return;
  $('map').scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'center' });
  state.map.setView(mk.getLatLng(), Math.max(state.map.getZoom(), 12));
  mk.openPopup();
}

/* ---------- Flujo principal ---------- */
async function run(alt = 0) {
  const btn = $('btn-go');
  btn.disabled = true;
  try {
    status('Buscando los lugares…');
    state.stops = state.stops.filter((x) => x.place || (x.text || '').trim());
    const a = (state.origin = await resolvePlace(state.origin, $('origen').value, 'de dónde sales'));
    const b = (state.dest = await resolvePlace(state.dest, $('destino').value, 'a dónde vas'));
    for (const st of state.stops) st.place = await resolvePlace(st.place, st.text, 'la parada');
    const stopPlaces = state.stops.map((x) => x.place);
    renderStops();
    save();
    status('Trazando la ruta y descargando precios…');
    const [routes] = await Promise.all([fetchRoute([a, ...stopPlaces, b]), loadStations()]);
    const route = routes[alt] || routes[0];
    const car = readCar();
    const fuel = FUELS.find((f) => f.k === state.fuel);
    const near = stationsNearRoute(route, state.stations, fuel.i, car.corridor, readDepart());
    const P = preparePlan(route, near, car);
    P.stopPlaces = stopPlaces;
    P.routes = routes; P.alt = routes.indexOf(route);
    state.plan = P;
    let measured = true;
    if (P.short.length) {
      status('Midiendo el desvío real de las mejores paradas…');
      try { await refineDetours(P); } catch (_) { measured = false; }
    }
    solve(P);
    renderResults();
    status(measured ? '' : 'No he podido medir los desvíos exactos: los minutos son aproximados.');
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
  renderDiscounts();
  updateGauge();
  setupPlace($('origen'), $('sugg-origen'), (pl) => { state.origin = pl; });
  setupPlace($('destino'), $('sugg-destino'), (pl) => { state.dest = pl; });
  renderStops();

  $('btn-add').addEventListener('click', () => {
    if (state.stops.length >= MAX_STOPS) return;
    state.stops.push({ place: null, text: '' }); renderStops(); $('stop-' + (state.stops.length - 1)).focus();
  });
  $('stops').addEventListener('click', (e) => {
    const b = e.target.closest('[data-del]');
    if (!b) return;
    state.stops.splice(+b.dataset.del, 1); renderStops(); save();
  });
  $('fuels').addEventListener('click', (e) => {
    const b = e.target.closest('.chip');
    if (!b) return;
    state.fuel = b.dataset.k; renderFuels(); save();
  });
  $('discounts').addEventListener('input', (e) => {
    const k = e.target.dataset.brand;
    if (!k) return;
    const n = parseFloat(String(e.target.value).replace(',', '.'));
    if (n > 0) state.discounts[k] = Math.min(50, n); else delete state.discounts[k];
    save();
  });
  for (const id of FIELDS) $(id).addEventListener('input', () => { updateGauge(); save(); });
  $('btn-swap').addEventListener('click', () => {
    [state.origin, state.dest] = [state.dest, state.origin];
    const o = $('origen').value; $('origen').value = $('destino').value; $('destino').value = o;
    state.stops.reverse(); renderStops(); save();
  });
  const useLocation = async (then) => {
    const b = $('btn-geo'); b.classList.add('busy');
    try { state.origin = await locate(); $('origen').value = 'Mi ubicación'; status(''); if (then) then(); }
    catch (e) { status(e.message, true); }
    finally { b.classList.remove('busy'); }
  };
  $('btn-geo').addEventListener('click', () => useLocation());
  $('form').addEventListener('submit', (e) => { e.preventDefault(); run(0); });
  $('results').addEventListener('click', (e) => {
    const sortBtn = e.target.closest('[data-sort]');
    if (sortBtn && state.plan) { state.sort = sortBtn.dataset.sort; $('list').innerHTML = renderList(state.plan); return; }
    const show = e.target.closest('[data-show]');
    if (show) { e.preventDefault(); showOnMap(show.dataset.show); return; }
    const dot = e.target.closest('.dot');
    if (dot) { showOnMap(dot.dataset.id); return; }
    const altBtn = e.target.closest('[data-alt]');
    if (altBtn) { run(+altBtn.dataset.alt); return; }
    if (e.target.closest('#btn-here')) {
      useLocation(() => {
        $('salida').value = '';
        status('Origen cambiado a tu ubicación. Ajusta el nivel del depósito y pulsa Buscar mi parada.');
        $('nivel').scrollIntoView({ behavior: 'smooth', block: 'center' });
      });
    }
  });
}

if (typeof document !== 'undefined') init();
