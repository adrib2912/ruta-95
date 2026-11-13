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

const norm = (s) => String(s).toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '').trim();

const state = { fuel: 'g95', origin: null, dest: null, stops: [], stopPlaces: [], discounts: {}, stations: null, places: null, recents: [],
  routes: null, alt: 0, plan: null, sort: 'score', map: null, rmap: null, mapDirty: true, markers: new Map(),
  car: { type: 'com', color: '#1F5FBF' }, frac: 0.25, detour: 'short', carDone: false, editing: false, q: 0, panel: 0, maxPanel: 0, stationsP: null };

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
  first.sort((a, b) => est(b) - est(a));
  for (const c of first) c.early = c.km / D * route.durMin < 60;
  const late = first.filter((c) => !c.early);
  // Si prefiere no parar en la primera hora, se priorizan las posteriores y se guardan unas pocas tempranas para comparar
  P.first = car.noEarly && late.length && !P.outOfReach ? [...late.slice(0, SHORTLIST - 6), ...first.filter((c) => c.early).slice(0, 6)] : first.slice(0, SHORTLIST);
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
  P.earlyBest = null;
  if (P.car.noEarly && singles.some((pl) => !pl.stops[0].early)) {
    P.earlyBest = singles.find((pl) => pl.stops[0].early) || null;
    singles = singles.filter((pl) => !pl.stops[0].early);
  }
  P.detourRelaxed = false;
  if (Number.isFinite(P.car.maxDetour) && singles.length) {
    const ok = singles.filter((pl) => pl.detMin <= P.car.maxDetour);
    if (ok.length) singles = ok; else P.detourRelaxed = true;
  }
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
  // Municipios con gasolinera: sirven para predecir al escribir sin esperar al buscador en línea
  const idx = new Map();
  for (const st of snap.e) {
    let name = st[6] || nice(st[5] || '');
    if (!name) continue;
    const m = name.match(/^(.*)\s\((.+)\)$/);
    if (m) name = m[2] + ' ' + m[1];
    const key = norm(name) + '|' + st[7];
    let e = idx.get(key);
    if (!e) idx.set(key, (e = { name, sub: nice(st[7] || ''), lats: [], lons: [] }));
    e.lats.push(st[1]); e.lons.push(st[2]);
  }
  state.places = [...idx.values()].map((e) => ({ name: e.name, sub: e.sub, lat: median(e.lats), lon: median(e.lons), n: e.lats.length, k: norm(e.name) }));
  const src = snap.live ? 'descargados ahora del Ministerio' : ageH < 1 ? 'copia de hace menos de 1 h' : `copia de hace ${fmt(ageH, 0)} h`;
  $('data-date').textContent = `Precios del ${snap.fecha} (${src}) · ${fmt(snap.e.length, 0)} estaciones`;
}

const geoCache = new Map();
async function geocode(q, limit = 5) {
  const ck = norm(q) + '|' + limit;
  if (geoCache.has(ck)) return geoCache.get(ck);
  const r = await geocodeRemote(q, limit);
  if (r.length) geoCache.set(ck, r);
  return r;
}
async function geocodeRemote(q, limit) {
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

async function fetchRoute(points, avoidTolls = false) {
  let j;
  const q = (ex) => `/route/v1/driving/${points.map((p) => p.lon.toFixed(5) + ',' + p.lat.toFixed(5)).join(';')}?overview=full&geometries=geojson&steps=true${points.length === 2 ? '&alternatives=3' : ''}${ex ? '&exclude=toll' : ''}`;
  try {
    if (avoidTolls) { try { j = await osrm(q(true)); } catch (_) { j = null; } }
    if (!j) j = await osrm(q(false));
  } catch (e) {
    throw new Error(e && e.message === 'NoRoute' ? 'No encuentro una ruta en coche entre esos puntos.' : 'El servicio de rutas no responde. Prueba otra vez en un momento.');
  }
  return j.routes.slice(0, 3).map((r) => {
    const route = buildRoute(r.geometry.coordinates, r.distance / 1000, r.duration / 60);
    let acc = 0;
    route.stopKm = (r.legs || []).slice(0, -1).map((l) => (acc += l.distance / 1000));
    const refs = new Map();
    for (const l of r.legs || []) for (const st of l.steps || []) for (const ref of String(st.ref || '').split(';')) {
      const t = ref.trim();
      if (/^[A-Z]{1,3}-?\d+/.test(t)) refs.set(t, (refs.get(t) || 0) + st.distance);
    }
    const main = [...refs].filter(([, d]) => d > r.distance * 0.08).sort((x, y) => y[1] - x[1]).slice(0, 3).map((x) => x[0]);
    route.tollKm = 0;
    const tolls = new Set();
    for (const l of r.legs || []) for (const st of l.steps || []) {
      if ((st.intersections || []).some((x) => (x.classes || []).includes('toll'))) {
        route.tollKm += st.distance / 1000;
        const t = String(st.ref || '').split(';')[0].trim();
        if (t) tolls.add(t);
      }
    }
    route.tollRefs = [...tolls].slice(0, 3);
    route.name = main.length ? [...refs.keys()].filter((k) => main.includes(k)).join(' · ')
      : [...new Set((r.legs || []).flatMap((l) => String(l.summary || '').split(',').map((t) => t.trim()).filter(Boolean)))].slice(0, 2).join(', ');
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

/* ---------- Interfaz: coche y preguntas ---------- */
/* Cada carrocería se describe con su perfil lateral en metros; de ahí salen el dibujo 2D y el modelo 3D. */
const CAR_TYPES = [
  { k: 'urb', n: 'Urbano', len: 3.4, w: 1.62, gc: 0.24, belt: 0.86, roof: 1.5, wind: 0.95, rf: 0.45, rr: -1.4, rear: -1.62, nose: 0.72, r: 0.29, cons: 5.0, tank: 35 },
  { k: 'com', n: 'Compacto', len: 4.1, w: 1.78, gc: 0.22, belt: 0.82, roof: 1.42, wind: 1.0, rf: 0.35, rr: -1.45, rear: -1.95, nose: 0.66, r: 0.31, cons: 5.8, tank: 45 },
  { k: 'ber', n: 'Berlina', len: 4.7, w: 1.82, gc: 0.2, belt: 0.8, roof: 1.38, wind: 1.05, rf: 0.3, rr: -0.95, rear: -1.7, nose: 0.64, r: 0.32, cons: 6.2, tank: 55 },
  { k: 'suv', n: 'SUV', len: 4.5, w: 1.88, gc: 0.34, belt: 1.02, roof: 1.68, wind: 1.1, rf: 0.5, rr: -1.8, rear: -2.12, nose: 0.92, r: 0.38, cons: 7.2, tank: 58 },
  { k: 'fur', n: 'Furgoneta', len: 4.9, w: 1.95, gc: 0.26, belt: 1.05, roof: 1.95, wind: 1.95, rf: 1.4, rr: -2.3, rear: -2.4, nose: 0.9, r: 0.34, cons: 8.0, tank: 70 },
  { k: 'dep', n: 'Deportivo', len: 4.4, w: 1.86, gc: 0.17, belt: 0.68, roof: 1.17, wind: 0.75, rf: -0.05, rr: -0.85, rear: -1.85, nose: 0.5, r: 0.34, cons: 8.5, tank: 55 },
];
const CAR_COLORS = ['#F2F2F2', '#22262B', '#8A9199', '#D5202A', '#1F5FBF', '#2E7D4F', '#F2B705', '#18A0A8'];
const THRESHOLDS = [{ f: 0.12, n: 'En reserva', d: 'Apuro el depósito' }, { f: 0.25, n: 'A un cuarto', d: 'Lo habitual' }, { f: 1 / 3, n: 'A un tercio', d: 'Con margen' }, { f: 0.5, n: 'A medio depósito', d: 'No me la juego' }];
const DETOURS = [
  { k: 'road', n: 'Solo a pie de carretera', d: 'Sin salir de mi ruta', corridor: 1.2, max: 2.5 },
  { k: 'short', n: 'Un desvío corto', d: 'Hasta unos 6 minutos', corridor: 4, max: 6 },
  { k: 'any', n: 'Lo que haga falta', d: 'Si el ahorro lo compensa', corridor: 8, max: Infinity },
];
const QS = ['coche', 'fuel', 'nums', 'umbral', 'desvio', 'nivel'];
const PUMP_SVG = '<svg viewBox="0 0 24 30" aria-hidden="true"><rect x="3" y="3" width="13" height="24" rx="2" fill="var(--red)"/><rect x="5.5" y="6" width="8" height="7" rx="1" fill="#fff"/><rect x="1" y="26" width="17" height="3" rx="1" fill="var(--ink)"/><path d="M16 12h2.5q2 0 2 2v8q0 1.5 1.2 1.5T23 22V11l-3-3" fill="none" stroke="var(--ink)" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"/></svg>';
const FLAG_SVG = '<svg viewBox="0 0 20 26" aria-hidden="true"><path d="M4 2v23" stroke="var(--ink)" stroke-width="2" stroke-linecap="round"/><path d="M5 3h12l-3 4 3 4H5z" fill="var(--ink)"/></svg>';
const carType = () => CAR_TYPES.find((c) => c.k === state.car.type) || CAR_TYPES[1];
const bodyPts = (t) => { const h = t.len / 2; return [[-h + 0.06, t.gc], [-h, t.gc + 0.2], [-h + 0.05, t.belt - (t.rear > -h + 0.4 ? 0.05 : 0)], [t.rear, t.belt], [t.wind, t.belt], [h - 0.14, t.nose], [h, t.nose - 0.2], [h - 0.04, t.gc]]; };
const cabinPts = (t) => [[t.rear, t.belt], [t.rr, t.roof], [t.rf, t.roof], [t.wind, t.belt]];
function carSVG() {
  const t = carType(), S = 22, X = (x) => (62 + x * S).toFixed(1), Y = (y) => (45 - y * S).toFixed(1);
  const path = (pts) => 'M' + pts.map((p) => X(p[0]) + ' ' + Y(p[1])).join('L') + 'Z';
  const wx = t.len / 2 - 0.82, wheel = (x) => `<circle cx="${X(x)}" cy="${Y(t.r)}" r="${(t.r * S).toFixed(1)}" fill="var(--ink)"/><circle cx="${X(x)}" cy="${Y(t.r)}" r="${(t.r * S * 0.42).toFixed(1)}" fill="#C9CED4"/>`;
  return `<svg viewBox="0 0 124 48" aria-hidden="true"><path d="${path(cabinPts(t))}" fill="#CFE3F5" stroke="var(--ink)" stroke-width="2" stroke-linejoin="round"/><path d="${path(bodyPts(t))}" fill="${state.car.color}" stroke="var(--ink)" stroke-width="2" stroke-linejoin="round"/>${wheel(-wx)}${wheel(wx)}</svg>`;
}

/* Modelo 3D: el perfil lateral extruido a lo ancho, con cabina de cristal, techo, ruedas y luces. */
const car3d = { ok: false, tried: false, renderer: null, scene: null, cam: null, group: null, paint: null, raf: 0, rot: -0.65, vel: 0.006, drag: null };
function init3D() {
  if (car3d.tried) return car3d.ok;
  car3d.tried = true;
  const cv = $('car3d');
  if (!window.THREE || !cv) return false;
  try {
    const T = window.THREE;
    const renderer = new T.WebGLRenderer({ canvas: cv, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1));
    const scene = new T.Scene();
    const cam = new T.PerspectiveCamera(30, 2, 0.1, 60);
    cam.position.set(0, 2.5, 9.4); cam.lookAt(0, 0.75, 0);
    scene.add(new T.HemisphereLight(0xffffff, 0x8a96a3, 1.05));
    const sun = new T.DirectionalLight(0xffffff, 0.95); sun.position.set(4, 7, 5); scene.add(sun);
    const cnv = document.createElement('canvas'); cnv.width = cnv.height = 128;
    const g = cnv.getContext('2d'), gr = g.createRadialGradient(64, 64, 4, 64, 64, 62);
    gr.addColorStop(0, 'rgba(0,0,0,.42)'); gr.addColorStop(1, 'rgba(0,0,0,0)');
    g.fillStyle = gr; g.fillRect(0, 0, 128, 128);
    const shadow = new T.Mesh(new T.PlaneGeometry(7.4, 4.2), new T.MeshBasicMaterial({ map: new T.CanvasTexture(cnv), transparent: true, depthWrite: false }));
    shadow.rotation.x = -Math.PI / 2; shadow.position.y = 0.01; scene.add(shadow);
    Object.assign(car3d, { renderer, scene, cam, ok: true });
    cv.addEventListener('pointerdown', (e) => { car3d.drag = e.clientX; cv.setPointerCapture(e.pointerId); });
    cv.addEventListener('pointermove', (e) => { if (car3d.drag == null) return; car3d.rot += (e.clientX - car3d.drag) * 0.012; car3d.drag = e.clientX; });
    const end = () => { car3d.drag = null; };
    cv.addEventListener('pointerup', end); cv.addEventListener('pointercancel', end);
    build3D();
  } catch (_) { car3d.ok = false; }
  return car3d.ok;
}
function build3D() {
  if (!car3d.ok) return;
  const T = window.THREE, t = carType();
  if (car3d.group) car3d.scene.remove(car3d.group);
  const grp = new T.Group();
  const extr = (pts, width, bevel, mat) => {
    const sh = new T.Shape(); pts.forEach((p, i) => (i ? sh.lineTo(p[0], p[1]) : sh.moveTo(p[0], p[1])));
    const geo = new T.ExtrudeGeometry(sh, { depth: width - 2 * bevel, bevelEnabled: bevel > 0, bevelThickness: bevel, bevelSize: bevel, bevelSegments: 3, steps: 1 });
    geo.translate(0, 0, -(width - 2 * bevel) / 2);
    const m = new T.Mesh(geo, mat); grp.add(m); return m;
  };
  car3d.paint = new T.MeshStandardMaterial({ color: state.car.color, metalness: 0.35, roughness: 0.42 });
  const glass = new T.MeshStandardMaterial({ color: 0x1b2836, metalness: 0.7, roughness: 0.12 });
  const dark = new T.MeshStandardMaterial({ color: 0x15181c, roughness: 0.85 });
  const hub = new T.MeshStandardMaterial({ color: 0xc9ced4, metalness: 0.6, roughness: 0.35 });
  extr(bodyPts(t), t.w, 0.07, car3d.paint);
  extr(cabinPts(t), t.w * 0.86, 0.03, glass);
  extr([[t.rr - 0.04, t.roof - 0.03], [t.rr - 0.02, t.roof + 0.05], [t.rf + 0.02, t.roof + 0.05], [t.rf + 0.04, t.roof - 0.03]], t.w * 0.88, 0.02, car3d.paint);
  // pilares: una franja de carrocería en el centro de la cabina
  const mid = (t.rr + t.rf) / 2;
  extr([[mid - 0.05, t.belt], [mid - 0.05, t.roof], [mid + 0.05, t.roof], [mid + 0.05, t.belt]], t.w * 0.875, 0.01, car3d.paint);
  const wx = t.len / 2 - 0.82;
  for (const sx of [-1, 1]) for (const sz of [-1, 1]) {
    const w = new T.Mesh(new T.CylinderGeometry(t.r, t.r, 0.26, 28), dark);
    w.rotation.x = Math.PI / 2; w.position.set(sx * wx, t.r, sz * (t.w / 2 - 0.1)); grp.add(w);
    const h = new T.Mesh(new T.CylinderGeometry(t.r * 0.55, t.r * 0.55, 0.275, 20), hub);
    h.rotation.x = Math.PI / 2; h.position.copy(w.position); grp.add(h);
  }
  const lamp = (x, y, color) => { for (const sz of [-1, 1]) { const m = new T.Mesh(new T.BoxGeometry(0.07, 0.13, 0.36), new T.MeshStandardMaterial({ color, emissive: color, emissiveIntensity: 0.7 })); m.position.set(x, y, sz * t.w * 0.3); grp.add(m); } };
  lamp(t.len / 2 - 0.03, t.nose - 0.16, 0xfff2c4);
  lamp(-t.len / 2 + 0.01, t.belt - 0.16, 0xd5202a);
  grp.scale.setScalar(4.6 / Math.max(4.6, t.len));
  car3d.group = grp; car3d.scene.add(grp);
}
function loop3D() {
  if (!car3d.ok) return;
  const cv = $('car3d'), w = cv.clientWidth, h = cv.clientHeight;
  if (w && h) {
    if (cv.width !== Math.round(w * car3d.renderer.getPixelRatio())) { car3d.renderer.setSize(w, h, false); car3d.cam.aspect = w / h; car3d.cam.updateProjectionMatrix(); }
    if (car3d.drag == null && !matchMedia('(prefers-reduced-motion: reduce)').matches) car3d.rot += car3d.vel;
    car3d.group.rotation.y = car3d.rot;
    car3d.renderer.render(car3d.scene, car3d.cam);
  }
  car3d.raf = requestAnimationFrame(loop3D);
}
function start3D() {
  const ok = init3D();
  $('car3d').hidden = !ok; $('car-flat').hidden = ok; $('car-hint').hidden = !ok;
  cancelAnimationFrame(car3d.raf);
  if (ok) loop3D();
}
const stop3D = () => cancelAnimationFrame(car3d.raf);

function paintCar() {
  document.querySelectorAll('.veh').forEach((el) => { el.innerHTML = carSVG(); });
  document.querySelectorAll('.pump:empty').forEach((el) => { el.innerHTML = PUMP_SVG; });
  $('car-types').innerHTML = CAR_TYPES.map((t) => `<button type="button" class="chip" role="radio" aria-checked="${t.k === state.car.type}" data-type="${t.k}">${t.n}</button>`).join('');
  $('car-colors').innerHTML = CAR_COLORS.map((c) => `<button type="button" role="radio" aria-checked="${c === state.car.color}" aria-label="Color ${c}" data-color="${c}" style="background:${c}"></button>`).join('');
}

function readCar() {
  const v = (id, def) => { const n = parseFloat(String($(id).value).replace(',', '.')); return Number.isFinite(n) ? n : def; };
  const tank = Math.max(5, v('deposito', 45));
  const cons = Math.max(1, v('consumo', 5.8));
  const det = DETOURS.find((d) => d.k === state.detour) || DETOURS[1];
  return {
    cons, tank, consSafe: cons * (1 + Math.min(50, Math.max(0, v('margen', 10))) / 100),
    fuelNow: tank * v('nivel', 50) / 100,
    reserve: tank * state.frac,
    corridor: det.corridor, maxDetour: det.max,
    timeValue: Math.max(0, v('tiempo', 6)),
    noEarly: $('temprano').checked,
  };
}
function readDepart() {
  const v = $('salida').value;
  const d = v ? new Date(v) : new Date();
  return Number.isNaN(d.getTime()) ? new Date() : d;
}
const tile = (attr, val, on, title, sub) => `<button type="button" class="tile" role="radio" aria-checked="${on}" ${attr}="${val}"><b>${title}</b>${sub ? `<small>${sub}</small>` : ''}</button>`;
function updateGauge() {
  const car = readCar(), t = carType();
  const pct = Math.max(0.05, Math.min(1, car.fuelNow / car.tank));
  const km = Math.max(0, (car.fuelNow - car.reserve) / car.consSafe * 100);
  const LEN = 251.3, ang = -90 + pct * 180, ta = (-180 + state.frac * 180) * Math.PI / 180;
  $('dial').innerHTML = `<svg viewBox="0 0 200 122" role="img" aria-label="Depósito al ${fmt(pct * 100, 0)} por ciento">
    <path d="M20 104A80 80 0 0 1 180 104" fill="none" stroke="var(--line)" stroke-width="14" stroke-linecap="round"/>
    <path d="M20 104A80 80 0 0 1 180 104" fill="none" stroke="${car.fuelNow <= car.reserve ? 'var(--red)' : 'var(--blue)'}" stroke-width="14" stroke-linecap="round" stroke-dasharray="${(LEN * pct).toFixed(1)} ${LEN}"/>
    <line x1="${(100 + 66 * Math.cos(ta)).toFixed(1)}" y1="${(104 + 66 * Math.sin(ta)).toFixed(1)}" x2="${(100 + 94 * Math.cos(ta)).toFixed(1)}" y2="${(104 + 94 * Math.sin(ta)).toFixed(1)}" stroke="var(--red)" stroke-width="3" stroke-linecap="round"/>
    <g transform="rotate(${ang.toFixed(1)} 100 104)"><path d="M100 104V40" stroke="var(--ink)" stroke-width="4" stroke-linecap="round"/></g><circle cx="100" cy="104" r="7" fill="var(--ink)"/>
    <text x="16" y="120" class="dl">R</text><text x="184" y="120" text-anchor="end" class="dl">Lleno</text></svg>`;
  $('nivel-out').textContent = `${fmt(car.fuelNow, 0)} L`;
  $('fuels').innerHTML = FUELS.map((f) => tile('data-k', f.k, f.k === state.fuel, f.n)).join('');
  $('umbral').innerHTML = THRESHOLDS.map((x) => tile('data-f', x.f, Math.abs(x.f - state.frac) < 0.01, x.n, `${x.d} · unos ${fmt(car.tank * x.f, 0)} L`)).join('');
  $('desvio').innerHTML = DETOURS.map((d) => tile('data-d', d.k, d.k === state.detour, d.n, d.d)).join('');
  $('tipico').innerHTML = `Lo normal en un ${t.k === 'suv' ? 'SUV' : t.n.toLowerCase()}: ${fmt(t.cons, 1)} L/100 km y ${t.tank} L. <button type="button" class="linkbtn inline" id="btn-tipico">Usar estos</button>`;
  $('umbral-out').textContent = car.fuelNow <= car.reserve
    ? `Ya estás por debajo de tu límite (${fmt(car.reserve, 0)} L, la marca roja): te buscaré la primera gasolinera que encuentres.`
    : `Tienes unos ${fmt(km, 0)} km antes de bajar de tu límite (${fmt(car.reserve, 0)} L, la marca roja).`;
  const fuelName = FUELS.find((f) => f.k === state.fuel).n, thr = THRESHOLDS.find((x) => Math.abs(x.f - state.frac) < 0.01) || THRESHOLDS[0], det = DETOURS.find((d) => d.k === state.detour) || DETOURS[1];
  $('car-sum').textContent = `${t.n} · ${fuelName} · ${fmt(car.cons, 1)} L/100 km · ${fmt(car.tank, 0)} L · reposto ${thr.n.toLowerCase()} · ${det.n.toLowerCase()}`;
}
function showQ(i, dir = 1) {
  state.q = i;
  document.querySelectorAll('#deck .qcard').forEach((c) => {
    const on = c.dataset.q === QS[i];
    c.hidden = !on;
    if (on) { c.classList.remove('in-f', 'in-b'); void c.offsetWidth; c.classList.add(dir >= 0 ? 'in-f' : 'in-b'); }
  });
  $('dots').innerHTML = QS.map((q, k) => `<i class="${k === i ? 'on' : k < i ? 'done' : ''}"></i>`).join('');
  $('btn-next').textContent = i < QS.length - 1 ? 'Siguiente' : 'Buscar mi parada';
  $('btn-editcar').hidden = !(state.carDone && !state.editing);
  if (QS[i] === 'coche') start3D(); else stop3D();
  updateGauge();
  window.scrollTo({ top: 0, behavior: 'auto' });
}

const FIELDS = ['consumo', 'deposito', 'nivel', 'tiempo', 'margen'];
function save() {
  try {
    localStorage.setItem('ruta95', JSON.stringify({
      fuel: state.fuel, ...Object.fromEntries(FIELDS.map((k) => [k, $(k).value])),
      discounts: state.discounts, skin: document.documentElement.dataset.skin || '',
      car: state.car, frac: state.frac, detour: state.detour, carDone: state.carDone,
      avoidTolls: $('peajes').checked, noEarly: $('temprano').checked, recents: state.recents,
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
    if (d.car && CAR_COLORS.includes(d.car.color)) state.car = { type: CAR_TYPES.some((t) => t.k === d.car.type) ? d.car.type : 'com', color: d.car.color };
    if (THRESHOLDS.some((t) => Math.abs(t.f - d.frac) < 0.01)) state.frac = d.frac;
    if (DETOURS.some((x) => x.k === d.detour)) state.detour = d.detour;
    state.carDone = !!d.carDone;
    $('peajes').checked = !!d.avoidTolls; $('temprano').checked = !!d.noEarly;
    if (Array.isArray(d.recents)) state.recents = d.recents.slice(0, 5);
    if (d.origin) { state.origin = d.origin; $('origen').value = d.origin.name; }
    if (d.dest) { state.dest = d.dest; $('destino').value = d.dest.name; }
    if (Array.isArray(d.stops)) state.stops = d.stops.slice(0, MAX_STOPS).map((pl) => ({ place: pl, text: pl.name }));
  } catch (_) { /* sin almacenamiento */ }
}
function renderDiscounts() {
  $('discounts').innerHTML = BRANDS.map((b) => `<div class="numfield"><label for="d-${b.k}">${b.n}</label>
    <div class="unit"><input id="d-${b.k}" data-brand="${b.k}" type="number" inputmode="decimal" step="1" min="0" max="50" value="${state.discounts[b.k] || ''}" placeholder="0"><span>cts/L</span></div></div>`).join('');
}

/* ---------- Interfaz: buscador de lugares ---------- */
/* Tres fuentes, de más rápida a más lenta: tus lugares recientes, los municipios con gasolinera
   (ya en memoria, respuesta instantánea) y el buscador en línea para direcciones. */
function localSuggest(q) {
  const k = norm(q);
  if (k.length < 2 || !state.places) return [];
  const a = [], b = [];
  for (const p of state.places) { if (p.k.startsWith(k)) a.push(p); else if (p.k.includes(' ' + k)) b.push(p); }
  const byN = (x, y) => y.n - x.n;
  return [...a.sort(byN), ...b.sort(byN)].slice(0, 4);
}
function setupPlace(input, list, onSet) {
  let timer = 0, seq = 0, items = [];
  const close = () => { list.hidden = true; list.innerHTML = ''; };
  const show = (arr) => {
    items = arr;
    list.innerHTML = arr.map((it, i) => `<li data-i="${i}">${esc(it.name)}<small>${esc(it.tag || it.sub || '')}</small></li>`).join('');
    list.hidden = !arr.length;
  };
  const pick = (it) => {
    const pl = { name: it.name, sub: it.sub || '', lat: it.lat, lon: it.lon };
    onSet(pl, pl.name); input.value = pl.name; close();
    state.recents = [pl, ...state.recents.filter((r) => norm(r.name) !== norm(pl.name))].slice(0, 5);
    save();
  };
  const recents = () => state.recents.map((r) => ({ ...r, tag: 'Reciente' }));
  const refresh = () => {
    onSet(null, input.value);
    clearTimeout(timer);
    const q = input.value.trim();
    if (!q) return show(recents());
    const kq = norm(q);
    const local = [...recents().filter((r) => norm(r.name).startsWith(kq)), ...localSuggest(q)];
    const dedupe = (arr) => { const seen = new Set(); return arr.filter((it) => { const k = norm(it.name) + '|' + norm(it.sub || '').slice(0, 6); if (seen.has(norm(it.name)) && !it.sub) return false; if (seen.has(k)) return false; seen.add(k); seen.add(norm(it.name)); return true; }); };
    show(dedupe(local).slice(0, 5));
    if (q.length < 3) return;
    const my = ++seq;
    timer = setTimeout(async () => {
      try {
        const r = await geocode(q);
        if (my !== seq || document.activeElement !== input) return;
        const have = new Set(local.map((it) => norm(it.name)));
        show(dedupe([...local, ...r.filter((it) => !have.has(norm(it.name)))]).slice(0, 6));
      } catch (_) { /* nos quedamos con las sugerencias locales */ }
    }, 220);
  };
  input.addEventListener('input', refresh);
  input.addEventListener('focus', () => { if (!input.value.trim()) show(recents()); });
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
        <input id="stop-${i}" type="text" placeholder="Ciudad o dirección" inputmode="search" autocomplete="off" value="${esc(st.text || '')}">
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
  const loc = localSuggest(q)[0];
  if (loc && loc.k === norm(q)) return { name: loc.name, sub: loc.sub, lat: loc.lat, lon: loc.lon };
  const r = await geocode(q, 1);
  if (r.length) return r[0];
  if (loc) return { name: loc.name, sub: loc.sub, lat: loc.lat, lon: loc.lon };
  throw new Error(`No encuentro "${q}". Prueba con el nombre del municipio.`);
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
function whenLabel() {
  const v = $('salida').value, d = v ? new Date(v) : null;
  if (!d || Number.isNaN(d.getTime())) return '';
  return d.toLocaleString('es-ES', { weekday: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit' });
}
function updateWhen() {
  const l = whenLabel();
  $('btn-when').textContent = l ? `Salgo el ${l} · cambiar` : 'Salgo ahora · cambiar';
}

/* ---------- Utilidades de resultado ---------- */
const gmaps = (cands) => {
  const o = state.origin, d = state.dest, ll = (p) => p.lat.toFixed(5) + ',' + p.lon.toFixed(5);
  const route = state.routes[state.alt];
  const via = state.stopPlaces.map((p, i) => ({ p, km: route.stopKm[i] || 0 }));
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
const dur = (m) => `${Math.floor(m / 60) ? Math.floor(m / 60) + ' h ' : ''}${Math.round(m % 60)} min`;
const priceTxt = (c) => `${fmt(c.price, 3)} €/L${c.disc ? ` (con tu descuento de ${fmt(c.disc, 0)} cts)` : ''}`;
const tollTxt = (r) => (r.tollKm >= 1 ? `Peaje: unos ${fmt(r.tollKm, 0)} km${r.tollRefs.length ? ' (' + r.tollRefs.join(', ') + ')' : ''}` : 'Sin peajes');
const isDark = () => {
  const skin = document.documentElement.dataset.skin;
  return skin === 'asfalto' || (!skin && matchMedia('(prefers-color-scheme: dark)').matches);
};
const smooth = () => (matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth');
function baseMap(id) {
  const map = L.map(id, { zoomControl: true, attributionControl: true, scrollWheelZoom: false });
  map.attributionControl.setPrefix(false);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19, attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>', className: isDark() ? 'tiles-dark' : '',
  }).addTo(map);
  return map;
}
const endDot = (map, p, t) => L.circleMarker([p.lat, p.lon], { radius: 6, color: '#fff', weight: 2, fillColor: '#10202E', fillOpacity: 1 }).addTo(map).bindTooltip(t);

/* ---------- Panel 2: elegir el camino en el mapa ---------- */
function renderRoutes() {
  const routes = state.routes;
  if (!routes || !window.L) return;
  if (state.rmap) { state.rmap.remove(); state.rmap = null; }
  const map = baseMap('rmap');
  const accent = isDark() ? getComputedStyle(document.documentElement).getPropertyValue('--blue').trim() || '#6AAEF7' : '#0B4EA2';
  let bounds = null;
  // La elegida se dibuja la última para que quede encima
  routes.map((r, i) => i).sort((a, b) => (a === state.alt) - (b === state.alt)).forEach((i) => {
    const sel = i === state.alt;
    const line = L.polyline(routes[i].coords.map((c) => [c[1], c[0]]), { color: sel ? accent : '#7C8894', weight: sel ? 6 : 4, opacity: sel ? 0.95 : 0.7 }).addTo(map);
    line.on('click', () => { state.alt = i; renderRoutes(); });
    bounds = bounds ? bounds.extend(line.getBounds()) : line.getBounds();
  });
  endDot(map, state.origin, 'Salida'); endDot(map, state.dest, 'Destino');
  for (const p of state.stopPlaces) L.circleMarker([p.lat, p.lon], { radius: 5, color: '#10202E', weight: 2, fillColor: '#fff', fillOpacity: 1 }).addTo(map).bindTooltip(p.name);
  map.fitBounds(bounds, { padding: [24, 24] });
  state.rmap = map;
  $('alts').innerHTML = routes.map((r, i) => `<button type="button" role="radio" data-alt="${i}" aria-checked="${i === state.alt}">
      <b>${esc(r.name || 'Ruta ' + (i + 1))}</b><small>${fmt(r.distKm, 0)} km · unas ${dur(r.durMin)}</small><small class="${r.tollKm >= 1 ? 'toll' : ''}">${tollTxt(r)}</small></button>`).join('');
}

/* ---------- Panel 4: resultado ---------- */
function renderStrip(P) {
  const pct = (km) => Math.max(0, Math.min(100, km / P.D * 100));
  const stops = P.chosen.stops;
  return `<div class="strip card">
    <div class="road"><div class="track">
      <i class="reach" style="width:${pct(P.reachKm)}%"></i>
      ${stops.map((c) => `<span class="pump" style="left:${pct(c.km)}%">${PUMP_SVG}</span>`).join('')}
      <span class="flag">${FLAG_SVG}</span>
      <span class="veh drive" style="--to:${pct(stops[0].km)}%">${carSVG()}</span>
    </div></div>
    <div class="strip-l"><span>${esc(state.origin.name)}</span><span>${stops.map((c) => 'km ' + fmt(c.km, 0)).join(' · ')}</span><span>${esc(state.dest.name)}</span></div>
  </div>`;
}

function renderChart(P) {
  const W = 340, H = 170, L = 36, R = 10, T = 12, B = 24;
  const all = P.cands;
  if (!all.length) return '';
  const nb = Math.max(6, Math.min(40, Math.round(P.D / 10)));
  const bw = P.D / nb, band = [];
  for (const c of all) { const i = Math.min(nb - 1, Math.floor(c.km / bw)); if (band[i] == null || c.price < band[i]) band[i] = c.price; }
  const pts = [];
  band.forEach((p, i) => { if (p != null) pts.push({ km: (i + 0.5) * bw, p }); });
  const chosen = new Set(P.chosen ? P.chosen.stops : []);
  const vals = [...pts.map((q) => q.p), ...P.short.map((c) => c.price), P.ref].filter(Boolean);
  const lo = Math.min(...vals), hi = Math.max(...vals), pad = Math.max(0.02, (hi - lo) * 0.1);
  const y0 = lo - pad, y1 = hi + pad;
  const x = (km) => L + (km / P.D) * (W - L - R);
  const y = (p) => T + (1 - (Math.min(y1, Math.max(y0, p)) - y0) / (y1 - y0)) * (H - T - B);
  const tip = (c) => `<title>${esc(stName(c))}, ${esc(stTown(c))}: ${fmt(c.price, 3)} €/L, km ${fmt(c.km, 0)}</title>`;
  let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Precio más barato en cada tramo de la ruta">`;
  s += `<rect x="${x(0)}" y="${T}" width="${(x(P.reachKm) - x(0)).toFixed(1)}" height="${H - T - B}" fill="var(--blue-soft)" rx="4"/>`;
  const ticks = [[hi, fmt(hi, 2)], [lo, fmt(lo, 2)]];
  if (P.ref && Math.abs(y(P.ref) - y(hi)) > 11 && Math.abs(y(P.ref) - y(lo)) > 11) ticks.push([P.ref, fmt(P.ref, 2)]);
  for (const [v, t] of ticks) s += `<line x1="${L}" x2="${W - R}" y1="${y(v)}" y2="${y(v)}" stroke="var(--line)" stroke-width=".7"/><text x="${L - 5}" y="${y(v) + 3}" text-anchor="end">${t}</text>`;
  if (P.ref) s += `<line x1="${L}" x2="${W - R}" y1="${y(P.ref)}" y2="${y(P.ref)}" stroke="var(--muted)" stroke-dasharray="3 3"/>`;
  s += `<line x1="${L}" x2="${W - R}" y1="${H - B}" y2="${H - B}" stroke="var(--muted)"/>`;
  const step = P.D > 600 ? 200 : P.D > 250 ? 100 : P.D > 100 ? 50 : P.D > 40 ? 20 : 10;
  for (let k = 0; k <= P.D; k += step) s += `<line x1="${x(k)}" x2="${x(k)}" y1="${H - B}" y2="${H - B + 4}" stroke="var(--muted)"/><text x="${x(k)}" y="${H - 6}" text-anchor="middle">${k === 0 ? 'km 0' : k}</text>`;
  if (pts.length > 1) s += `<polyline fill="none" stroke="var(--muted)" stroke-width="1.6" stroke-linejoin="round" points="${pts.map((q) => x(q.km).toFixed(1) + ',' + y(q.p).toFixed(1)).join(' ')}"/>`;
  for (const c of P.short) if (!chosen.has(c)) s += `<circle class="dot" data-id="${esc(c.id)}" cx="${x(c.km).toFixed(1)}" cy="${y(c.price).toFixed(1)}" r="3.6" fill="var(--blue)" stroke="var(--surface)" stroke-width="1">${tip(c)}</circle>`;
  for (const c of chosen) s += `<line x1="${x(c.km)}" x2="${x(c.km)}" y1="${y(c.price)}" y2="${H - B}" stroke="var(--red)" stroke-width="1.5"/><circle class="dot" data-id="${esc(c.id)}" cx="${x(c.km)}" cy="${y(c.price)}" r="6" fill="var(--red)" stroke="var(--surface)" stroke-width="2">${tip(c)}</circle>`;
  s += '</svg>';
  return `<section class="card chart"><h3>Precio a lo largo de tu ruta (€/L)</h3>${s}
    <div class="legend"><span><i style="background:var(--red)"></i>Tu parada</span><span><i style="background:var(--blue)"></i>Candidatas: tócalas</span><span><i class="ln"></i>Lo más barato de cada tramo</span><span>Fondo: hasta donde llegas sin repostar</span></div>
    <p class="hint">La línea discontinua es el precio normal en gasolineras de ${P.refKind === 'carretera' ? 'carretera' : 'la ruta'}: ${fmt(P.ref, 3)} €/L.</p></section>`;
}

function renderList(P) {
  const all = P.singles;
  if (all.length < 2) return '<p class="hint">No hay más paradas que cumplan tus condiciones en esta ruta.</p>';
  const st = (pl) => pl.stops[0];
  const cheapest = all.reduce((a, c) => (st(c).price < st(a).price ? c : a));
  const measured = all.filter((c) => st(c).exact);
  const quick = (measured.length ? measured : all).reduce((a, c) => (st(c).detourMin < st(a).detourMin ? c : a));
  let items = [...all];
  if (state.sort === 'price') items.sort((a, b) => st(a).price - st(b).price || st(a).detourMin - st(b).detourMin);
  else if (state.sort === 'detour') items.sort((a, b) => st(a).detourMin - st(b).detourMin || st(a).price - st(b).price);
  const groups = new Map();
  for (const pl of items) {
    const c = st(pl), key = (stTown(c) || '?') + ':' + Math.round(c.km / 6);
    if (!groups.has(key)) groups.set(key, { pl, more: 0 }); else groups.get(key).more++;
  }
  const li = [...groups.values()].slice(0, 8).map(({ pl, more }) => {
    const c = st(pl);
    const tags = [P.chosen === pl ? '<span class="tag">Recomendada</span>' : '', pl === cheapest ? '<span class="tag">Más barata</span>' : '', pl === quick ? '<span class="tag">Menos desvío</span>' : ''].join('');
    const cls = pl.net > 0.005 ? 'pos' : pl.net < -0.005 ? 'negv' : '';
    return `<li>
      <div class="kmtag">km<b>${fmt(c.km, 0)}</b></div>
      <div class="st">${tags}<b>${esc(stName(c))}</b><small>${esc(stPlace(c))}</small><small>${fmt(c.price, 3)} €/L · ${approx(c)}${mins(c.detourMin)} · ${fmt(pl.litres, 0)}&nbsp;L${c.open === null && c.s[8] ? ' · horario sin confirmar' : ''}</small>
        ${more ? `<small class="more">y ${more} más en la zona</small>` : ''}</div>
      <div class="amt"><b class="${cls}">${pl.net >= 0 ? '+' : '−'}${fmt(Math.abs(pl.net), 2)} €</b><small>ahorro</small></div>
      <div class="acts"><a href="${gmaps([c])}" target="_blank" rel="noopener">Ir con esta parada</a><a href="#map" data-show="${esc(c.id)}">Ver en el mapa</a></div>
    </li>`;
  }).join('');
  const btn = (k, t) => `<button type="button" data-sort="${k}" aria-pressed="${state.sort === k}">${t}</button>`;
  return `<section class="card"><div class="sorter">${btn('score', 'Mejor')}${btn('price', 'Más barata')}${btn('detour', 'Menos desvío')}</div><ul class="list">${li}</ul></section>`;
}

function renderStopBlock(leg, n, total) {
  const c = leg.s;
  const what = leg.full ? `Llena el depósito: <b>${fmt(leg.L, 0)} L</b>` : `Echa solo <b>${fmt(leg.L, 0)} L</b>, lo justo para llegar a la siguiente`;
  return `<div class="best-head">
      <div class="hito" aria-label="Kilómetro ${fmt(c.km, 0)} de tu ruta"><i>KM</i><b>${fmt(c.km, 0)}</b></div>
      <div class="best-id"><span class="eyebrow">${total > 1 ? `Parada ${n} de ${total} · ` : ''}Hacia las ${hhmm(c.eta)}</span><h2>${esc(stName(c))}</h2></div>
      <div class="price"><b>${fmt(c.price, 3)}</b><span>€/L${c.disc ? ' con descuento' : ''}</span></div>
      <div class="best-more">
        <p class="what">${what} · desvío de ${approx(c)}${fmt(c.detourKm, 1)} km, ${mins(c.detourMin)}</p>
        <p>${esc(stPlace(c))}${c.s[8] ? ' · ' + esc(c.s[8]) : ''}${c.open === null && c.s[8] ? ' (horario sin confirmar)' : ''}</p>
      </div>
    </div>`;
}

function renderResult() {
  const P = state.plan, car = P.car, ch = P.chosen;
  const fuelName = FUELS.find((f) => f.k === state.fuel).n;
  $('loading').hidden = true;
  $('result').hidden = false;
  const trip = `<div class="trip"><span><b>${fmt(P.D, 0)} km</b></span><span>unas <b>${dur(P.route.durMin)}</b></span><span>Gastarás <b>${fmt(P.need, 1)} L</b></span><span>${tollTxt(P.route)}</span></div>`;
  if (!P.cands.length || !ch) {
    $('strip').innerHTML = ''; $('tabs').hidden = true;
    $('t-plan').innerHTML = trip + `<div class="note"><p>${P.closed && !P.cands.length ? `Las ${P.closed} gasolineras de esta ruta están cerradas a la hora a la que pasarías.` : `No hay gasolineras con ${esc(fuelName)} a menos de ${fmt(car.corridor, 0)} km de esta ruta. Amplía la búsqueda en los ajustes finos del coche.`}</p></div>`;
    showTab('plan'); return;
  }
  $('tabs').hidden = false;
  $('strip').innerHTML = renderStrip(P);
  const warns = [];
  if (P.outOfReach) warns.push(`Con lo que llevas no llegas a ninguna gasolinera de la ruta sin bajar de ${fmt(car.reserve, 0)} L. Reposta cuanto antes: estas son las primeras que encontrarás.`);
  if (P.incomplete && !P.outOfReach) warns.push('El viaje pide más de dos repostajes. Esta es la mejor primera parada; vuelve a calcular desde allí.');
  const n = ch.stops.length;
  const where = n > 1 ? `Para en los km ${ch.stops.map((c) => fmt(c.km, 0)).join(' y ')}` : `Para en el km ${fmt(ch.stops[0].km, 0)}`;
  const gain = ch.net > 0.005;
  let why;
  if (n > 1) why = 'Con un solo repostaje no llegas. ' + (ch.legs[0].full ? 'Llenas donde es más barato y completas después lo que falte.' : 'En la primera echas lo justo para alcanzar la segunda, que es más barata.');
  else if (ch.detMin < 0.5) why = 'Te pilla de camino: no pierdes tiempo.';
  else {
    const c = ch.stops[0], be = c.price < P.ref ? ch.detCost / (P.ref - c.price) : null;
    why = be != null && be < ch.litres ? `El desvío compensa a partir de ${fmt(Math.max(0.1, be), 1)} L, y vas a echar ${fmt(ch.litres, 0)}.` : 'Es la mejor combinación de precio y desvío en el tramo al que llegas.';
  }
  const infos = [];
  if (!P.mustRefuel) infos.push(`Llegarías sin repostar y sin bajar de ${fmt(car.reserve, 0)} L. Esta parada es por si quieres llenar barato.`);
  else infos.push(`Sin repostar bajarías de ${fmt(car.reserve, 0)} L hacia el km ${fmt(Math.min(P.D, P.rangeKm), 0)}.`);
  if (P.earlyBest && P.earlyBest.net > ch.net + 0.3) {
    const e = P.earlyBest.stops[0];
    infos.push(`Si no te importara parar en la primera hora, en el km ${fmt(e.km, 0)} (${esc(stName(e))}, ${esc(stTown(e))}) ahorrarías ${eur(P.earlyBest.net - ch.net)} más.`);
  } else if (P.car.noEarly && ch.stops[0].early) infos.push('No hay parada posible después de la primera hora, así que te propongo una antes.');
  if (P.detourRelaxed) infos.push('Ninguna parada cumple tu límite de desvío, así que te propongo la mejor de las que hay.');
  if (P.closed) infos.push(`${P.closed} ${P.closed === 1 ? 'gasolinera descartada porque estará cerrada' : 'gasolineras descartadas porque estarán cerradas'} cuando pases.`);
  $('t-plan').innerHTML = `${warns.length ? `<div class="note">${warns.map((w) => `<p>${w}</p>`).join('')}</div>` : ''}
    <article class="card best">
      <div class="verdict ${gain ? '' : 'zero'}"><span>${where}</span><b>${gain ? '' : '−'}<span class="count" data-to="${Math.abs(ch.net).toFixed(2)}">${eur(Math.abs(ch.net))}</span><small>${gain ? 'de ahorro' : 'de sobrecoste'}</small></b></div>
      ${ch.legs.map((l, i) => renderStopBlock(l, i + 1, n)).join('<hr class="sep">')}
      <p class="why">${why}</p>
      <a class="go" href="${gmaps(ch.stops)}" target="_blank" rel="noopener">Ir con ${n > 1 ? 'estas paradas' : 'esta parada'} en Google Maps</a>
      <details class="breakdown"><summary>Ver las cuentas</summary>
        <dl class="rows">
          <div><dt>Precio normal en gasolineras de ${P.refKind === 'carretera' ? 'carretera' : 'la ruta'}</dt><dd>${fmt(P.ref, 3)} €/L</dd></div>
          <div><dt>Litros que echarás</dt><dd>${fmt(ch.litres, 0)} L</dd></div>
          <div><dt>Ahorro por precio</dt><dd>${ch.gross >= 0 ? '' : '−'}${eur(Math.abs(ch.gross))}</dd></div>
          <div><dt>Gasolina del desvío (${mins(ch.detMin)})</dt><dd class="${ch.detCost >= 0.005 ? 'neg' : ''}">−${eur(ch.detCost)}</dd></div>
          <div class="total"><dt>${gain ? 'Ahorro' : 'Sobrecoste'}</dt><dd>${eur(Math.abs(ch.net))}</dd></div>
        </dl>
      </details>
    </article>
    ${trip}<div class="infos">${infos.map((t) => `<p>${t}</p>`).join('')}<button type="button" class="linkbtn" id="btn-here">Ya estoy en ruta: recalcular desde donde estoy</button></div>`;
  $('t-precios').innerHTML = renderChart(P);
  $('t-otras').innerHTML = renderList(P);
  state.mapDirty = true;
  showTab('plan');
  // El ahorro se cuenta hacia arriba al aparecer
  const el = document.querySelector('.count');
  if (el && !matchMedia('(prefers-reduced-motion: reduce)').matches) {
    const to = +el.dataset.to, t0 = performance.now();
    const tick = (now) => { const k = Math.min(1, (now - t0) / 800), e = 1 - Math.pow(1 - k, 3); el.textContent = eur(to * e); if (k < 1) requestAnimationFrame(tick); };
    requestAnimationFrame(tick);
  }
}

function renderMap() {
  const P = state.plan;
  if (!window.L || !P || !P.chosen) return;
  if (state.map) { state.map.remove(); state.map = null; }
  state.markers = new Map();
  const map = baseMap('map');
  const css = getComputedStyle(document.documentElement);
  const line = L.polyline(P.route.coords.map((c) => [c[1], c[0]]), { color: isDark() ? css.getPropertyValue('--blue').trim() || '#6AAEF7' : '#0B4EA2', weight: 4, opacity: 0.9 }).addTo(map);
  const chosen = new Set(P.chosen.stops);
  const popup = (c) => `<b>${esc(stName(c))}</b><br>${esc(stPlace(c))}<br>${priceTxt(c)} · ${approx(c)}${mins(c.detourMin)}<br><a href="${gmaps([c])}" target="_blank" rel="noopener">Ir con esta parada</a>`;
  const top = new Set(), zones = new Set();
  for (const pl of P.singles) {
    const c = pl.stops[0], z = Math.round(c.km / 15);
    if (chosen.has(c) || zones.has(z)) continue;
    zones.add(z); top.add(c);
    if (top.size >= 3) break;
  }
  for (const c of P.short) {
    if (chosen.has(c)) continue;
    const mk = top.has(c)
      ? L.marker([c.lat, c.lon], { icon: L.divIcon({ className: '', html: `<div class="pin">${fmt(c.price, 3)}</div>`, iconSize: [0, 0] }) })
      : L.circleMarker([c.lat, c.lon], { radius: 6, color: '#fff', weight: 1.5, fillColor: '#0B4EA2', fillOpacity: 0.9 });
    state.markers.set(String(c.id), mk.addTo(map).bindPopup(popup(c)));
  }
  for (const c of chosen) {
    state.markers.set(String(c.id), L.marker([c.lat, c.lon], { zIndexOffset: 1000, icon: L.divIcon({ className: '', html: `<div class="pin top">${fmt(c.price, 3)} €</div>`, iconSize: [0, 0] }) }).addTo(map).bindPopup(popup(c)));
  }
  endDot(map, state.origin, 'Salida'); endDot(map, state.dest, 'Destino');
  for (const p of state.stopPlaces) L.circleMarker([p.lat, p.lon], { radius: 5, color: '#10202E', weight: 2, fillColor: '#fff', fillOpacity: 1 }).addTo(map).bindTooltip(p.name);
  map.fitBounds(line.getBounds(), { padding: [24, 24] });
  state.map = map;
  state.mapDirty = false;
}
function showTab(name) {
  document.querySelectorAll('#tabs [data-tab]').forEach((b) => b.setAttribute('aria-selected', b.dataset.tab === name));
  for (const t of ['plan', 'precios', 'mapa', 'otras']) { const el = $('t-' + t); el.hidden = t !== name; if (t === name) { el.classList.remove('in-f'); void el.offsetWidth; el.classList.add('in-f'); } }
  if (name === 'mapa') { if (state.mapDirty || !state.map) renderMap(); else state.map.invalidateSize(); }
}
function showOnMap(id) {
  showTab('mapa');
  const mk = state.markers.get(String(id));
  if (!mk || !state.map) return;
  state.map.setView(mk.getLatLng(), Math.max(state.map.getZoom(), 12));
  mk.openPopup();
}

/* ---------- Navegación entre paneles ---------- */
const NEXT_LABEL = ['Ver el camino', 'Elegir esta ruta', 'Buscar mi parada', 'Nueva búsqueda'];
const STEP_NAMES = ['Gasolineras de la ruta', 'Desvíos reales', 'Mejor plan'];
function go(i) {
  const prev = state.panel;
  state.panel = i;
  state.maxPanel = Math.max(state.maxPanel, i);
  for (let k = 0; k < 4; k++) $('p' + k).hidden = k !== i;
  document.querySelectorAll('#wiz [data-go]').forEach((b) => {
    const k = +b.dataset.go;
    b.disabled = k > state.maxPanel;
    b.setAttribute('aria-current', k === i ? 'step' : 'false');
    b.classList.toggle('done', k < i);
  });
  $('btn-back').hidden = i === 0;
  $('btn-next').textContent = NEXT_LABEL[i];
  status('');
  if (i === 1) renderRoutes();
  const pan = $('p' + i); pan.classList.remove('in-f', 'in-b'); void pan.offsetWidth; pan.classList.add(i >= prev ? 'in-f' : 'in-b');
  if (i === 2) { paintCar(); showQ(state.carDone && !state.editing ? QS.length - 1 : state.q || 0, i >= prev ? 1 : -1); } else stop3D();
  window.scrollTo({ top: 0, behavior: 'auto' });
}
function progress(i) {
  $('steps').innerHTML = STEP_NAMES.map((t, k) => `<li class="${k < i ? 'done' : k === i ? 'active' : ''}">${t}</li>`).join('');
}
function busy(on, label) {
  const b = $('btn-next');
  b.disabled = on;
  if (on && label) b.textContent = label;
  if (!on) b.textContent = state.panel === 2 && state.q < QS.length - 1 ? 'Siguiente' : NEXT_LABEL[state.panel];
}
const fail = (e) => status(e && e.name === 'AbortError' ? 'El servidor tarda demasiado. Prueba otra vez.' : (e && e.message) || 'Algo ha fallado. Prueba otra vez.', true);

async function stepRoute() {
  busy(true, 'Trazando rutas…');
  try {
    state.stops = state.stops.filter((x) => x.place || (x.text || '').trim());
    state.origin = await resolvePlace(state.origin, $('origen').value, 'de dónde sales');
    state.dest = await resolvePlace(state.dest, $('destino').value, 'a dónde vas');
    for (const st of state.stops) st.place = await resolvePlace(st.place, st.text, 'la parada');
    state.stopPlaces = state.stops.map((x) => x.place);
    $('origen').value = state.origin.name; $('destino').value = state.dest.name;
    renderStops(); save();
    state.routes = await fetchRoute([state.origin, ...state.stopPlaces, state.dest], $('peajes').checked);
    state.alt = 0; state.plan = null; state.maxPanel = 1;
    busy(false); go(1);
  } catch (e) { busy(false); fail(e); }
}

async function stepCompute() {
  go(3);
  $('loading').hidden = false; $('result').hidden = true;
  paintCar(); progress(0); busy(true, 'Calculando…');
  try {
    await state.stationsP;
    if (!state.stations) await loadStations();
    const route = state.routes[state.alt];
    const car = readCar();
    const fuel = FUELS.find((f) => f.k === state.fuel);
    const near = stationsNearRoute(route, state.stations, fuel.i, car.corridor, readDepart());
    const P = preparePlan(route, near, car);
    P.stopPlaces = state.stopPlaces;
    state.plan = P;
    let measured = true;
    progress(1);
    if (P.short.length) { try { await refineDetours(P); } catch (_) { measured = false; } }
    progress(2);
    solve(P);
    renderResult();
    busy(false);
    status(measured ? '' : 'No he podido medir los desvíos exactos: los minutos son aproximados.');
  } catch (e) { busy(false); go(2); fail(e); }
}

function init() {
  restore();
  renderDiscounts(); paintCar(); updateGauge(); updateWhen();
  setupPlace($('origen'), $('sugg-origen'), (pl) => { state.origin = pl; });
  setupPlace($('destino'), $('sugg-destino'), (pl) => { state.dest = pl; });
  renderStops();
  go(0);
  // Los precios se descargan ya, en segundo plano: sirven también para predecir municipios al escribir
  state.stationsP = loadStations().catch(() => {});

  $('btn-next').addEventListener('click', () => {
    if (state.panel === 0) stepRoute();
    else if (state.panel === 1) go(2);
    else if (state.panel === 2) {
      if (state.q < QS.length - 1) showQ(state.q + 1, 1);
      else { state.carDone = true; state.editing = false; save(); stepCompute(); }
    }
    else { state.maxPanel = 0; go(0); }
  });
  $('btn-back').addEventListener('click', () => {
    if (state.panel === 2 && state.q > 0 && !(state.carDone && !state.editing)) return showQ(state.q - 1, -1);
    go(Math.max(0, state.panel - 1));
  });
  $('wiz').addEventListener('click', (e) => { const b = e.target.closest('[data-go]'); if (b && !b.disabled) go(+b.dataset.go); });
  $('alts').addEventListener('click', (e) => { const b = e.target.closest('[data-alt]'); if (b) { state.alt = +b.dataset.alt; state.plan = null; renderRoutes(); } });

  $('btn-add').addEventListener('click', () => {
    if (state.stops.length >= MAX_STOPS) return;
    state.stops.push({ place: null, text: '' }); renderStops(); $('stop-' + (state.stops.length - 1)).focus();
  });
  $('stops').addEventListener('click', (e) => {
    const b = e.target.closest('[data-del]');
    if (!b) return;
    state.stops.splice(+b.dataset.del, 1); renderStops(); save();
  });
  $('btn-swap').addEventListener('click', () => {
    [state.origin, state.dest] = [state.dest, state.origin];
    const o = $('origen').value; $('origen').value = $('destino').value; $('destino').value = o;
    state.stops.reverse(); renderStops(); save();
  });
  const useLocation = async () => {
    const b = $('btn-geo'); b.classList.add('busy');
    try { state.origin = await locate(); $('origen').value = 'Mi ubicación'; status(''); }
    catch (e) { status(e.message, true); }
    finally { b.classList.remove('busy'); }
  };
  $('btn-geo').addEventListener('click', useLocation);
  $('btn-when').addEventListener('click', () => { const b = $('when-box'); b.hidden = !b.hidden; if (!b.hidden) $('salida').focus(); });
  $('salida').addEventListener('input', updateWhen);
  $('btn-now').addEventListener('click', () => { $('salida').value = ''; $('when-box').hidden = true; updateWhen(); });
  $('peajes').addEventListener('change', save);
  $('temprano').addEventListener('change', save);

  const auto = () => setTimeout(() => { if (state.panel === 2 && state.q < QS.length - 1) showQ(state.q + 1, 1); }, 260);
  $('fuels').addEventListener('click', (e) => { const b = e.target.closest('[data-k]'); if (b) { state.fuel = b.dataset.k; updateGauge(); save(); auto(); } });
  $('car-types').addEventListener('click', (e) => { const b = e.target.closest('[data-type]'); if (b) { state.car.type = b.dataset.type; paintCar(); build3D(); updateGauge(); save(); } });
  $('car-colors').addEventListener('click', (e) => { const b = e.target.closest('[data-color]'); if (b) { state.car.color = b.dataset.color; paintCar(); if (car3d.paint) car3d.paint.color.set(state.car.color); save(); } });
  $('umbral').addEventListener('click', (e) => { const b = e.target.closest('[data-f]'); if (b) { state.frac = +b.dataset.f; updateGauge(); save(); auto(); } });
  $('desvio').addEventListener('click', (e) => { const b = e.target.closest('[data-d]'); if (b) { state.detour = b.dataset.d; updateGauge(); save(); auto(); } });
  $('deck').addEventListener('click', (e) => {
    const st = e.target.closest('[data-step]');
    if (st) {
      const [id, d] = st.dataset.step.split(':'), el = $(id);
      const v = Math.min(+el.max, Math.max(+el.min, (parseFloat(el.value) || 0) + +d));
      el.value = id === 'consumo' ? v.toFixed(1) : String(Math.round(v));
      updateGauge(); save(); return;
    }
    if (e.target.closest('#btn-tipico')) { const t = carType(); $('consumo').value = t.cons.toFixed(1); $('deposito').value = t.tank; updateGauge(); save(); return; }
    if (e.target.closest('#btn-editcar')) { state.editing = true; showQ(0, -1); }
  });
  $('discounts').addEventListener('input', (e) => {
    const k = e.target.dataset.brand;
    if (!k) return;
    const n = parseFloat(String(e.target.value).replace(',', '.'));
    if (n > 0) state.discounts[k] = Math.min(50, n); else delete state.discounts[k];
    save();
  });
  for (const id of FIELDS) $(id).addEventListener('input', () => { if (id === 'nivel') updateGauge(); save(); });
  for (const id of ['consumo', 'deposito']) $(id).addEventListener('change', () => { updateGauge(); });

  const paintSkins = () => { const cur = document.documentElement.dataset.skin || ''; document.querySelectorAll('[data-skin-btn]').forEach((b) => b.setAttribute('aria-pressed', b.dataset.skinBtn === cur)); };
  paintSkins();
  $('skins').addEventListener('click', (e) => {
    const b = e.target.closest('[data-skin-btn]');
    if (!b) return;
    if (b.dataset.skinBtn) document.documentElement.dataset.skin = b.dataset.skinBtn; else delete document.documentElement.dataset.skin;
    paintSkins(); save(); state.mapDirty = true;
  });

  $('tabs').addEventListener('click', (e) => { const b = e.target.closest('[data-tab]'); if (b) showTab(b.dataset.tab); });
  $('p3').addEventListener('click', async (e) => {
    const sortBtn = e.target.closest('[data-sort]');
    if (sortBtn && state.plan) { state.sort = sortBtn.dataset.sort; $('t-otras').innerHTML = renderList(state.plan); return; }
    const show = e.target.closest('[data-show]');
    if (show) { e.preventDefault(); showOnMap(show.dataset.show); return; }
    const dot = e.target.closest('.dot');
    if (dot) { showOnMap(dot.dataset.id); return; }
    if (e.target.closest('#btn-here')) {
      state.maxPanel = 0; go(0);
      await useLocation();
      $('salida').value = ''; updateWhen();
      if (state.origin && state.origin.gps) status('Origen cambiado a tu ubicación. Revisa el nivel del depósito en el paso del coche.');
    }
  });
}

if (typeof document !== 'undefined') init();
