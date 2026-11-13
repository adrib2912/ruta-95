// Restaurantes a menos de 400 m de alguna gasolinera de España, de OpenStreetMap.
// Se ejecuta en GitHub Actions una vez por semana y deja data/restaurantes.json junto a la web.
import { readFile, writeFile } from 'node:fs/promises';

const MIRRORS = ['https://overpass-api.de/api/interpreter', 'https://overpass.private.coffee/api/interpreter', 'https://overpass.kumi.systems/api/interpreter'];
const QUERY = '[out:json][timeout:600];area["ISO3166-1"="ES"]["admin_level"="2"]->.es;nwr["amenity"~"^(restaurant|fast_food)$"]["name"](area.es);out center;';
const RADIUS_M = 400;

const hav = (a, b, c, d) => { const r = Math.PI / 180, x = Math.sin((c - a) * r / 2) ** 2 + Math.cos(a * r) * Math.cos(c * r) * Math.sin((d - b) * r / 2) ** 2; return 12742000 * Math.asin(Math.sqrt(x)); };

const st = JSON.parse(await readFile('data/estaciones.json', 'utf8')).e;
let data = null;
for (const url of MIRRORS) {
  try {
    const res = await fetch(url, { method: 'POST', body: 'data=' + encodeURIComponent(QUERY), headers: { 'Content-Type': 'application/x-www-form-urlencoded', 'User-Agent': 'ruta-95 (GitHub Actions)' }, signal: AbortSignal.timeout(620000) });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    data = await res.json();
    if (!Array.isArray(data.elements) || data.elements.length < 1000) throw new Error('respuesta corta');
    console.log('Overpass:', url, data.elements.length, 'restaurantes');
    break;
  } catch (e) { console.log('Falla', url, e.message); data = null; }
}
if (!data) throw new Error('Ningún servidor de OpenStreetMap ha respondido');

// Rejilla de gasolineras para filtrar rápido
const CELL = 0.01, grid = new Map();
for (const s of st) { const k = Math.floor(s[1] / CELL) + ':' + Math.floor(s[2] / CELL); if (!grid.has(k)) grid.set(k, []); grid.get(k).push(s); }
const out = [];
for (const e of data.elements) {
  const lat = e.lat ?? e.center?.lat, lon = e.lon ?? e.center?.lon, name = e.tags?.name;
  if (lat == null || !name) continue;
  const cy = Math.floor(lat / CELL), cx = Math.floor(lon / CELL);
  let near = false;
  for (let dy = -1; dy <= 1 && !near; dy++) for (let dx = -1; dx <= 1 && !near; dx++) for (const s of grid.get((cy + dy) + ':' + (cx + dx)) || []) if (hav(lat, lon, s[1], s[2]) <= RADIUS_M) { near = true; break; }
  if (near) out.push([+lat.toFixed(5), +lon.toFixed(5), name.slice(0, 60), e.tags.amenity === 'fast_food' ? 'f' : 'r']);
}
await writeFile('data/restaurantes.json', JSON.stringify({ ts: Date.now(), r: out }));
console.log('Guardados', out.length, 'restaurantes junto a gasolineras');
