// Descarga los precios del Ministerio y guarda una copia compacta en data/estaciones.json
import { writeFile, mkdir } from 'node:fs/promises';

const URL_MIN = 'https://sedeaplicaciones.minetur.gob.es/ServiciosRESTCarburantes/PreciosCarburantes/EstacionesTerrestres/';
const num = (v) => {
  if (v == null || v === '') return null;
  const n = parseFloat(String(v).replace(',', '.'));
  return Number.isFinite(n) ? n : null;
};

const res = await fetch(URL_MIN, {
  headers: { Accept: 'application/json', 'User-Agent': 'Mozilla/5.0 (ruta-95; GitHub Actions)' },
  signal: AbortSignal.timeout(90000),
});
if (!res.ok) throw new Error('El Ministerio respondió ' + res.status);
const json = await res.json();
const lista = json.ListaEESSPrecio || [];
if (lista.length < 1000) throw new Error('Respuesta sospechosamente corta: ' + lista.length);

const e = [];
for (const s of lista) {
  if (s['Tipo Venta'] && s['Tipo Venta'] !== 'P') continue; // solo venta al público
  const lat = num(s['Latitud']);
  const lon = num(s['Longitud (WGS84)']);
  if (lat == null || lon == null) continue;
  e.push([
    s['IDEESS'], lat, lon, s['Rótulo'] || '', s['Dirección'] || '', s['Localidad'] || '',
    s['Municipio'] || '', s['Provincia'] || '', s['Horario'] || '',
    num(s['Precio Gasolina 95 E5']), num(s['Precio Gasolina 98 E5']),
    num(s['Precio Gasoleo A']), num(s['Precio Gasoleo Premium']),
    num(s['Precio Gases licuados del petróleo']),
  ]);
}
await mkdir('data', { recursive: true });
await writeFile('data/estaciones.json', JSON.stringify({ fecha: json.Fecha || '', ts: Date.now(), e }));
console.log(`Guardadas ${e.length} estaciones (${json.Fecha})`);
