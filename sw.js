/* Ruta 95: funciona como app y sin cobertura.
   - La app (HTML, CSS, JS, iconos): siempre se pide la versión nueva; si no hay red, la guardada.
   - Librerías de los CDN: se guardan la primera vez y se sirven desde el móvil.
   - Mapas (OpenFreeMap): se sirven al instante desde lo guardado y se refrescan por detrás.
   - Precios: red primero; sin red, los últimos descargados. */
const V = 'r95-v47';
const SHELL = ['./', 'index.html', 'app.css?v=47', 'app.js?v=47', 'manifest.webmanifest', 'icon.svg', 'icon-180.png', 'icon-192.png', 'icon-512.png', 'vendor/flubber.min.js'];
const LIBS = 'r95-libs', TILES = 'r95-tiles', DATA = 'r95-data';
const MAX_TILES = 600;

self.addEventListener('install', (e) => {
  e.waitUntil(caches.open(V).then((c) => c.addAll(SHELL)).then(() => self.skipWaiting()));
});

self.addEventListener('activate', (e) => {
  e.waitUntil((async () => {
    for (const k of await caches.keys()) if (k.startsWith('r95-v') && k !== V) await caches.delete(k);
    await self.clients.claim();
  })());
});

async function networkFirst(req, cacheName, timeoutMs) {
  const cache = await caches.open(cacheName);
  try {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), timeoutMs);
    const res = await fetch(req, { cache: 'no-cache', signal: ctl.signal });
    clearTimeout(t);
    if (res.ok) cache.put(req, res.clone());
    return res;
  } catch (_) {
    const hit = await cache.match(req, { ignoreSearch: req.mode === 'navigate' }) || await caches.match(req, { ignoreSearch: true });
    if (hit) return hit;
    if (req.mode === 'navigate') return (await caches.match('index.html')) || Response.error();
    return Response.error();
  }
}

async function cacheFirst(req, cacheName) {
  const cache = await caches.open(cacheName);
  const hit = await cache.match(req);
  if (hit) return hit;
  const res = await fetch(req);
  if (res.ok || res.type === 'opaque') cache.put(req, res.clone());
  return res;
}

async function trim(cacheName, max) {
  const cache = await caches.open(cacheName);
  const keys = await cache.keys();
  for (let i = 0; i < keys.length - max; i++) await cache.delete(keys[i]);
}

async function staleWhileRevalidate(e, cacheName) {
  const cache = await caches.open(cacheName);
  const hit = await cache.match(e.request);
  const fresh = fetch(e.request).then((res) => {
    if (res.ok) { cache.put(e.request, res.clone()); trim(cacheName, MAX_TILES); }
    return res;
  }).catch(() => hit || Response.error());
  if (hit) { e.waitUntil(fresh); return hit; }
  return fresh;
}

self.addEventListener('fetch', (e) => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin === location.origin) {
    if (url.pathname.includes('/data/')) return e.respondWith(networkFirst(req, DATA, 8000));
    return e.respondWith(networkFirst(req, V, 4000));
  }
  if (/(^|\.)cdnjs\.cloudflare\.com$|(^|\.)unpkg\.com$|(^|\.)jsdelivr\.net$/.test(url.hostname)) return e.respondWith(cacheFirst(req, LIBS));
  if (url.hostname === 'tiles.openfreemap.org') return e.respondWith(staleWhileRevalidate(e, TILES));
  if (url.hostname.endsWith('minetur.gob.es')) return e.respondWith(networkFirst(req, DATA, 15000));
  // Rutas, buscador de sitios, etc.: siempre en directo
});
