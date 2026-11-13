# Hito

Dónde repostar en tu ruta. Metes origen, destino y los datos del coche, y calcula la parada que más ahorra contando el desvío real.

- **Precios:** Geoportal de Gasolineras del Ministerio para la Transición Ecológica. Una GitHub Action guarda una copia cada 6 horas en `data/estaciones.json`; si no existe o está vieja, la web los pide en directo.
- **Rutas y desvíos:** OSRM (servidor público) sobre OpenStreetMap. **Buscador de lugares:** Photon.
- **Sin servidor propio:** todo es estático y se publica en GitHub Pages con `.github/workflows/deploy.yml`.

## Cómo calcula

1. Autonomía = (litros al salir − reserva) / consumo. Solo cuentan las gasolineras hasta ese kilómetro.
2. Precio de referencia = mediana de las gasolineras a pie de ruta (a menos de 400 m) en ese tramo.
3. Ahorro neto = (referencia − precio) × litros que caben al llegar − coste del desvío.
4. El orden resta además los minutos de desvío al valor que pongas a tu tiempo.

## Probar en local

    python3 -m http.server 8000
