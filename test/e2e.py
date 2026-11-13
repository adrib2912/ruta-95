import json, math, random, sys, threading, http.server, functools
from playwright.sync_api import sync_playwright
ROOT = sys.argv[1]; OUT = sys.argv[2]
random.seed(7)
A=(40.4168,-3.7038); B=(39.4699,-0.3763)
def hav(a,b):
    r=math.pi/180; dlat=(b[0]-a[0])*r; dlon=(b[1]-a[1])*r
    h=math.sin(dlat/2)**2+math.cos(a[0]*r)*math.cos(b[0]*r)*math.sin(dlon/2)**2
    return 2*6371*math.asin(math.sqrt(h))
N=80
coords=[[A[1]+(B[1]-A[1])*i/N + 0.03*math.sin(i/6), A[0]+(B[0]-A[0])*i/N] for i in range(N+1)]
dist=sum(hav((coords[i][1],coords[i][0]),(coords[i+1][1],coords[i+1][0])) for i in range(N))*1.08
lista=[]
for n in range(420):
    i=random.randrange(N); t=random.random()
    lon=coords[i][0]+(coords[i+1][0]-coords[i][0])*t; lat=coords[i][1]+(coords[i+1][1]-coords[i][1])*t
    off=random.choice([0,0,0.001,0.004,0.01,0.02,0.03,0.05])
    lat+=off*random.choice([-1,1])
    p=(1.60+random.random()*0.14) if off<0.003 else (1.44+random.random()*0.2)
    lista.append({"IDEESS":str(n),"Latitud":f"{lat:.6f}".replace('.',','),"Longitud (WGS84)":f"{lon:.6f}".replace('.',','),
      "Rótulo":random.choice(["REPSOL","BALLENOIL","PLENOIL","CEPSA","BP","GALP","PETROPRIX"]),"Dirección":f"AUTOVIA A-3 KM {n}","Localidad":"MOTILLA DEL PALANCAR","Municipio":"Motilla","Provincia":"CUENCA","Horario":random.choice(["L-D: 24H","L-D: 24H","L-V: 06:00-22:00; S: 08:00-14:00","L-D: 02:00-03:00","raro"]),"Tipo Venta":"P",
      "Precio Gasolina 95 E5":f"{p:.3f}".replace('.',','),"Precio Gasoleo A":f"{p-0.1:.3f}".replace('.',','),"Precio Gasolina 98 E5":"","Precio Gasoleo Premium":"","Precio Gases licuados del petróleo":""})
# relleno para superar el mínimo de 1000
for n in range(1200):
    lista.append({"IDEESS":"x"+str(n),"Latitud":"43,0","Longitud (WGS84)":"-8,0","Rótulo":"X","Tipo Venta":"P","Precio Gasolina 95 E5":"1,700"})
def handle(route):
    u=route.request.url
    if 'minetur' in u: return route.fulfill(json={"Fecha":"13/11/2026 14:00:00","ListaEESSPrecio":lista})
    if '/route/v1/' in u: return route.fulfill(json={"code":"Ok","routes":[{"legs":[{"distance":dist*400},{"distance":dist*600}],"distance":dist*1000,"duration":dist/105*3600,"geometry":{"coordinates":coords}}]})
    if '/table/v1/' in u:
        path=u.split('/driving/')[1]; cs,q=path.split('?'); pts=[tuple(map(float,c.split(','))) for c in cs.split(';')]
        qs=dict(x.split('=') for x in q.split('&')); src=[int(x) for x in qs['sources'].split(';')]; dst=[int(x) for x in qs['destinations'].split(';')]
        D=[[hav((pts[s][1],pts[s][0]),(pts[d][1],pts[d][0]))*1300 for d in dst] for s in src]
        return route.fulfill(json={"code":"Ok","distances":D,"durations":[[x/1000/70*3600 for x in row] for row in D]})
    if 'photon' in u:
        q=u.lower(); c=B if 'valencia' in q else A
        return route.fulfill(json={"features":[{"geometry":{"coordinates":[c[1],c[0]]},"properties":{"name":"Valencia" if c==B else "Madrid","state":"España"}}]})
    if 'leaflet.min.js' in u: return route.fulfill(path='/tmp/t/node_modules/leaflet/dist/leaflet.js')
    if 'leaflet.min.css' in u: return route.fulfill(path='/tmp/t/node_modules/leaflet/dist/leaflet.css')
    if '127.0.0.1' in u: return route.continue_()
    return route.abort()
H=functools.partial(http.server.SimpleHTTPRequestHandler, directory=ROOT)
H.log_message=lambda *a,**k: None
srv=http.server.ThreadingHTTPServer(('127.0.0.1',8765),H); threading.Thread(target=srv.serve_forever,daemon=True).start()
with sync_playwright() as p:
    b=p.chromium.launch()
    for scheme in ['light','dark']:
        pg=b.new_page(viewport={'width':390,'height':844}, device_scale_factor=2, color_scheme=scheme)
        errs=[]; pg.on('pageerror', lambda e: errs.append(str(e))); pg.on('console', lambda m: errs.append(m.text) if m.type=='error' and 'ERR_FAILED' not in m.text and 'Failed to load resource' not in m.text else None)
        pg.route('**/*', handle); pg.goto('http://127.0.0.1:8765/index.html')
        pg.screenshot(path=f'{OUT}/home-{scheme}.png', full_page=True)
        pg.fill('#origen','Madrid'); pg.fill('#destino','Valencia'); pg.click('#btn-add'); pg.fill('#stop-0','Cuenca'); pg.click('#btn-go')
        pg.wait_for_selector('.best', timeout=20000); pg.wait_for_timeout(600)
        pg.screenshot(path=f'{OUT}/res-{scheme}.png', full_page=True)
        if scheme=='light':
            DUMP="""()=>{const p=state.plan,c=p.chosen;return JSON.stringify({D:Math.round(p.D),range:Math.round(p.rangeKm),full:Math.round(p.fullRangeKm),must:p.mustRefuel,ref:p.ref,kind:p.refKind,near:p.near.length,closed:p.closed,first:p.first.length,later:p.later.length,singles:p.singles.length,incomplete:p.incomplete,legs:c.legs.map(l=>({km:Math.round(l.s.km),p:l.s.price,L:+l.L.toFixed(1),full:l.full,h:l.s.s[8],dm:+l.s.detourMin.toFixed(1)})),net:+c.net.toFixed(2),status:document.getElementById('status').textContent})}"""
            print(pg.evaluate(DUMP))
            pg.fill('#deposito','20'); pg.evaluate("()=>{const n=document.getElementById('nivel');n.value=100;n.dispatchEvent(new Event('input',{bubbles:true}))}")
            pg.evaluate("()=>document.querySelectorAll('details').forEach(d=>d.open=true)"); pg.fill('#d-repsol','8'); pg.click('#btn-go'); pg.wait_for_timeout(3500)
            print(pg.evaluate(DUMP)); pg.screenshot(path=f'{OUT}/res2-light.png', full_page=True)
            pg.click('.dot'); pg.wait_for_timeout(300); print('popup:', pg.locator('.leaflet-popup-content').count())
        print(scheme,'errors:',errs)
    b.close()
