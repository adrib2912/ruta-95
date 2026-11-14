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
coords2=[[c[0], c[1]+0.25*math.sin(math.pi*i/N)] for i,c in enumerate(coords)]
dist=sum(hav((coords[i][1],coords[i][0]),(coords[i+1][1],coords[i+1][0])) for i in range(N))*1.08
lista=[]
towns=["Motilla del Palancar","Tarancón","Utiel","Requena","Honrubia","Minglanilla"]
for n in range(420):
    i=random.randrange(N); t=random.random()
    lon=coords[i][0]+(coords[i+1][0]-coords[i][0])*t; lat=coords[i][1]+(coords[i+1][1]-coords[i][1])*t
    off=random.choice([0,0,0.001,0.004,0.01,0.02,0.03,0.05]); lat+=off*random.choice([-1,1])
    p=(1.60+random.random()*0.14) if off<0.003 else (1.44+random.random()*0.2)
    tw=towns[i*len(towns)//N]
    lista.append({"IDEESS":str(n),"Latitud":f"{lat:.6f}".replace('.',','),"Longitud (WGS84)":f"{lon:.6f}".replace('.',','),
      "Rótulo":random.choice(["REPSOL","BALLENOIL","PLENOIL","CEPSA","BP","GALP","PETROPRIX"]),"Dirección":f"AUTOVIA A-3 KM {n}","Localidad":tw.upper(),"Municipio":tw,"Provincia":"CUENCA",
      "Horario":random.choice(["L-D: 24H","L-D: 24H","L-V: 06:00-22:00; S: 08:00-14:00","L-D: 02:00-03:00","raro"]),"Tipo Venta":"P",
      "Precio Gasolina 95 E5":f"{p:.3f}".replace('.',','),"Precio Gasoleo A":f"{p-0.1:.3f}".replace('.',',')})
for n in range(1200):
    lista.append({"IDEESS":"x"+str(n),"Latitud":"43,0","Longitud (WGS84)":"-8,0","Rótulo":"X","Municipio":"Coruña (A)","Provincia":"CORUÑA (A)","Tipo Venta":"P","Precio Gasolina 95 E5":"1,700"})
lista.append({"IDEESS":"m1","Latitud":"40,4168","Longitud (WGS84)":"-3,7038","Rótulo":"X","Municipio":"Madrid","Provincia":"MADRID","Tipo Venta":"P","Precio Gasolina 95 E5":"1,700"})
lista.append({"IDEESS":"v1","Latitud":"39,4699","Longitud (WGS84)":"-0,3763","Rótulo":"X","Municipio":"Valencia","Provincia":"VALENCIA","Tipo Venta":"P","Precio Gasolina 95 E5":"1,700"})
def rt(cs, d, toll):
    return {"legs":[{"summary":"x","steps":[{"ref":"M-30","distance":d*30,"intersections":[{"classes":["motorway"]}]},{"ref":"AP-36" if toll else "A-3","distance":d*970,"intersections":[{"classes":["toll","motorway"] if toll else ["motorway"]}]}],"distance":d*1000}],"distance":d*1000,"duration":d/105*3600,"geometry":{"coordinates":cs}}
def handle(route):
    u=route.request.url
    if 'minetur' in u: return route.fulfill(json={"Fecha":"13/11/2026 14:00:00","ListaEESSPrecio":lista})
    if '/route/v1/' in u: return route.fulfill(json={"code":"Ok","routes":[rt(coords,dist,False)] + ([] if 'exclude=toll' in u else [rt(coords2,dist*1.05,True)])})
    if '/table/v1/' in u:
        path=u.split('/driving/')[1]; cs,q=path.split('?'); pts=[tuple(map(float,c.split(','))) for c in cs.split(';')]
        qs=dict(x.split('=') for x in q.split('&')); src=[int(x) for x in qs['sources'].split(';')]; dst=[int(x) for x in qs['destinations'].split(';')]
        D=[[hav((pts[s][1],pts[s][0]),(pts[d][1],pts[d][0]))*1300 for d in dst] for s in src]
        return route.fulfill(json={"code":"Ok","distances":D,"durations":[[x/1000/70*3600 for x in row] for row in D]})
    if 'interpreter' in u:
        els=[]
        for k,s in enumerate(lista[:420:7]):
            la=float(s["Latitud"].replace(',','.')); lo=float(s["Longitud (WGS84)"].replace(',','.'))
            els.append({"type":"node","id":k,"lat":la+0.001,"lon":lo,"tags":{"amenity":"restaurant","name":f"Casa Paco {k}"}})
        return route.fulfill(json={"elements":els})
    if 'photon' in u or 'nominatim' in u: return route.fulfill(json={"features":[]} if 'photon' in u else [])
    if 'three.min.js' in u: return route.fulfill(path='/tmp/t/node_modules/three/build/three.min.js')
    if 'leaflet.min.js' in u: return route.fulfill(path='/tmp/t/node_modules/leaflet/dist/leaflet.js')
    if 'leaflet.min.css' in u: return route.fulfill(path='/tmp/t/node_modules/leaflet/dist/leaflet.css')
    if '127.0.0.1' in u: return route.continue_()
    return route.abort()
H=functools.partial(http.server.SimpleHTTPRequestHandler, directory=ROOT)
H.log_message=lambda *a,**k: None
srv=http.server.ThreadingHTTPServer(('127.0.0.1',8765),H); threading.Thread(target=srv.serve_forever,daemon=True).start()
DUMP="""()=>{const p=state.plan,c=p.chosen;return JSON.stringify({D:Math.round(p.D),range:Math.round(p.rangeKm),reserve:p.car.reserve,must:p.mustRefuel,closed:p.closed,singles:p.singles.length,legs:c.legs.map(l=>({km:Math.round(l.s.km),p:l.s.price,L:+l.L.toFixed(1)})),net:+c.net.toFixed(2),toll:p.route.tollKm|0,early:p.earlyBest?+p.earlyBest.net.toFixed(2):null,meal:c.meal,food:(c.stops[0].food||[]).length,info:document.querySelector('.infos').innerText.slice(0,300)})}"""
with sync_playwright() as p:
    b=p.chromium.launch()
    for scheme in ['light','dark']:
        pg=b.new_page(viewport={'width':390,'height':844}, device_scale_factor=2, color_scheme=scheme)
        errs=[]; pg.on('pageerror', lambda e: errs.append(str(e))); pg.on('console', lambda m: errs.append(m.text) if m.type=='error' and 'ERR_FAILED' not in m.text and 'Failed to load resource' not in m.text else None)
        pg.route('**/*', handle); pg.goto('http://127.0.0.1:8765/index.html'); pg.wait_for_timeout(800)
        pg.click('[data-when="later"]'); pg.click('[data-day="2"]'); pg.fill('#hora', '11:30'); pg.dispatch_event('#hora', 'change'); print('salida', pg.input_value('#salida'), pg.inner_text('#when-later')); pg.screenshot(path=f'{OUT}/when-{scheme}.png')
        pg.click('#origen'); pg.keyboard.type('mad'); pg.wait_for_timeout(700)
        sug=pg.locator('#sugg-origen li').all_inner_texts(); pg.locator('#sugg-origen li').first.dispatch_event('pointerdown')
        pg.click('#destino'); pg.keyboard.type('valen'); pg.wait_for_timeout(700); pg.locator('#sugg-destino li').first.dispatch_event('pointerdown')
        pg.screenshot(path=f'{OUT}/w1-{scheme}.png')
        pg.click('#btn-next'); pg.wait_for_selector('#alts button'); pg.wait_for_timeout(500)
        alts=pg.locator('#alts button').all_inner_texts(); pg.screenshot(path=f'{OUT}/w2-{scheme}.png')
        pg.click('#btn-next'); pg.wait_for_timeout(900); pg.click('[data-type="suv"]'); pg.click('[data-color="#D5202A"]'); pg.click('[data-roof="#16181B"]'); pg.wait_for_timeout(700)
        pg.screenshot(path=f'{OUT}/q0-{scheme}.png')
        pg.click('#q-next'); pg.wait_for_timeout(350); pg.click('#q-prev'); pg.wait_for_timeout(350)
        shots=0
        while pg.locator('#btn-next').inner_text().strip().lower()!='buscar mi parada' and shots<10:
            pg.click('#btn-next'); pg.wait_for_timeout(380); shots+=1
            q=pg.evaluate('()=>QS[state.q]')
            if q=='comida': pg.click('[data-eat="yes"]'); pg.wait_for_timeout(500)
            if q=='umbral': pg.check('#temprano')
            pg.screenshot(path=f'{OUT}/q{shots}-{scheme}.png')
        box=pg.locator('#dial svg').bounding_box(); pg.mouse.move(box['x']+box['width']*0.5, box['y']+box['height']*0.85); pg.mouse.down(); pg.mouse.move(box['x']+box['width']*0.78, box['y']+box['height']*0.2, steps=5); pg.mouse.up()
        if scheme=='light': print('QS', pg.evaluate('()=>QS.join(",")'), '| nivel tras arrastrar', pg.evaluate("()=>document.getElementById('nivel').value"), '| 3d', pg.evaluate('()=>car3d.ok'))
        pg.click('#btn-next'); pg.wait_for_selector('.planA', timeout=20000); pg.wait_for_timeout(1800)
        pg.screenshot(path=f'{OUT}/w4-{scheme}.png', full_page=True)
        if scheme=='light':
            print('sugg', sug, '| alts', alts); print(pg.evaluate(DUMP))
            for t in ['precios','mapa','otras']:
                pg.click(f'[data-tab="{t}"]'); pg.wait_for_timeout(500); pg.screenshot(path=f'{OUT}/w4-{t}.png')
            pg.click('[data-show]'); pg.wait_for_timeout(400); print('popup', pg.locator('.leaflet-popup-content').count())
            pg.screenshot(path=f'{OUT}/res-full.png', full_page=True); pg.click('#btn-back'); pg.wait_for_timeout(300); print('atajo q', pg.evaluate('()=>state.q')); pg.click('#btn-back'); pg.click('[data-alt="1"]'); pg.click('#btn-next'); pg.wait_for_timeout(400); print('atajo empieza en', pg.evaluate('()=>QS[state.q]'))
            for _ in range(4):
                if pg.locator('#btn-next').inner_text().strip().lower() in ('nueva búsqueda','calculando…'): break
                pg.click('#btn-next'); pg.wait_for_timeout(500)
            pg.wait_for_selector('.planA'); pg.wait_for_timeout(1500); print(pg.evaluate(DUMP))
        print(scheme,'errors:',errs)
    b.close()
