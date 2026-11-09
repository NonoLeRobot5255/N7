#!/usr/bin/env python3
"""Dependency-free TCP receiver and live CPU dashboard (Python 3 standard library)."""
import json
import math
import socketserver
import threading
import time
from collections import defaultdict, deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

TCP_HOST = '127.0.0.1'
TCP_PORT = 9998
HTTP_HOST = '127.0.0.1'
HTTP_PORT = 8080
HISTORY_SECONDS = 300

samples = defaultdict(lambda: {'raw': deque(), 'average': deque()})
lock = threading.Lock()

class TCPHandler(socketserver.StreamRequestHandler):
    def handle(self):
        for raw_line in self.rfile:
            try:
                fields = raw_line.decode('utf-8').strip().split()
                if len(fields) not in (3, 4):
                    continue
                kind, node, value_text = fields[:3]
                if kind not in ('raw', 'average') or not node.startswith('node'):
                    continue
                value = float(value_text)
                if not math.isfinite(value):
                    continue
                timestamp = float(fields[3]) if len(fields) == 4 else time.time()
                if not math.isfinite(timestamp):
                    continue
                with lock:
                    q = samples[node][kind]
                    q.append((timestamp, value))
                    cutoff = time.time() - HISTORY_SECONDS
                    while q and q[0][0] < cutoff:
                        q.popleft()
            except (UnicodeError, ValueError, OverflowError):
                continue

class TCPServer(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True

PAGE = r'''<!doctype html>
<html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>CPU Streaming Monitor</title>
<style>
body{font-family:system-ui,Arial,sans-serif;background:#f5f7fb;color:#18243b;margin:0;padding:24px}
header{max-width:1100px;margin:auto auto 22px}h1{margin:0 0 8px}p{margin:0;color:#526079}
.legend{margin-top:12px;font-size:14px}.raw{color:#8893a7}.avg{color:#1769cc}
main{max-width:1100px;margin:auto;display:grid;grid-template-columns:repeat(auto-fit,minmax(430px,1fr));gap:16px}
.card{background:white;border:1px solid #e2e7f0;border-radius:12px;padding:16px;box-shadow:0 3px 10px #2030500b}
h2{margin:0 0 8px;font-size:18px}svg{width:100%;height:auto;display:block}
small{color:#67758c}#status{margin-top:10px;font-size:13px}
@media(max-width:520px){main{grid-template-columns:1fr}body{padding:12px}}
</style></head><body><header><h1>CPU Streaming Monitor</h1>
<p>Charge CPU brute (1 s) et moyenne Spark (fenêtre de 10 s, pas de 5 s).</p>
<div class="legend"><b class="raw">━ Brute</b> &nbsp;&nbsp; <b class="avg">━ Moyenne Spark</b></div>
<div id="status">En attente des données…</div></header><main id="charts"></main>
<script>
const NS='http://www.w3.org/2000/svg', host=document.getElementById('charts');
function el(name,attrs={},parent){const e=document.createElementNS(NS,name);for(const [k,v] of Object.entries(attrs))e.setAttribute(k,v);if(parent)parent.appendChild(e);return e;}
function draw(node,data,now){
  const card=document.createElement('section');card.className='card';
  const title=document.createElement('h2');title.textContent=node;card.appendChild(title);
  const svg=el('svg',{viewBox:'0 0 520 210',role:'img','aria-label':'CPU '+node});card.appendChild(svg);
  const x0=48,x1=505,y0=10,y1=178,from=now-300;
  for(const v of [0,25,50,75,100]){
    const y=y1-(v/100)*(y1-y0);
    el('line',{x1:x0,y1:y,x2:x1,y2:y,stroke:'#e6eaf0'},svg);
    const t=el('text',{x:40,y:y+4,'text-anchor':'end',fill:'#718096','font-size':11},svg);t.textContent=v+'%';
  }
  for(const sec of [300,240,180,120,60,0]){
    const x=x1-(sec/300)*(x1-x0);
    const t=el('text',{x,y:198,'text-anchor':'middle',fill:'#718096','font-size':11},svg);
    t.textContent=sec===0?'maint.':'-'+sec/60+' min';
  }
  for(const [kind,color,width] of [['raw','#9aa6b6',1.5],['average','#1769cc',3]]){
    const pts=(data[kind]||[]).filter(p=>p[0]>=from&&p[0]<=now+2).sort((a,b)=>a[0]-b[0]);
    if(!pts.length)continue;
    const path=pts.map(([ts,v],i)=>{
      const x=x0+((ts-from)/300)*(x1-x0),y=y1-(Math.max(0,Math.min(100,v))/100)*(y1-y0);
      return (i?'L':'M')+x.toFixed(1)+' '+y.toFixed(1);
    }).join(' ');
    el('path',{d:path,fill:'none',stroke:color,'stroke-width':width,'stroke-linejoin':'round','stroke-linecap':'round'},svg);
  }
  const footer=document.createElement('small');footer.textContent='Historique : 5 minutes';card.appendChild(footer);
  return card;
}
async function refresh(){
  try{
    const r=await fetch('/api/data',{cache:'no-store'});if(!r.ok)throw new Error('HTTP '+r.status);
    const payload=await r.json(), nodes=Object.keys(payload.nodes).sort();
    host.replaceChildren(...nodes.map(n=>draw(n,payload.nodes[n],payload.now)));
    document.getElementById('status').textContent=nodes.length?`${nodes.length} nœud(s) • actualisation 1 s`:'En attente des données TCP sur le port 9998…';
  }catch(e){document.getElementById('status').textContent='Serveur indisponible : '+e.message;}
}
refresh();setInterval(refresh,1000);
</script></body></html>'''

class HTTPHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        path = urlparse(self.path).path
        if path == '/':
            data = PAGE.encode('utf-8')
            content_type = 'text/html; charset=utf-8'
        elif path == '/api/data':
            now = time.time()
            with lock:
                cutoff = now - HISTORY_SECONDS
                for streams in samples.values():
                    for q in streams.values():
                        while q and q[0][0] < cutoff:
                            q.popleft()
                nodes = {node: {kind: list(q) for kind,q in streams.items()} for node,streams in samples.items()}
            data = json.dumps({'now': now, 'nodes': nodes}).encode('utf-8')
            content_type = 'application/json'
        else:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(data)
    def log_message(self, format, *args):
        pass

if __name__ == '__main__':
    tcp = TCPServer((TCP_HOST,TCP_PORT),TCPHandler)
    threading.Thread(target=tcp.serve_forever,daemon=True).start()
    print(f'TCP receiver: {TCP_HOST}:{TCP_PORT}')
    print(f'Dashboard: http://{HTTP_HOST}:{HTTP_PORT}/')
    try:
        ThreadingHTTPServer((HTTP_HOST,HTTP_PORT),HTTPHandler).serve_forever()
    except KeyboardInterrupt:
        print('\nStopping')
    finally:
        tcp.shutdown()
        tcp.server_close()
