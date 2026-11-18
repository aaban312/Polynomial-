const CACHE = 'konkur-graph-v2-20261118';
const ASSETS = ['./','./index.html','./styles-v2.css','./app-v2.js','./manifest-v2.webmanifest','./icons/icon-192.png','./icons/icon-512.png'];
self.addEventListener('install', e=>e.waitUntil(caches.open(CACHE).then(c=>c.addAll(ASSETS)).then(()=>self.skipWaiting())));
self.addEventListener('activate', e=>e.waitUntil(Promise.all([caches.keys().then(ks=>Promise.all(ks.filter(k=>k!==CACHE).map(k=>caches.delete(k)))),self.clients.claim()])));
self.addEventListener('fetch', e=>{
 if(e.request.method!=='GET'||new URL(e.request.url).origin!==self.location.origin) return;
 e.respondWith((async()=>{
   if(e.request.mode==='navigate'){
     try {const res=await fetch(e.request);if(res.ok){const c=await caches.open(CACHE);c.put(e.request,res.clone());}return res;}
     catch{return await caches.match(e.request)||await caches.match('./index.html')||Response.error();}
   }
   return await caches.match(e.request)||fetch(e.request).then(res=>{if(res.ok)caches.open(CACHE).then(c=>c.put(e.request,res.clone()));return res;});
 })());
});
