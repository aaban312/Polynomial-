(()=>{
'use strict';
const $=id=>document.getElementById(id);
const PALETTE=['#009f8e','#f27752','#755cff','#e64b96','#218ec8','#d0a33e','#49aa6a','#b36ab5'];
const KEY='konkur-graph-state-v2',SAVES_KEY='konkur-graph-snapshots-v2',THEME_KEY='konkur-graph-theme-v2',OLD_KEY='polynomial-workshop-data-v1';
const PARAM_DEFAULT={a:1,b:1,c:0,d:0,h:0,k:0,m:1,n:0};
const PARAM_DESCRIPTIONS={a:'ضریب a',b:'ضریب b',c:'ثابت c',d:'ثابت d',h:'جابجایی h',k:'انتقال k',m:'ضریب m',n:'ثابت n'};
const FN_NAMES=new Set(['abs','sqrt','floor','ceil','frac','sign','sin','cos','tan','cot','asin','acos','atan','ln','log','exp','cbrt','root','min','max','if']);
const canvas=$('graphCanvas'),ctx=canvas.getContext('2d'),stage=$('graphStage');
const liveCache=new Map();
let frame=false,W=700,H=460,toastTimer,installPrompt=null;
let pointer=null,dragPointers=new Map(),confirmAction=null,initialFit=false;
const initial=readCurrent()||readLegacy()||null;
const state={functions:initial?.functions||[createPoly(1,[5,2],1,PALETTE[0]),createExpr('a*abs(x-b)+c',2,PALETTE[1])],nextId:initial?.nextId||3,viewport:initial?.viewport||{cx:0,cy:0,sx:55,sy:38},activeId:initial?.activeId||1,editingId:null,tab:'controls',theme:readTheme()};
let saves=readSaves();
if(!state.functions.find(f=>f.id===state.activeId))state.activeId=state.functions[0]?.id??null;

function validColor(c){return typeof c==='string'&&/^#[0-9a-f]{6}$/i.test(c)}
function colorFor(id){return PALETTE[(id-1)%PALETTE.length]}
function cleanNumber(n){return typeof n==='number'&&Number.isFinite(n)&&Math.abs(n)<=1e7}
function normalise(text){
 let s=String(text).trim().replace(/[۰-۹]/g,d=>String('۰۱۲۳۴۵۶۷۸۹'.indexOf(d))).replace(/[٠-٩]/g,d=>String('٠١٢٣٤٥٦٧٨٩'.indexOf(d)))
  .replace(/[−–—]/g,'-').replace(/[＋]/g,'+').replace(/[×·]/g,'*').replace(/[٫،]/g,'.').replace(/π/gi,'pi')
  .replace(/≥/g,'>=').replace(/≤/g,'<=').replace(/≠/g,'!=').replace(/√/g,'sqrt')
  .replace(/⌊/g,'floor(').replace(/⌋/g,')').replace(/⌈/g,'ceil(').replace(/⌉/g,')')
  .replace(/\[([^\[\]]+)\]/g,'floor($1)').replace(/\|([^|]+)\|/g,'abs($1)')
  .replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]/g,d=>'^'+'⁰¹²³⁴⁵⁶⁷⁸⁹'.indexOf(d)).replace(/\s+/g,'').toLowerCase();
 s=s.replace(/^f\(x\)=/,'').replace(/^p\(x\)=/,'');
 if(!s)throw Error('لطفاً یک عبارت ریاضی وارد کنید.');
 if(s.length>180)throw Error('عبارت بیش از حد طولانی است (حداکثر ۱۸۰ نویسه).');
 return s;
}
function polyParse(s){
 if(!/^[x0-9.+\-*^]+$/.test(s))return null;
 if(/\*/.test(s))return null;
 const terms=s.replace(/-/g,'+-').split('+').filter(Boolean),co=Array(6).fill(0);
 if(!terms.length)return null;
 for(let t of terms){let sign=1;if(t.startsWith('-')){sign=-1;t=t.slice(1)}
  const m=t.match(/^((?:\d+(?:\.\d*)?|\.\d+)?)x(?:\^(\d+))?$/);
  let p,v;if(m){p=m[2]===undefined?1:Number(m[2]);v=m[1]?Number(m[1]):1;}
  else if(/^(?:\d+(?:\.\d*)?|\.\d+)$/.test(t)){p=0;v=Number(t);}
  else return null;
  if(p>5||!Number.isInteger(p)||!Number.isFinite(v)||Math.abs(v)>1e7)return null;
  co[p]+=sign*v;if(!cleanNumber(co[p]))return null;
 }
 let degree=5;while(degree>0&&Math.abs(co[degree])<1e-10)degree--;
 return {degree,coeffs:co.slice(0,degree+1)};
}
function scan(s){
 const raw=[];let i=0,numberIndex=0;
 while(i<s.length){
  const sub=s.slice(i),mNum=sub.match(/^(?:\d+(?:\.\d*)?|\.\d+)(?:e[+\-]?\d+)?/i);
  if(mNum){let rawN=mNum[0]; // avoid confusing 2e^x with scientific notation
    const v=Number(rawN);if(!Number.isFinite(v)||Math.abs(v)>1e7)throw Error('اندازهٔ عدد در عبارت بیش از حد زیاد است.');
    raw.push({t:'num',v,start:i,end:i+rawN.length,nidx:numberIndex++});i+=rawN.length;continue;
  }
  const mId=sub.match(/^[a-z]+/);
  if(mId){raw.push({t:'id',v:mId[0],start:i,end:i+mId[0].length});i+=mId[0].length;continue;}
  let op=s.slice(i,i+2);
  if(['<=','>=','!=','=='].includes(op)){raw.push({t:'op',v:op,start:i,end:i+2});i+=2;continue;}
  op=s[i];if('+-*/^(),<>= '.includes(op)&&op!==' '){raw.push({t:op==='('? 'open':op===')'?'close':op===','?'comma':'op',v:op,start:i,end:i+1});i++;continue;}
  throw Error(`علامت «${op}» شناخته نشد. از قالب‌های راهنما استفاده کن.`);
 }
 const toks=[];
 for(let j=0;j<raw.length;j++){
  const a=raw[j-1],b=raw[j];
  if(a){const aEnd=a.t==='num'||a.t==='close'||a.t==='id';const bStart=b.t==='num'||b.t==='id'||b.t==='open';
    const isFn=a.t==='id'&&FN_NAMES.has(a.v)&&b.t==='open';
    if(aEnd&&bStart&&!isFn)toks.push({t:'op',v:'*'});
  }
  toks.push(b);
 }
 toks.push({t:'eof',v:''});return {toks,literals:raw.filter(t=>t.t==='num').map(t=>({v:t.v,start:t.start,end:t.end,nidx:t.nidx}))};
}
function astParse(src){
 const scanned=scan(src),toks=scanned.toks;let pos=0,nodes=0;
 const peek=()=>toks[pos],take=()=>toks[pos++];
 function parse(min=0,depth=0){
  if(depth>32||++nodes>250)throw Error('عبارت بیش از حد پیچیده است.');
  const token=take();let left;
  if(token.t==='num')left={t:'num',i:token.nidx};
  else if(token.t==='id'){
   if(FN_NAMES.has(token.v)){
    if(peek().t!=='open')throw Error(`برای تابع ${token.v} از پرانتز استفاده کن؛ مانند ${token.v}(x).`);
    take();const args=[];
    if(peek().t!=='close'){args.push(parse(0,depth+1));while(peek().t==='comma'){take();args.push(parse(0,depth+1));}}
    if(take().t!=='close')throw Error('پرانتز تابع را ببند.');
    if(!(token.v==='log'?[1,2].includes(args.length):args.length===(token.v==='if'?3:['root','min','max'].includes(token.v)?2:1)))throw Error(`تعداد ورودی‌های تابع ${token.v} صحیح نیست.`);
    if(token.v==='if'&&args[0].t!=='rel')throw Error('ورودی اول if باید شرط باشد، مانند if(x<0,-x,x).');
    left={t:'fn',name:token.v,args};
   }else if(token.v==='x'||token.v==='y'||token.v==='pi'||token.v==='e'||Object.hasOwn(PARAM_DEFAULT,token.v))left={t:'id',name:token.v};
   else throw Error(`نماد «${token.v}» ناشناخته است. برای توابع از نام‌های راهنما استفاده کن.`);
  }
  else if(token.t==='open') {left=parse(0,depth+1);if(take().t!=='close')throw Error('تعداد پرانتزهای باز و بسته برابر نیست.');}
  else if(token.t==='op'&&(token.v==='+'||token.v==='-'))left={t:'unary',op:token.v,value:parse(25,depth+1)};
  else throw Error('ساختار عبارت صحیح نیست. جای عملگرها و پرانتزها را بررسی کن.');
  while(true){const next=peek();if(next.t!=='op')break;
   const spec={'+':[10,11],'-':[10,11],'*':[20,21],'/':[20,21],'^':[30,30],'<':[5,6],'>':[5,6],'<=':[5,6],'>=':[5,6],'=':[5,6],'==':[5,6],'!=':[5,6]}[next.v];
   if(!spec||spec[0]<min)break;
   take();const right=parse(spec[1],depth+1);
   left={t:spec[0]===5?'rel':'op',op:next.v,left,right};
  }
  return left;
 }
 const ast=parse();if(peek().t!=='eof')throw Error('بخشی از عبارت قابل تحلیل نبود. پرانتزها و عملگرها را بررسی کن.');
 const used=new Set(),powers=new Set();let hasY=false;
 function traverse(node,isExponent=false){
  if(node.t==='num'){if(isExponent)powers.add(node.i);return;}
  if(node.t==='id'){if(node.name==='y')hasY=true;if(Object.hasOwn(PARAM_DEFAULT,node.name))used.add(node.name);return;}
  if(node.t==='unary'){traverse(node.value,isExponent);return;}
  if(node.t==='fn'){node.args.forEach(arg=>traverse(arg,isExponent));return;}
  traverse(node.left,isExponent);traverse(node.right,isExponent||node.op==='^');
 }
 traverse(ast);
 if(hasY && (ast.t!=='rel'||(ast.left.t!=='id'||ast.left.name!=='y')&&(ast.right.t!=='id'||ast.right.name!=='y')))
   throw Error('برای ناحیهٔ صفحه، y را به‌صورت y<=f(x) یا y>=f(x) وارد کن.');
 let mode='curve',relation=null, boundary=null;
 if(ast.t==='rel'){
  relation=ast.op==='=='?'=':ast.op;
  if(relation==='!=')throw Error('نامساوی ≠ فعلاً پشتیبانی نمی‌شود؛ از < یا > استفاده کن.');
  if(ast.left.t==='id'&&ast.left.name==='y'){
    mode=relation==='='?'curve':'yshade';boundary=ast.right;
  }else if(ast.right.t==='id'&&ast.right.name==='y'){
    mode=relation==='='?'curve':'yshade';boundary=ast.left;
    relation={'<':'>','>':'<','<=':'>=','>=':'<=','=':'='}[relation];
  }else {mode=relation==='='?'equality':'xshade';}
 }
 const params={};used.forEach(k=>params[k]=PARAM_DEFAULT[k]);
 const adjustable=scanned.literals.filter(t=>!powers.has(t.nidx));
 const extraTransform=mode==='curve'&&used.size===0&&adjustable.length===0;
 if(extraTransform){params.a=1;params.h=0;params.k=0;}
 return {ast,mode,relation,boundary,params,literals:scanned.literals.map(l=>l.v),positions:scanned.literals,adjustable:adjustable.map(l=>l.nidx),extraTransform};
}
function createPoly(degree,coeffs,id,color){return {id,kind:'poly',degree,coeffs,visible:true,color};}
function createExpr(expression,id,color){const src=normalise(expression),comp=astParse(src);
 const f={id,kind:'expr',src,params:comp.params,literals:comp.literals,visible:true,color};
 liveCache.set(id,comp);return f;
}
function compile(f){
 if(f.kind==='poly')return null;
 let comp=liveCache.get(f.id);if(!comp){comp=astParse(f.src);liveCache.set(f.id,comp);}return comp;
}
function makeFunction(source,id,col){const src=normalise(source),p=polyParse(src);if(p)return createPoly(p.degree,p.coeffs,id,col);return createExpr(src,id,col);}
function evaluateNode(node,f,x,comp){
 switch(node.t){
  case 'num':return f.literals[node.i];
  case 'id':return node.name==='x'?x:node.name==='pi'?Math.PI:node.name==='e'?Math.E:node.name==='y'?NaN:f.params[node.name];
  case 'unary':{const v=evaluateNode(node.value,f,x,comp);return node.op==='-'?-v:v;}
  case 'rel':{const l=evaluateNode(node.left,f,x,comp),r=evaluateNode(node.right,f,x,comp);return relationHolds(node.op,l,r)?1:0;}
  case 'op':{
   const l=evaluateNode(node.left,f,x,comp),r=evaluateNode(node.right,f,x,comp);
   if(node.op==='+')return l+r;if(node.op==='-')return l-r;if(node.op==='*')return l*r;
   if(node.op==='/')return r===0?NaN:l/r;if(node.op==='^')return Math.pow(l,r);return NaN;
  }
  case 'fn':{
   if(node.name==='if'){return evaluateNode(node.args[0],f,x,comp)?evaluateNode(node.args[1],f,x,comp):evaluateNode(node.args[2],f,x,comp);}
   const v=evaluateNode(node.args[0],f,x,comp);
   if(node.name==='min'||node.name==='max'){const q=evaluateNode(node.args[1],f,x,comp);return node.name==='min'?Math.min(v,q):Math.max(v,q);}
   if(node.name==='root'){const q=evaluateNode(node.args[1],f,x,comp);if(q===0)return NaN;if(v<0&&Number.isInteger(q)&&Math.abs(q)%2===1)return -Math.pow(-v,1/q);return Math.pow(v,1/q);}
   switch(node.name){case 'abs':return Math.abs(v);case 'sqrt':return Math.sqrt(v);case 'floor':return Math.floor(v);case 'ceil':return Math.ceil(v);case 'frac':return v-Math.floor(v);case 'sign':return Math.sign(v);
    case 'sin':return Math.sin(v);case 'cos':return Math.cos(v);case 'tan':return Math.tan(v);case 'cot':return 1/Math.tan(v);case 'cbrt':return Math.cbrt(v);case 'asin':return Math.asin(v);case 'acos':return Math.acos(v);case 'atan':return Math.atan(v);case 'ln':return Math.log(v);case 'log':return node.args.length===2?Math.log(v)/Math.log(evaluateNode(node.args[1],f,x,comp)):Math.log10(v);case 'exp':return Math.exp(v);
   }return NaN;
  }
 }return NaN;
}
function relationHolds(op,l,r){if(!Number.isFinite(l)||!Number.isFinite(r))return false;
 return {'<':l<r,'<=':l<=r,'>':l>r,'>=':l>=r,'=':Math.abs(l-r)<1e-8,'==':Math.abs(l-r)<1e-8}[op]||false;
}
function evalCurve(f,x){
 if(f.kind==='poly'){let y=f.coeffs[f.degree];for(let i=f.degree-1;i>=0;i--)y=y*x+f.coeffs[i];return Number.isFinite(y)?y:NaN;}
 const c=compile(f),xx=c.extraTransform?x-f.params.h:x;
 const base=evaluateNode(c.boundary||c.ast,f,xx,c);
 return Number.isFinite(base)?c.extraTransform?f.params.a*base+f.params.k:base:NaN;
}
function difference(f,x){const c=compile(f);return evaluateNode(c.ast.left,f,x,c)-evaluateNode(c.ast.right,f,x,c);}
function modeOf(f){return f.kind==='poly'?'curve':compile(f).mode;}
function saveCurrent(){try{localStorage.setItem(KEY,JSON.stringify({version:2,functions:state.functions,nextId:state.nextId,viewport:state.viewport,activeId:state.activeId}));$('autoSavedText').textContent='● ذخیرهٔ خودکار فعال است';}catch{$('autoSavedText').textContent='ذخیرهٔ خودکار غیرفعال است';}}
function readTheme(){try{const v=localStorage.getItem(THEME_KEY);return v==='dark'?'dark':'light';}catch{return 'light';}}
function parseSafeModel(item){
 if(!item||!Array.isArray(item.functions)||item.functions.length>60)throw Error('فایل پروژه معتبر نیست.');
 const functions=[],ids=new Set();
 for(const obj of item.functions){
  if(!obj||!Number.isSafeInteger(obj.id)||obj.id<1||ids.has(obj.id))throw Error('شناسهٔ یک تابع نامعتبر است.');ids.add(obj.id);
  const color=validColor(obj.color)?obj.color:colorFor(obj.id);
  let f;
  if(obj.kind==='poly'){
   if(!Number.isInteger(obj.degree)||obj.degree<0||obj.degree>5||!Array.isArray(obj.coeffs)||obj.coeffs.length!==obj.degree+1||!obj.coeffs.every(cleanNumber))throw Error('ضرایب چندجمله‌ای نامعتبر است.');
   f=createPoly(obj.degree,obj.coeffs.slice(),obj.id,color);
  }else if(obj.kind==='expr'){
   if(typeof obj.src!=='string')throw Error('عبارت تابع نامعتبر است.');
   f=createExpr(obj.src,obj.id,color);const c=compile(f);
   if(!Array.isArray(obj.literals)||obj.literals.length!==c.literals.length||!obj.literals.every(cleanNumber))throw Error('ثابت‌های عبارت نامعتبرند.');
   f.literals=obj.literals.slice();
   if(!obj.params||typeof obj.params!=='object')throw Error('پارامترهای تابع نامعتبرند.');
   for(const k of Object.keys(c.params)){if(!cleanNumber(obj.params[k]))throw Error('پارامتر تابع نامعتبر است.');f.params[k]=obj.params[k];}
  }else throw Error('نوع تابع شناخته نشد.');
  f.visible=obj.visible!==false;functions.push(f);
 }
 const v=item.viewport;
 const viewport=v&&[v.cx,v.cy,v.sx,v.sy].every(n=>typeof n==='number'&&Number.isFinite(n))&&v.sx>1&&v.sx<3000&&v.sy>1&&v.sy<3000?{cx:v.cx,cy:v.cy,sx:v.sx,sy:v.sy}:{cx:0,cy:0,sx:48,sy:42};
 const nextId=Math.max(1,...functions.map(f=>f.id+1));
 return {functions,nextId,viewport,activeId:functions.some(f=>f.id===item.activeId)?item.activeId:(functions[0]?.id??null)};
}
function readCurrent(){try{const s=localStorage.getItem(KEY);return s?parseSafeModel(JSON.parse(s)):null;}catch{return null;}}
function readLegacy(){try{const s=localStorage.getItem(OLD_KEY);if(!s)return null;const old=JSON.parse(s);if(!old||!Array.isArray(old.functions))return null;
 return parseSafeModel({functions:old.functions.map(f=>({...f,kind:'poly'})),nextId:old.nextId,viewport:old.viewport,activeId:old.functions[0]?.id});
 }catch{return null;}}
function readSaves(){try{const data=JSON.parse(localStorage.getItem(SAVES_KEY)||'[]');if(!Array.isArray(data))return [];return data.slice(0,30).filter(v=>v&&typeof v.name==='string'&&v.name.length<100&&typeof v.date==='string'&&v.model&&typeof v.id==='string');}catch{return [];}}
function writeSaves(){try{localStorage.setItem(SAVES_KEY,JSON.stringify(saves));return true;}catch{toast('حافظهٔ مرورگر پر است؛ از خروجی JSON استفاده کن.');return false;}}
function snapshot(){return {version:2,functions:JSON.parse(JSON.stringify(state.functions)),nextId:state.nextId,viewport:{...state.viewport},activeId:state.activeId};}
function loadSnapshot(model){const value=parseSafeModel(model);liveCache.clear();state.functions=value.functions;state.nextId=value.nextId;state.viewport=value.viewport;state.activeId=value.activeId;state.editingId=null;initialFit=true;$('equationInput').value='';renderAll();saveCurrent();drawSoon();}
function formatNumber(n){if(!Number.isFinite(n))return '—';if(Math.abs(n)<1e-8)return '0';if(Math.abs(n)>1e6||(Math.abs(n)<.0001))return Number(n.toPrecision(5)).toString();return String(Number(n.toFixed(5)));}
function persian(n){return String(n).replace(/\d/g,d=>'۰۱۲۳۴۵۶۷۸۹'[Number(d)]);}
function polyFormula(f){const pieces=[];for(let p=f.degree;p>=0;p--){const num=f.coeffs[p];if(Math.abs(num)<1e-10)continue;
  const value=Math.abs(num),coef=p&&Math.abs(value-1)<1e-10?'':formatNumber(value);
  const term=p===0?formatNumber(value):`${coef}x${p===1?'':'^'+p}`;
  pieces.push((pieces.length?(num<0?' - ':' + '):(num<0?'-':''))+term);
 }return pieces.join('')||'0';}
function shownFormula(f){if(f.kind==='poly')return `y = ${polyFormula(f)}`;
 const comp=compile(f);let out='',idx=0;
 for(const pos of comp.positions){out+=f.src.slice(idx,pos.start)+formatNumber(f.literals[pos.nidx]);idx=pos.end;}
 out+=f.src.slice(idx);
 return (comp.mode==='curve'?'y = ':comp.mode==='xshade'?'نامعادله: ':comp.mode==='yshade'?'ناحیه: ':'ریشه‌ها: ')+out;
}
function labelKind(f){if(f.kind==='poly')return `چندجمله‌ای درجهٔ ${persian(f.degree)}`;
 const c=compile(f);if(c.mode==='xshade'||c.mode==='yshade')return 'نامعادله';if(c.mode==='equality')return 'معادله';
 if(f.src.includes('abs('))return 'قدرمطلقی';if(f.src.includes('sqrt('))return 'رادیکالی';if(f.src.includes('floor('))return 'جزء صحیح';return 'تابع دلخواه';
}
function descriptor(f){return `تابع ${persian(f.id)}`;}
function toast(s){const el=$('toast');clearTimeout(toastTimer);el.textContent=s;el.classList.add('show');toastTimer=setTimeout(()=>el.classList.remove('show'),2600);}
function setTab(tab){state.tab=tab;document.querySelectorAll('.tab').forEach(b=>{const yes=b.dataset.tab===tab;b.classList.toggle('active',yes);b.setAttribute('aria-selected',String(yes));});document.querySelectorAll('.pane').forEach(p=>{p.classList.toggle('active',p.id==='pane-'+tab);p.hidden=p.id!=='pane-'+tab;});if(tab==='saves')renderSaves();}
document.querySelectorAll('.tab').forEach(b=>b.addEventListener('click',()=>setTab(b.dataset.tab)));
$('newFromControls').onclick=()=>{resetEditing();setTab('create');$('equationInput').focus();};
function renderPills(){const root=$('functionPills');root.replaceChildren();
 for(const f of state.functions){const b=document.createElement('button');b.type='button';b.className='function-pill'+(state.activeId===f.id?' selected':'');b.dataset.id=f.id;b.setAttribute('aria-pressed',String(state.activeId===f.id));
  const dot=document.createElement('i');dot.className='pill-dot';dot.style.background=f.color;const lab=document.createElement('span');lab.textContent=descriptor(f)+(f.visible?'':' (مخفی)');b.append(dot,lab);root.append(b);
 }
 $('emptyFunctions').hidden=state.functions.length>0;
}
$('functionPills').addEventListener('click',e=>{const button=e.target.closest('[data-id]');if(!button)return;state.activeId=Number(button.dataset.id);renderPills();renderActive();saveCurrent();$('pane-controls').scrollTo({top:0,behavior:'smooth'});});
function boundOf(n){return Math.min(1e7,Math.max(5,Math.ceil(Math.abs(n)*1.3/5)*5+5));}
function sliderPaint(el,color){let percent=100*(Number(el.value)-Number(el.min))/(Number(el.max)-Number(el.min));el.style.background=`linear-gradient(to right, ${color} ${percent}%, var(--line) ${percent}%)`;el.style.setProperty('--param-color',color);}
function paramsFor(f){
 if(f.kind==='poly')return [...f.coeffs].map((v,p)=>({key:String(p),label:String.fromCharCode(97+f.degree-p),hint:p===0?'جملهٔ ثابت':`ضریب x${p===1?'':'^'+p}`,v})).reverse();
 const c=compile(f),ps=Object.keys(f.params).map(k=>({key:'p-'+k,label:k,hint:c.extraTransform?({'a':'کشش عمودی','h':'انتقال افقی','k':'انتقال عمودی'}[k]||k):PARAM_DESCRIPTIONS[k],v:f.params[k]}));
 for(const ix of c.adjustable){ps.push({key:'n-'+ix,label:'k'+(ix+1),hint:`عدد ${persian(ix+1)} در عبارت`,v:f.literals[ix]});}
 return ps;
}
function renderActive(){const root=$('activeFunction');root.replaceChildren();const f=state.functions.find(f=>f.id===state.activeId);root.hidden=!f;if(!f)return;
 root.style.setProperty('--current-color',f.color);
 const head=document.createElement('div');head.className='function-head';
 const titleBox=document.createElement('div'),label=document.createElement('div'),formula=document.createElement('p');
 label.className='function-title';label.textContent=descriptor(f)+' · '+labelKind(f);
 formula.className='function-formula';formula.textContent=shownFormula(f);titleBox.append(label,formula);head.append(titleBox);
 const tools=document.createElement('div');tools.className='function-actions';
 const inp=document.createElement('input');inp.type='color';inp.className='color-well';inp.value=f.color;inp.title='رنگ نمودار';inp.setAttribute('aria-label','تغییر رنگ نمودار');inp.dataset.action='color';tools.append(inp);
 for(const [act,txt,title] of [['visibility',f.visible?'◉':'◌',f.visible?'مخفی کردن نمودار':'نمایش نمودار'],['edit','✎','ویرایش عبارت'],['delete','×','حذف نمودار']]){
  const b=document.createElement('button');b.type='button';b.className='icon-action'+(act==='delete'?' danger':'');b.dataset.action=act;b.textContent=txt;b.title=title;b.setAttribute('aria-label',title);tools.append(b);
 }head.append(tools);root.append(head);
 const list=document.createElement('div');list.className='param-list';
 for(const p of paramsFor(f)){
  const bound=boundOf(p.v),line=document.createElement('div');line.className='param-row';line.dataset.param=p.key;
  line.innerHTML=`<div class="param-top"><span class="param-title"><span class="param-symbol"></span><span class="param-hint"></span></span><input type="number" class="param-number" inputmode="decimal" step="any" min="-10000000" max="10000000" aria-label="مقدار ضریب" /></div><div class="range-row"><span class="range-edge">-${bound}</span><input type="range" class="param-slider" min="${-bound}" max="${bound}" step="0.1" aria-label="اهرم ضریب"><span class="range-edge">+${bound}</span></div>`;
  line.querySelector('.param-symbol').textContent=p.label;line.querySelector('.param-hint').textContent=p.hint;
  const n=line.querySelector('.param-number');n.value=p.v;
  const slider=line.querySelector('.param-slider');slider.value=p.v;sliderPaint(slider,f.color);
  list.append(line);
 }
 if(list.children.length)root.append(list);
 else {const note=document.createElement('p');note.className='hint-note';note.textContent='این عبارت پارامتر عددی ندارد. برای ساخت اهرم از a، b یا c در عبارت استفاده کن.';root.append(note);}
 if(modeOf(f)==='equality'){
  const res=document.createElement('p');res.className='roots-line';res.id='rootsReadout';root.append(res);updateRoots();
 }
}
function updateFormulaLabel(f){const el=$('activeFunction').querySelector('.function-formula');if(el)el.textContent=shownFormula(f);}
function getParam(f,key){if(f.kind==='poly')return f.coeffs[Number(key)];return key.startsWith('p-')?f.params[key.slice(2)]:f.literals[Number(key.slice(2))];}
function putParam(f,key,v){if(f.kind==='poly')f.coeffs[Number(key)]=v;else if(key.startsWith('p-'))f.params[key.slice(2)]=v;else f.literals[Number(key.slice(2))]=v;}
$('activeFunction').addEventListener('input',e=>{
 const el=e.target,f=state.functions.find(f=>f.id===state.activeId);if(!f)return;
 if(el.dataset.action==='color'){if(!validColor(el.value))return;f.color=el.value;renderPills();renderLegend();$('activeFunction').querySelectorAll('.param-slider').forEach(s=>sliderPaint(s,f.color));saveCurrent();drawSoon();return;}
 if(!el.matches('.param-slider, .param-number'))return;
 if(el.classList.contains('param-number')&&!el.value.trim())return;
 const row=el.closest('.param-row'),value=Number(el.value);if(!cleanNumber(value))return;
 putParam(f,row.dataset.param,value);
 const slider=row.querySelector('.param-slider'),number=row.querySelector('.param-number');
 const max=Math.max(Math.abs(Number(slider.min)),Math.abs(Number(slider.max)));
 if(Math.abs(value)>max){const b=boundOf(value);slider.min=-b;slider.max=b;row.querySelectorAll('.range-edge')[0].textContent='-'+b;row.querySelectorAll('.range-edge')[1].textContent='+'+b;}
 slider.value=String(value);number.value=String(value);sliderPaint(slider,f.color);updateFormulaLabel(f);
 if(modeOf(f)==='equality')updateRoots();saveCurrent();drawSoon();
});
$('activeFunction').addEventListener('change',e=>{if(!e.target.matches('.param-number'))return;const f=state.functions.find(f=>f.id===state.activeId);if(!f)return;const row=e.target.closest('.param-row');e.target.value=String(getParam(f,row.dataset.param));});
$('activeFunction').addEventListener('click',e=>{
 const b=e.target.closest('[data-action]');if(!b)return;
 const f=state.functions.find(f=>f.id===state.activeId);if(!f)return;
 const act=b.dataset.action;
 if(act==='visibility'){f.visible=!f.visible;renderAll();saveCurrent();drawSoon();}
 if(act==='edit'){state.editingId=f.id;$('equationInput').value=f.kind==='poly'?polyFormula(f):f.src;$('formTitle').textContent='ویرایش نمودار '+persian(f.id);$('submitEquation').textContent='✓ ثبت تغییرات';$('cancelEdit').hidden=false;setTab('create');$('equationInput').focus();}
 if(act==='delete'){askConfirm('حذف نمودار',`«${descriptor(f)}» حذف شود؟`,()=>{state.functions=state.functions.filter(item=>item.id!==f.id);liveCache.delete(f.id);state.activeId=state.functions[0]?.id??null;renderAll();saveCurrent();drawSoon();toast('نمودار حذف شد.');});}
});
function resetEditing(){state.editingId=null;$('equationInput').value='';$('formTitle').textContent='افزودن تابع یا نامعادله';$('submitEquation').textContent='＋ افزودن به نمودار';$('cancelEdit').hidden=true;$('equationError').textContent='';}
$('cancelEdit').onclick=resetEditing;
$('equationInput').addEventListener('input',()=>{$('equationError').textContent='';});
$('equationForm').addEventListener('submit',e=>{
 e.preventDefault();const expr=$('equationInput').value.trim();let f;
 try{if(state.editingId!==null){const old=state.functions.find(f=>f.id===state.editingId);if(!old)throw Error('نمودار پیدا نشد.');f=makeFunction(expr,old.id,old.color);f.visible=old.visible;state.functions=state.functions.map(item=>item.id===f.id?f:item);}
 else {if(state.functions.length>=60)throw Error('حداکثر ۶۰ نمودار هم‌زمان قابل افزودن است.');const id=state.nextId++;f=makeFunction(expr,id,colorFor(id));state.functions.push(f);}
 }catch(err){$('equationError').textContent=err.message;return;}
 state.activeId=f.id;resetEditing();setTab('controls');renderAll();saveCurrent();drawSoon();toast('نمودار اضافه یا به‌روزرسانی شد.');
});
document.querySelectorAll('[data-example]').forEach(b=>b.onclick=()=>{$('equationInput').value=b.dataset.example;$('equationError').textContent='';$('equationInput').focus();});
function askConfirm(title,text,action){confirmAction=action;$('confirmTitle').textContent=title;$('confirmText').textContent=text;$('confirmDialog').showModal();}
$('cancelConfirm').onclick=()=>{$('confirmDialog').close();confirmAction=null;};
$('acceptConfirm').onclick=()=>{$('confirmDialog').close();const fn=confirmAction;confirmAction=null;fn?.();};
$('clearAllButton').onclick=()=>{if(!state.functions.length)return;askConfirm('پاک کردن همهٔ نمودارها','تمام نمودارهای پروژهٔ فعلی حذف شوند؟ پروژه‌های جداگانه ذخیره‌شده باقی می‌مانند.',()=>{state.functions=[];state.activeId=null;liveCache.clear();renderAll();saveCurrent();drawSoon();toast('صفحه پاک شد.');});};
function renderLegend(){const el=$('legend');el.replaceChildren();for(const f of state.functions){if(!f.visible)continue;const chip=document.createElement('span');chip.className='legend-chip';const dot=document.createElement('i');dot.className='legend-dot';dot.style.background=f.color;chip.append(dot,document.createTextNode(descriptor(f)));el.append(chip);} $('visibleCount').textContent=persian(state.functions.filter(f=>f.visible).length)+' نمودار';}
function renderAll(){renderPills();renderActive();renderLegend();}
function timeLabel(s){try{return new Date(s).toLocaleString('fa-IR',{dateStyle:'medium',timeStyle:'short'});}catch{return s;}}
function renderSaves(){const box=$('savedProjects');box.replaceChildren();if(!saves.length){const p=document.createElement('p');p.className='no-functions';p.textContent='هنوز پروژه‌ای به‌صورت جداگانه ذخیره نشده است.';box.append(p);return;}
 for(const obj of saves){const card=document.createElement('article');card.className='save-item';const title=document.createElement('div');title.className='save-item-head';const strong=document.createElement('strong');strong.textContent=obj.name;title.append(strong);const date=document.createElement('div');date.className='save-date';date.textContent=timeLabel(obj.date)+' · '+persian(obj.model?.functions?.length||0)+' نمودار';const actions=document.createElement('div');actions.className='save-item-actions';for(const [act,txt] of [['load','باز کردن'],['download','↓ JSON'],['delete','حذف']]){const b=document.createElement('button');b.type='button';b.className=act==='delete'?'text-btn danger-text':'small-btn';b.textContent=txt;b.dataset.saveAction=act;b.dataset.id=obj.id;actions.append(b);}card.append(title,date,actions);box.append(card);}
}
function addSave(){const name=$('saveName').value.trim()||'پروژهٔ '+timeLabel(new Date().toISOString());const obj={id:Date.now().toString(36)+'-'+Math.random().toString(36).slice(2,7),name,date:new Date().toISOString(),model:snapshot()};saves.unshift(obj);saves=saves.slice(0,30);if(!writeSaves())return;saves=readSaves();$('saveName').value='';renderSaves();toast('پروژه در حافظهٔ همین مرورگر ذخیره شد.');}
$('saveProjectButton').onclick=addSave;
$('quickSaveButton').onclick=()=>{setTab('saves');$('saveName').focus();toast('نام پروژه را وارد کن و «ذخیره» را بزن.');};
$('savedProjects').addEventListener('click',e=>{const b=e.target.closest('[data-save-action]');if(!b)return;const item=saves.find(s=>s.id===b.dataset.id);if(!item)return;
 if(b.dataset.saveAction==='load'){try{loadSnapshot(item.model);setTab('controls');toast('پروژه بازیابی شد.');}catch(err){toast('خطا در باز کردن پروژه: '+err.message);}}
 else if(b.dataset.saveAction==='download'){downloadJSON({kind:'konkur-graph-project',version:2,project:item.model},safeName(item.name)+'.json');}
 else if(b.dataset.saveAction==='delete')askConfirm('حذف نسخهٔ ذخیره‌شده',`پروژهٔ «${item.name}» از حافظه حذف شود؟`,()=>{saves=saves.filter(s=>s.id!==item.id);writeSaves();renderSaves();toast('نسخهٔ ذخیره‌شده حذف شد.');});
});
function safeName(s){return s.replace(/[\\/:*?"<>|]/g,'_').slice(0,70)||'konkur-graph';}
function downloadJSON(data,name){const blob=new Blob([JSON.stringify(data,null,2)],{type:'application/json;charset=utf-8'}),url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),2500);}
$('exportJsonButton').onclick=()=>{downloadJSON({kind:'konkur-graph-backup',version:2,current:snapshot(),saves},'konkur-graph-backup.json');toast('فایل پشتیبان آماده شد.');};
$('importJsonInput').addEventListener('change',async e=>{const file=e.target.files?.[0];e.target.value='';if(!file)return;
 try{if(file.size>1000000)throw Error('فایل بیش از حد بزرگ است.');const data=JSON.parse(await file.text());const model=data.kind==='konkur-graph-project'?data.project:data.kind==='konkur-graph-backup'?data.current:data;
 const checked=parseSafeModel(model);if(data.kind==='konkur-graph-backup'&&Array.isArray(data.saves)){
  const imported=[];for(const s of data.saves.slice(0,30)){if(typeof s.name!=='string'||typeof s.id!=='string')continue;try{parseSafeModel(s.model);imported.push({id:s.id,name:s.name.slice(0,95),date:s.date||new Date().toISOString(),model:s.model});}catch{}}
  saves=imported;writeSaves();
 }
 loadSnapshot(checked);setTab('controls');toast('پروژه از فایل JSON بازیابی شد.');
 }catch(err){toast('بازیابی انجام نشد: '+err.message);}
});
function updateRoots(){const f=state.functions.find(f=>f.id===state.activeId),el=$('rootsReadout');if(!f||!el||modeOf(f)!=='equality')return;const roots=findRoots(f);el.textContent='ریشه‌های تقریبی در بازهٔ قابل مشاهده: '+(roots.length?roots.map(formatNumber).join('، '):'ریشه‌ای دیده نشد');}

// Plotting engine: domain breaks and vertical asymptotes are not joined.
const worldX=px=>(px-W/2)/state.viewport.sx+state.viewport.cx;
const worldY=py=>(H/2-py)/state.viewport.sy+state.viewport.cy;
const screenX=x=>W/2+(x-state.viewport.cx)*state.viewport.sx;
const screenY=y=>H/2-(y-state.viewport.cy)*state.viewport.sy;
function chartColors(){const cs=getComputedStyle(document.documentElement);const val=k=>cs.getPropertyValue(k).trim();return {bg:val('--chart'),grid:val('--grid'),axis:val('--axis'),tick:val('--tick')};}
function niceStep(raw){let e=Math.pow(10,Math.floor(Math.log10(Math.max(raw,1e-20)))),v=raw/e;return (v<=1?1:v<=2?2:v<=5?5:10)*e;}
function drawGrid(colors){const v=state.viewport,x0=worldX(0),x1=worldX(W),y0=worldY(H),y1=worldY(0),dx=niceStep(65/v.sx),dy=niceStep(55/v.sy),ax=screenX(0),ay=screenY(0);ctx.save();ctx.strokeStyle=colors.grid;ctx.lineWidth=1;ctx.beginPath();
 for(let x=Math.ceil(x0/dx)*dx,n=0;x<=x1+dx/10000&&n<140;x+=dx,n++){let px=screenX(x);ctx.moveTo(px,0);ctx.lineTo(px,H);}
 for(let y=Math.ceil(y0/dy)*dy,n=0;y<=y1+dy/10000&&n<140;y+=dy,n++){let py=screenY(y);ctx.moveTo(0,py);ctx.lineTo(W,py);}ctx.stroke();
 ctx.strokeStyle=colors.axis;ctx.lineWidth=1.5;ctx.beginPath();if(ax>=0&&ax<=W){ctx.moveTo(ax,0);ctx.lineTo(ax,H);}if(ay>=0&&ay<=H){ctx.moveTo(0,ay);ctx.lineTo(W,ay);}ctx.stroke();
 ctx.fillStyle=colors.tick;ctx.font='11px Consolas,monospace';ctx.direction='ltr';ctx.textAlign='center';ctx.textBaseline='top';
 for(let x=Math.ceil(x0/dx)*dx,n=0;x<=x1+dx/10000&&n<140;x+=dx,n++)if(Math.abs(x)>dx/100&&screenX(x)>22&&screenX(x)<W-22)ctx.fillText(formatNumber(x),screenX(x),Math.max(5,Math.min(H-17,ay+5)));
 ctx.textAlign='right';ctx.textBaseline='middle';for(let y=Math.ceil(y0/dy)*dy,n=0;y<=y1+dy/10000&&n<140;y+=dy,n++)if(Math.abs(y)>dy/100&&screenY(y)>13&&screenY(y)<H-13)ctx.fillText(formatNumber(y),Math.min(W-8,Math.max(29,ax-7)),screenY(y));ctx.restore();}
function findRoots(f){const x0=worldX(0),x1=worldX(W),n=Math.max(300,Math.min(1300,Math.floor(W*1.5))),roots=[],step=(x1-x0)/n;
 const add=r=>{if(!Number.isFinite(r)||r<x0||r>x1)return;if(!roots.some(z=>Math.abs(z-r)<Math.max(step*2,.00001)))roots.push(r);};
 let xp=x0,yp=difference(f,xp);let pp=NaN;
 for(let i=1;i<=n;i++){
  const x=x0+i*step,y=difference(f,x);
  if(Number.isFinite(y)&&Math.abs(y)<Math.max(1e-8,step*step*.03))add(x);
  if(Number.isFinite(yp)&&Number.isFinite(y)&&Math.sign(yp)!==Math.sign(y)&&Math.abs(yp)<1e8&&Math.abs(y)<1e8){
   let lo=xp,hi=x,flo=yp;
   for(let j=0;j<34;j++){const mid=(lo+hi)/2,fm=difference(f,mid);if(!Number.isFinite(fm)){lo=mid;continue;}if(Math.sign(fm)===Math.sign(flo)){lo=mid;flo=fm;}else hi=mid;}
   const r=(lo+hi)/2,val=difference(f,r);
   if(Number.isFinite(val)&&Math.abs(val)<.0005)add(r);
  }
  if(Number.isFinite(pp)&&Number.isFinite(yp)&&Number.isFinite(y)&&Math.abs(yp)<Math.abs(pp)&&Math.abs(yp)<Math.abs(y)&&Math.abs(yp)<step*step*.05)add(xp);
  pp=yp;yp=y;xp=x;
 }return roots.sort((a,b)=>a-b).slice(0,50);
}
function drawYRegion(f,comp){const rel=comp.relation,above=rel==='>'||rel==='>=';ctx.save();ctx.fillStyle=f.color;ctx.globalAlpha=.13;const step=2.5;
 for(let px=0;px<=W;px+=step){const val=evalCurve(f,worldX(px));if(!Number.isFinite(val))continue;
  const y=screenY(val),edge=Math.min(H,Math.max(0,y));ctx.fillRect(px,above?0:edge,step+1,above?edge:H-edge);
 }ctx.restore();}
function drawXRegion(f){ctx.save();ctx.fillStyle=f.color;ctx.globalAlpha=.14;const step=2.5;for(let px=0;px<W;px+=step){const comp=compile(f),x=worldX(px+step/2),a=evaluateNode(comp.ast.left,f,x,comp),b=evaluateNode(comp.ast.right,f,x,comp);
  if(relationHolds(comp.relation,a,b))ctx.fillRect(px,0,step+1,H);
 }ctx.restore();drawRootMarkers(f,findRoots(f),true);}
function drawRootMarkers(f,roots,isBoundary){ctx.save();ctx.strokeStyle=f.color;ctx.fillStyle=f.color;ctx.lineWidth=1.4;ctx.setLineDash(isBoundary?[4,5]:[3,5]);
 for(const r of roots){const x=screenX(r);ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,H);ctx.stroke();
  if(!isBoundary){const y=screenY(0);if(y>=4&&y<=H-4){ctx.setLineDash([]);ctx.beginPath();ctx.arc(x,y,5,0,2*Math.PI);ctx.fill();ctx.setLineDash([3,5]);}}
 }ctx.restore();}
function drawCurve(f){ctx.save();ctx.strokeStyle=f.color;ctx.lineWidth=2.8;ctx.lineCap='round';ctx.lineJoin='round';ctx.beginPath();let last=null,part=false;
 const incr=W>1600?2:1.5;
 for(let px=0;px<=W+incr;px+=incr){const y=evalCurve(f,worldX(px)),py=screenY(y);
  const finite=Number.isFinite(py)&&Math.abs(py)<H*12;
  if(!finite){last=null;part=false;continue;}
  const discontinuity=last&&((Math.abs(py-last.py)>Math.max(H*.8,320)&&Math.sign(py-H/2)!==Math.sign(last.py-H/2))||(last.y*y<0&&Math.abs(last.y)>H/state.viewport.sy*.5&&Math.abs(y)>H/state.viewport.sy*.5));
  if(!part||discontinuity)ctx.moveTo(px,py);else ctx.lineTo(px,py);last={y,py};part=true;
 }
 ctx.stroke();ctx.restore();}
function drawChart(withPointer=true){if(W<25||H<25)return;const dpr=canvas.width/W;ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,W,H);const cs=chartColors();ctx.fillStyle=cs.bg;ctx.fillRect(0,0,W,H);drawGrid(cs);
 ctx.save();ctx.beginPath();ctx.rect(0,0,W,H);ctx.clip();
 for(const f of state.functions){if(!f.visible)continue;const mode=modeOf(f);if(mode==='yshade')drawYRegion(f,compile(f));else if(mode==='xshade')drawXRegion(f);}
 for(const f of state.functions){if(!f.visible)continue;const mode=modeOf(f);if(mode==='curve'||mode==='yshade')drawCurve(f);else if(mode==='equality')drawRootMarkers(f,findRoots(f),false);}
 if(withPointer&&pointer){const px=screenX(pointer.x),py=screenY(pointer.y);ctx.strokeStyle=cs.axis;ctx.lineWidth=1;ctx.setLineDash([3,5]);ctx.beginPath();ctx.moveTo(px,0);ctx.lineTo(px,H);ctx.moveTo(0,py);ctx.lineTo(W,py);ctx.stroke();ctx.setLineDash([]);}
 ctx.restore();$('scaleInfo').textContent=`x: ${formatNumber(W/state.viewport.sx)} · y: ${formatNumber(H/state.viewport.sy)}`;
}
function drawSoon(){if(frame)return;frame=true;requestAnimationFrame(()=>{frame=false;drawChart();});}
function fit(){if(W<20||H<20)return;const visible=state.functions.filter(f=>f.visible);const xspan=visible.some(f=>f.kind==='poly'&&f.degree>=4)?8:12;
 let yy=[];for(const f of visible){const type=modeOf(f);if(type!=='curve'&&type!=='yshade')continue;
  for(let i=0;i<201;i++){const y=evalCurve(f,(i/200-.5)*xspan);if(Number.isFinite(y)&&Math.abs(y)<1e7)yy.push(y);}
 }
 let min=-6,max=6;if(yy.length){yy.sort((a,b)=>a-b);const lo=yy[Math.floor(yy.length*.06)],hi=yy[Math.floor(yy.length*.94)];min=Math.min(0,lo);max=Math.max(0,hi);if(max-min<2){min-=2;max+=2;}const pad=(max-min)*.16;min-=pad;max+=pad;}
 state.viewport={cx:0,cy:(min+max)/2,sx:W/xspan,sy:Math.max(3,Math.min(2000,H/(max-min)))};saveCurrent();drawSoon();updateRoots();}
function zoomAt(factor,px,py,tx=px,ty=py){const x=worldX(px),y=worldY(py),v=state.viewport;v.sx=Math.min(2700,Math.max(2,v.sx*factor));v.sy=Math.min(2700,Math.max(2,v.sy*factor));v.cx=x-(tx-W/2)/v.sx;v.cy=y+(ty-H/2)/v.sy;drawSoon();saveCurrent();updateRoots();}
$('zoomInButton').onclick=()=>zoomAt(1.3,W/2,H/2);
$('zoomOutButton').onclick=()=>zoomAt(1/1.3,W/2,H/2);
$('fitButton').onclick=()=>{fit();toast('محدودهٔ نمودار تنظیم شد.');};
$('exportButton').onclick=()=>{drawChart(false);try{const a=document.createElement('a');a.download='konkur-graph-'+new Date().toISOString().slice(0,10)+'.png';a.href=canvas.toDataURL('image/png');a.click();toast('تصویر PNG آمادهٔ ذخیره است.');}catch{toast('دریافت تصویر در این مرورگر ممکن نشد.');}drawSoon();};
function resize(){const r=stage.getBoundingClientRect();if(r.width<25||r.height<25)return;const nW=Math.round(r.width),nH=Math.round(r.height),dpr=Math.min(devicePixelRatio||1,3);if(canvas.width!==Math.round(nW*dpr)||canvas.height!==Math.round(nH*dpr)){canvas.width=Math.round(nW*dpr);canvas.height=Math.round(nH*dpr);}W=nW;H=nH;if(!initialFit){initialFit=true;if(!initial)fit();}drawSoon();}
function relPoint(e){const r=canvas.getBoundingClientRect();return {x:e.clientX-r.left,y:e.clientY-r.top};}
function updateCursor(p){pointer={x:worldX(p.x),y:worldY(p.y)};$('cursorLabel').textContent=`x: ${formatNumber(pointer.x)}  y: ${formatNumber(pointer.y)}`;drawSoon();}
canvas.addEventListener('wheel',e=>{e.preventDefault();const p=relPoint(e);zoomAt(Math.exp(-Math.max(-200,Math.min(200,e.deltaY))*.0018),p.x,p.y);},{passive:false});
canvas.addEventListener('pointerdown',e=>{if(e.pointerType==='mouse'&&e.button!==0)return;canvas.setPointerCapture(e.pointerId);dragPointers.set(e.pointerId,relPoint(e));if(e.pointerType!=='touch')updateCursor(relPoint(e));});
canvas.addEventListener('pointermove',e=>{const p=relPoint(e);if(dragPointers.has(e.pointerId)){
 const before=[...dragPointers.values()].map(p=>({...p}));dragPointers.set(e.pointerId,p);const after=[...dragPointers.values()];
 if(after.length===1){state.viewport.cx-=(p.x-before[0].x)/state.viewport.sx;state.viewport.cy+=(p.y-before[0].y)/state.viewport.sy;}
 else if(after.length>=2){const old=before.slice(0,2),now=after.slice(0,2),oldM={x:(old[0].x+old[1].x)/2,y:(old[0].y+old[1].y)/2},newM={x:(now[0].x+now[1].x)/2,y:(now[0].y+now[1].y)/2};
 const od=Math.hypot(old[0].x-old[1].x,old[0].y-old[1].y),nd=Math.hypot(now[0].x-now[1].x,now[0].y-now[1].y);if(od>10&&nd>10)zoomAt(nd/od,oldM.x,oldM.y,newM.x,newM.y);}
 if(e.pointerType!=='touch')updateCursor(p);drawSoon();
 }else if(e.pointerType!=='touch')updateCursor(p);});
const stopPointer=e=>{if(dragPointers.has(e.pointerId)){dragPointers.delete(e.pointerId);saveCurrent();updateRoots();}if(e.pointerType==='touch'&&!dragPointers.size){pointer=null;drawSoon();}};
canvas.addEventListener('pointerup',stopPointer);canvas.addEventListener('pointercancel',stopPointer);canvas.addEventListener('pointerleave',()=>{if(!dragPointers.size){pointer=null;$('cursorLabel').textContent='x: —   y: —';drawSoon();}});
canvas.tabIndex=0;canvas.addEventListener('keydown',e=>{let changed=true;switch(e.key){case '+':case '=':zoomAt(1.25,W/2,H/2);break;case '-':zoomAt(.8,W/2,H/2);break;case 'Home':fit();break;case 'ArrowLeft':state.viewport.cx-=40/state.viewport.sx;break;case 'ArrowRight':state.viewport.cx+=40/state.viewport.sx;break;case 'ArrowUp':state.viewport.cy+=40/state.viewport.sy;break;case 'ArrowDown':state.viewport.cy-=40/state.viewport.sy;break;default:changed=false;}if(changed){e.preventDefault();saveCurrent();drawSoon();}});
function applyTheme(){document.documentElement.dataset.theme=state.theme;$('themeButton').firstChild.textContent=state.theme==='dark'?'☀ ':'☾ ';$('themeLabel').textContent=state.theme==='dark'?'روشن':'تاریک';document.querySelector('meta[name="theme-color"]').content=state.theme==='dark'?'#0d1b29':'#0f766e';drawSoon();}
$('themeButton').onclick=()=>{state.theme=state.theme==='dark'?'light':'dark';try{localStorage.setItem(THEME_KEY,state.theme);}catch{}applyTheme();};
function connection(){const offline=!navigator.onLine;$('network').title=offline?'بدون اینترنت؛ نمودارها قابل استفاده‌اند':'برنامه برای کار به اینترنت وابسته نیست';document.querySelector('.network-label').textContent=offline?'آفلاین':'آماده';}
window.addEventListener('online',connection);window.addEventListener('offline',connection);
window.addEventListener('beforeinstallprompt',e=>{e.preventDefault();installPrompt=e;$('installButton').hidden=false;});
$('installButton').onclick=async()=>{if(!installPrompt){toast('از منوی مرورگر «افزودن به صفحهٔ اصلی» را بزن.');return;}await installPrompt.prompt();installPrompt=null;};
window.addEventListener('appinstalled',()=>{$('installButton').hidden=true;toast('برنامه نصب شد.');});
if('serviceWorker' in navigator&&(location.protocol==='https:'||['localhost','127.0.0.1'].includes(location.hostname))){window.addEventListener('load',()=>navigator.serviceWorker.register('./sw.js').catch(()=>{}));}
applyTheme();connection();renderAll();saveCurrent();if(typeof ResizeObserver!=='undefined')new ResizeObserver(resize).observe(stage);window.addEventListener('resize',resize);resize();
})();
