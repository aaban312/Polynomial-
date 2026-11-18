(() => {
  'use strict';

  const STORAGE_KEY = 'polynomial-workshop-data-v1';
  const PALETTE = ['#0c9a86', '#705cf3', '#ef7952', '#df4a91', '#258cc8', '#c39e24', '#9656ac', '#d35d56'];
  const SUPERSCRIPT = ['', '', '²', '³', '⁴', '⁵'];
  const $ = id => document.getElementById(id);
  const canvas = $('graphCanvas');
  const ctx = canvas.getContext('2d');
  const stage = $('graphStage');
  const functionList = $('functionList');
  const input = $('equationInput');
  const error = $('equationError');
  const form = $('equationForm');
  const stored = readState();

  const state = {
    functions: stored ? stored.functions : [{id: 1, degree: 1, coeffs: [5, 2], color: PALETTE[0], visible: true}],
    nextId: stored ? stored.nextId : 2,
    viewport: stored ? stored.viewport : {cx: 0, cy: 0, sx: 45, sy: 45},
    expandedId: null,
    editingId: null
  };
  state.expandedId = state.functions.length ? state.functions[0].id : null;
  let frameQueued = false;
  let viewportInitialized = !!stored;
  let pointerCursor = null;
  let toastTimer;
  let installPrompt = null;
  let width = 800;
  let height = 500;
  const activePointers = new Map();

  function readState() {
    try {
      const value = JSON.parse(localStorage.getItem(STORAGE_KEY));
      if (!value || !Array.isArray(value.functions) || value.functions.length > 80) return null;
      const functions = value.functions.map(item => {
        if (!Number.isSafeInteger(item.id) || item.id <= 0 || !Number.isInteger(item.degree) || item.degree < 1 || item.degree > 5 ||
            !Array.isArray(item.coeffs) || item.coeffs.length !== item.degree + 1 ||
            !item.coeffs.every(n => typeof n === 'number' && Number.isFinite(n) && Math.abs(n) <= 1e7)) throw Error('Invalid data');
        return {id: item.id, degree: item.degree, coeffs: [...item.coeffs], color: validColor(item.color) ? item.color : PALETTE[0], visible: item.visible !== false};
      });
      const v = value.viewport;
      const viewport = v && [v.cx,v.cy,v.sx,v.sy].every(n => typeof n === 'number' && Number.isFinite(n)) && v.sx >= 3 && v.sx <= 2000 && v.sy >= 3 && v.sy <= 2000
        ? {cx:v.cx, cy:v.cy, sx:v.sx, sy:v.sy}
        : {cx:0,cy:0,sx:45,sy:45};
      const maxId = Math.max(0, ...functions.map(f => f.id));
      return {functions, viewport, nextId: Math.max(maxId + 1, Number.isSafeInteger(value.nextId) ? value.nextId : 1)};
    } catch { return null; }
  }

  function validColor(c) { return typeof c === 'string' && /^#[0-9a-fA-F]{6}$/.test(c); }
  function persist() {
    try {
      localStorage.setItem(STORAGE_KEY, JSON.stringify({functions:state.functions, viewport:state.viewport, nextId:state.nextId}));
    } catch { /* App still works when storage is disabled. */ }
  }

  function normalizeEquation(expression) {
    let text = String(expression).trim()
      .replace(/[۰-۹]/g, digit => String('۰۱۲۳۴۵۶۷۸۹'.indexOf(digit)))
      .replace(/[٠-٩]/g, digit => String('٠١٢٣٤٥٦٧٨٩'.indexOf(digit)))
      .replace(/[−–—]/g, '-').replace(/[＋]/g, '+')
      .replace(/[٫،,]/g, '.').replace(/[×·]/g, '*')
      .replace(/[X]/g, 'x').replace(/\s+/g, '')
      .replace(/x([¹²³⁴⁵])/g, (_, exponent) => `x^${'¹²³⁴⁵'.indexOf(exponent) + 1}`)
      .replace(/(\d|\.)\*x/g, '$1x');
    const equalIndex = text.indexOf('=');
    if (equalIndex >= 0) {
      const left = text.slice(0, equalIndex).toLowerCase();
      const right = text.slice(equalIndex + 1);
      if (right.includes('=')) throw new Error('فقط یک علامت مساوی مجاز است.');
      if (['y','f(x)','p(x)'].includes(left)) text = right;
      else if (right === '0') text = left;
      else throw new Error('عبارت را به صورت y=... یا فقط چندجمله‌ای بنویسید.');
    }
    return text;
  }

  function parsePolynomial(expression) {
    const text = normalizeEquation(expression);
    if (!text) throw new Error('لطفاً یک عبارت وارد کنید.');
    if (/x\^[6-9]|x\^\d{2,}/.test(text)) throw new Error('فقط توان‌های صفر تا پنج پشتیبانی می‌شوند.');
    if (!/^[0-9x+\-.*^]+$/.test(text)) throw new Error('فقط عدد، x، +، − و توان ^ مجاز هستند.');
    if (/[+\-]$/.test(text)) throw new Error('عبارت نباید به علامت + یا − ختم شود.');

    const terms = text.replace(/-/g, '+-').split('+').filter(Boolean);
    const coefficients = Array(6).fill(0);
    for (let term of terms) {
      let sign = 1;
      if (term.startsWith('-')) { sign = -1; term = term.slice(1); }
      if (!term) throw new Error('علامت‌های عبارت را بررسی کنید.');
      const variable = term.match(/^((?:\d+(?:\.\d*)?|\.\d+)?)x(?:\^(\d+))?$/);
      let power, magnitude;
      if (variable) {
        power = variable[2] === undefined ? 1 : Number(variable[2]);
        if (power > 5) throw new Error('درجهٔ تابع نباید بیشتر از پنج باشد.');
        magnitude = variable[1] ? Number(variable[1]) : 1;
      } else if (/^(?:\d+(?:\.\d*)?|\.\d+)$/.test(term)) {
        power = 0;
        magnitude = Number(term);
      } else {
        throw new Error('قالب عبارت صحیح نیست. نمونهٔ درست: 2x^2-3x+5');
      }
      if (!Number.isFinite(magnitude) || Math.abs(magnitude) > 1e7) throw new Error('ضریب واردشده بیش از حد بزرگ است.');
      coefficients[power] += sign * magnitude;
      if (Math.abs(coefficients[power]) > 1e7) throw new Error('مقدار نهایی یک ضریب بیش از حد بزرگ است.');
    }
    let degree = 1;
    for (let p = 5; p >= 1; p--) if (Math.abs(coefficients[p]) > 1e-10) { degree = p; break; }
    return {degree, coeffs:coefficients.slice(0,degree+1)};
  }

  function formatNumber(n) {
    if (Math.abs(n) < 0.0000005) return '0';
    if (Math.abs(n) >= 1e6 || Math.abs(n) < 0.0001) return Number(n.toPrecision(5)).toString();
    return String(Number(n.toFixed(5)));
  }
  function formulaOf(f) {
    const pieces = [];
    for (let power = f.degree; power >= 0; power--) {
      const coefficient = f.coeffs[power];
      if (Math.abs(coefficient) < 1e-10) continue;
      const absolute = Math.abs(coefficient);
      const value = power !== 0 && Math.abs(absolute - 1) < 1e-10 ? '' : formatNumber(absolute);
      const term = power === 0 ? formatNumber(absolute) : `${value}x${power > 1 ? '^' + power : ''}`;
      pieces.push((pieces.length === 0 ? (coefficient < 0 ? '-' : '') : (coefficient < 0 ? ' - ' : ' + ')) + term);
    }
    return pieces.join('') || '0';
  }
  function evaluate(f, x) {
    let y = f.coeffs[f.degree];
    for (let p = f.degree - 1; p >= 0; p--) y = y * x + f.coeffs[p];
    return y;
  }
  function findFunction(id) { return state.functions.find(f => f.id === id); }
  function labelFor(degree, power) { return String.fromCharCode(97 + degree - power); }
  function termFor(power) { return power === 0 ? 'ثابت' : power === 1 ? 'x' : 'x' + SUPERSCRIPT[power]; }
  function sliderBound(value) { return Math.min(1e7, Math.max(10, Math.ceil(Math.abs(value) / 5) * 5 + 5)); }
  function sliderFill(slider) {
    const fraction = (Number(slider.value) - Number(slider.min)) / (Number(slider.max) - Number(slider.min)) * 100;
    slider.style.background = `linear-gradient(to right, var(--curve-color) ${fraction}%, #e7edef ${fraction}%)`;
  }

  function buildCard(f) {
    const card = document.createElement('article');
    const isExpanded = state.expandedId === f.id;
    card.className = `function-card${isExpanded ? ' expanded' : ''}${f.visible ? '' : ' is-hidden'}`;
    card.style.setProperty('--curve-color', f.color);
    card.dataset.id = String(f.id);
    const header = document.createElement('div');
    header.className = 'function-card-head';
    header.innerHTML = `
      <div class="function-name"><span class="function-swatch" aria-hidden="true"></span><div>
        <span class="function-id">تابع ${f.id} <small style="font-size:10px;color:#9ba9ac;font-weight:500">(درجهٔ ${toPersian(f.degree)})</small></span>
        <span class="function-formula" dir="ltr"></span>
      </div></div>
      <div class="function-tools">
        <label class="color-label" title="تغییر رنگ تابع"><input class="color-control" type="color" value="${f.color}" data-id="${f.id}" aria-label="رنگ تابع ${f.id}"></label>
        <button type="button" class="function-icon" data-action="visibility" data-id="${f.id}" aria-label="${f.visible ? 'پنهان کردن' : 'نمایش'} تابع ${f.id}" title="${f.visible ? 'پنهان کردن' : 'نمایش'} نمودار">${f.visible ? '◉' : '◌'}</button>
        <button type="button" class="function-icon" data-action="edit" data-id="${f.id}" aria-label="ویرایش تابع ${f.id}" title="ویرایش عبارت">✎</button>
        <button type="button" class="function-icon delete" data-action="delete" data-id="${f.id}" aria-label="حذف تابع ${f.id}" title="حذف تابع">×</button>
      </div>`;
    header.querySelector('.function-formula').textContent = 'y = ' + formulaOf(f);
    card.appendChild(header);
    const toggle = document.createElement('button');
    toggle.type = 'button';
    toggle.className = 'coefficients-toggle';
    toggle.dataset.action = 'expand';
    toggle.dataset.id = f.id;
    toggle.setAttribute('aria-expanded', String(isExpanded));
    toggle.innerHTML = `<span>${isExpanded ? 'بستن' : 'نمایش'} تنظیمات ضرایب</span><span class="chevron" aria-hidden="true">⌄</span>`;
    card.appendChild(toggle);
    if (isExpanded) {
      const body = document.createElement('div');
      body.className = 'coefficients';
      for (let p = f.degree; p >= 0; p--) {
        const value = f.coeffs[p];
        const bound = sliderBound(value);
        const row = document.createElement('div');
        row.className = 'coeff-row';
        row.dataset.power = String(p);
        row.innerHTML = `
          <div class="coeff-meta"><label class="coeff-label" for="coeff-${f.id}-${p}"><span class="coeff-letter">${labelFor(f.degree,p)}</span><span class="coeff-term">${termFor(p)}</span></label>
          <input class="coeff-number" id="coeff-${f.id}-${p}" data-id="${f.id}" data-power="${p}" type="number" step="any" min="-10000000" max="10000000" inputmode="decimal" aria-label="مقدار ضریب ${labelFor(f.degree,p)}"></div>
          <div class="slider-line"><span class="range-limit">-${bound}</span>
          <input class="coeff-slider" type="range" min="${-bound}" max="${bound}" step="0.1" data-id="${f.id}" data-power="${p}" aria-label="اهرم ضریب ${labelFor(f.degree,p)}">
          <span class="range-limit">+${bound}</span></div>`;
        row.querySelector('.coeff-number').value = String(value);
        const slider = row.querySelector('.coeff-slider');
        slider.value = String(value);
        sliderFill(slider);
        body.appendChild(row);
      }
      card.appendChild(body);
    }
    return card;
  }
  function toPersian(value) { return String(value).replace(/\d/g, ch => '۰۱۲۳۴۵۶۷۸۹'[Number(ch)]); }
  function renderFunctions() {
    const fragment = document.createDocumentFragment();
    for (const f of state.functions) fragment.appendChild(buildCard(f));
    functionList.replaceChildren(fragment);
    $('functionCount').textContent = toPersian(state.functions.length);
    $('emptyMessage').hidden = state.functions.length > 0;
    $('clearAllButton').disabled = state.functions.length === 0;
    renderLegend();
  }
  function renderLegend() {
    const root = $('graphLegend');
    root.replaceChildren();
    for (const f of state.functions) {
      const item = document.createElement('div');
      item.className = 'legend-item';
      item.style.opacity = f.visible ? '1' : '.48';
      item.dataset.functionId = String(f.id);
      const dot = document.createElement('i'); dot.className = 'legend-dot'; dot.style.background = f.color;
      const name = document.createElement('span'); name.textContent = `تابع ${toPersian(f.id)}`;
      const sample = document.createElement('span'); sample.className = 'legend-value'; sample.dir = 'ltr';
      item.append(dot, name, sample);
      root.appendChild(item);
    }
    updateLegendHover();
  }
  function updateLegendHover() {
    for (const el of $('graphLegend').querySelectorAll('[data-function-id]')) {
      const f = findFunction(Number(el.dataset.functionId));
      const value = el.querySelector('.legend-value');
      const y = pointerCursor && f && f.visible ? evaluate(f, pointerCursor.x) : null;
      value.textContent = y === null || !Number.isFinite(y) ? '' : '= ' + formatNumber(y);
    }
  }
  function updateInputMode() {
    $('submitText').textContent = state.editingId === null ? 'افزودن به نمودار' : 'ثبت تغییرات';
    $('cancelEditButton').hidden = state.editingId === null;
  }
  function resetEditing() { state.editingId = null; input.value = ''; error.textContent = ''; updateInputMode(); }

  form.addEventListener('submit', event => {
    event.preventDefault();
    let parsed;
    try { parsed = parsePolynomial(input.value); }
    catch (err) { error.textContent = err.message; input.focus(); return; }
    if (state.editingId !== null) {
      const f = findFunction(state.editingId);
      if (f) {f.degree = parsed.degree; f.coeffs = parsed.coeffs; state.expandedId = f.id; showToast('تابع با موفقیت ویرایش شد.');}
    } else {
      const id = state.nextId++;
      state.functions.push({...parsed, id, color:PALETTE[(id - 1) % PALETTE.length], visible:true});
      state.expandedId = id;
      if (state.functions.filter(f => f.visible).length === 1) fitGraph();
      showToast('نمودار جدید اضافه شد.');
    }
    resetEditing(); renderFunctions(); persist(); queueDraw();
  });
  input.addEventListener('input', () => { error.textContent = ''; });
  $('cancelEditButton').addEventListener('click', resetEditing);
  document.querySelectorAll('[data-example]').forEach(button => button.addEventListener('click', () => {
    input.value = button.dataset.example;
    error.textContent = '';
    input.focus();
  }));

  function setCoefficient(f, p, value) {
    if (!Number.isFinite(value) || Math.abs(value) > 1e7) return false;
    f.coeffs[p] = value;
    const card = [...functionList.children].find(el => Number(el.dataset.id) === f.id);
    if (card) {
      card.querySelector('.function-formula').textContent = 'y = ' + formulaOf(f);
      const row = [...card.querySelectorAll('.coeff-row')].find(el => Number(el.dataset.power) === p);
      if (row) {
        const number = row.querySelector('.coeff-number');
        const slider = row.querySelector('.coeff-slider');
        const currentBound = Math.max(Math.abs(Number(slider.min)), Math.abs(Number(slider.max)));
        const bound = Math.abs(value) > currentBound ? sliderBound(value) : currentBound;
        slider.min = -bound; slider.max = bound;
        row.querySelectorAll('.range-limit')[0].textContent = '-' + bound;
        row.querySelectorAll('.range-limit')[1].textContent = '+' + bound;
        slider.value = String(value);
        number.value = String(value);
        sliderFill(slider);
      }
    }
    updateLegendHover(); persist(); queueDraw();
    return true;
  }
  functionList.addEventListener('input', event => {
    const el = event.target;
    if (el.matches('.color-control')) {
      const f = findFunction(Number(el.dataset.id));
      if (f && validColor(el.value)) {
        f.color = el.value;
        const card = el.closest('.function-card'); card.style.setProperty('--curve-color', f.color);
        card.querySelector('.function-swatch').style.background = f.color;
        const dot = [...$('graphLegend').querySelectorAll('[data-function-id]')].find(n => Number(n.dataset.functionId) === f.id)?.querySelector('.legend-dot');
        if (dot) dot.style.background = f.color;
        card.querySelectorAll('.coeff-slider').forEach(sliderFill);
        persist(); queueDraw();
      }
      return;
    }
    if (!el.matches('.coeff-slider, .coeff-number')) return;
    if (el.classList.contains('coeff-number') && el.value.trim() === '') return;
    const f = findFunction(Number(el.dataset.id));
    if (!f) return;
    const value = Number(el.value);
    if (!setCoefficient(f, Number(el.dataset.power), value)) {
      if (el.classList.contains('coeff-number')) el.setCustomValidity('بازهٔ مجاز: منفی ده میلیون تا مثبت ده میلیون');
    } else el.setCustomValidity('');
  });
  functionList.addEventListener('change', event => {
    const el = event.target;
    if (!el.matches('.coeff-number')) return;
    const f = findFunction(Number(el.dataset.id));
    if (f) { el.setCustomValidity(''); setCoefficient(f, Number(el.dataset.power), f.coeffs[Number(el.dataset.power)]); }
  });
  functionList.addEventListener('click', event => {
    const button = event.target.closest('[data-action]');
    if (!button) return;
    const id = Number(button.dataset.id), action = button.dataset.action;
    const f = findFunction(id);
    if (!f) return;
    if (action === 'expand') { state.expandedId = state.expandedId === id ? null : id; renderFunctions(); }
    else if (action === 'visibility') { f.visible = !f.visible; renderFunctions(); persist(); queueDraw(); }
    else if (action === 'delete') {
      state.functions = state.functions.filter(item => item.id !== id);
      if (state.editingId === id) resetEditing();
      if (state.expandedId === id) state.expandedId = state.functions[0]?.id ?? null;
      renderFunctions(); persist(); queueDraw(); showToast('تابع حذف شد.');
    } else if (action === 'edit') {
      state.editingId = id; input.value = formulaOf(f).replace(/\s+/g, '');
      error.textContent = ''; updateInputMode(); input.focus(); input.scrollIntoView({behavior:'smooth',block:'nearest'});
    }
  });
  $('clearAllButton').addEventListener('click', () => {
    const dialog = $('clearDialog');
    if (typeof dialog.showModal === 'function') { dialog.returnValue = ''; dialog.showModal(); }
    else if (window.confirm('همهٔ توابع پاک شوند؟')) clearAll();
  });
  $('clearDialog').addEventListener('close', event => {
    if (event.target.returnValue === 'confirm') clearAll();
  });
  function clearAll() {
    state.functions = []; state.expandedId = null; resetEditing(); renderFunctions(); queueDraw(); persist(); showToast('همهٔ توابع پاک شدند.');
  }
  function showToast(message) {
    const el = $('toast');
    clearTimeout(toastTimer);
    el.textContent = message; el.classList.add('show');
    toastTimer = setTimeout(() => el.classList.remove('show'), 2100);
  }

  // A high-resolution, dependency-free Cartesian plotter.
  function resizeCanvas() {
    const rect = stage.getBoundingClientRect();
    if (rect.width < 30 || rect.height < 30) return;
    const newWidth = Math.round(rect.width), newHeight = Math.round(rect.height);
    const dpr = Math.min(window.devicePixelRatio || 1, 3);
    if (canvas.width !== Math.round(newWidth*dpr) || canvas.height !== Math.round(newHeight*dpr)) {
      canvas.width = Math.round(newWidth*dpr); canvas.height = Math.round(newHeight*dpr);
    }
    width = newWidth; height = newHeight;
    if (!viewportInitialized) {fitGraph(); viewportInitialized = true;}
    queueDraw();
  }
  function niceStep(rawStep) {
    const exponent = Math.pow(10, Math.floor(Math.log10(Math.max(rawStep,1e-12))));
    const mantissa = rawStep / exponent;
    return (mantissa <= 1 ? 1 : mantissa <= 2 ? 2 : mantissa <= 5 ? 5 : 10) * exponent;
  }
  const toScreenX = x => width/2 + (x - state.viewport.cx) * state.viewport.sx;
  const toScreenY = y => height/2 - (y - state.viewport.cy) * state.viewport.sy;
  const worldX = px => (px-width/2)/state.viewport.sx + state.viewport.cx;
  const worldY = py => (height/2-py)/state.viewport.sy + state.viewport.cy;
  function drawGrid() {
    const v = state.viewport;
    const left = worldX(0), right = worldX(width);
    const bottom = worldY(height), top = worldY(0);
    const stepX = niceStep(58 / v.sx), stepY = niceStep(52 / v.sy);
    const axisX = toScreenX(0), axisY = toScreenY(0);
    ctx.save();
    ctx.strokeStyle = '#ebf0f1';ctx.lineWidth = 1;
    ctx.beginPath();
    for (let x=Math.ceil(left/stepX)*stepX, n=0; x<=right+1e-8 && n<150; x+=stepX,n++) {
      const sx=toScreenX(x);ctx.moveTo(sx,0);ctx.lineTo(sx,height);
    }
    for (let y=Math.ceil(bottom/stepY)*stepY,n=0; y<=top+1e-8 && n<150; y+=stepY,n++) {
      const sy=toScreenY(y);ctx.moveTo(0,sy);ctx.lineTo(width,sy);
    }
    ctx.stroke();
    ctx.lineWidth=1.45;ctx.strokeStyle='#a5b7bb';ctx.beginPath();
    if (axisX>=0 && axisX<=width) {ctx.moveTo(axisX,0);ctx.lineTo(axisX,height);}
    if (axisY>=0 && axisY<=height) {ctx.moveTo(0,axisY);ctx.lineTo(width,axisY);}
    ctx.stroke();
    ctx.fillStyle='#90a1a7';ctx.font='11px ui-monospace, Consolas, monospace';ctx.direction='ltr';
    ctx.textAlign='center';ctx.textBaseline='top';
    const xLabelY=Math.max(5,Math.min(height-19,axisY+7));
    for (let x=Math.ceil(left/stepX)*stepX,n=0;x<=right+1e-8 && n<150;x+=stepX,n++) {
      if (Math.abs(x)<stepX/100) continue;
      const sx=toScreenX(x);if(sx>22&&sx<width-22)ctx.fillText(formatTick(x),sx,xLabelY);
    }
    ctx.textAlign='right';ctx.textBaseline='middle';
    const yLabelX=Math.min(width-8,Math.max(36,axisX-8));
    for (let y=Math.ceil(bottom/stepY)*stepY,n=0;y<=top+1e-8 && n<150;y+=stepY,n++) {
      if(Math.abs(y)<stepY/100)continue;
      const sy=toScreenY(y);if(sy>12&&sy<height-12)ctx.fillText(formatTick(y),yLabelX,sy);
    }
    if(axisX>10&&axisX<width-10&&axisY>10&&axisY<height-10){ctx.fillText('0',axisX-9,axisY+11);}
    ctx.restore();
  }
  function formatTick(n) {
    if (Math.abs(n)<1e-9) return '0';
    if (Math.abs(n)>=10000 || Math.abs(n)<0.001) return n.toExponential(1);
    return String(Number(n.toPrecision(5)));
  }
  function drawCurve(f) {
    ctx.beginPath();
    ctx.lineWidth=2.7;ctx.lineCap='round';ctx.lineJoin='round';ctx.strokeStyle=f.color;
    const increment=width>1600?2:1.5;
    let lastVisible=false;
    for(let sx=0;sx<=width+increment;sx+=increment){
      const x=worldX(sx);
      const y=evaluate(f,x);
      const sy=toScreenY(y);
      if(!Number.isFinite(sy)||Math.abs(sy)>height*20){lastVisible=false;continue;}
      if(!lastVisible)ctx.moveTo(sx,sy);else ctx.lineTo(sx,sy);
      lastVisible=true;
    }
    ctx.stroke();
  }
  function drawCrosshair() {
    if (!pointerCursor) return;
    const x=toScreenX(pointerCursor.x),y=toScreenY(pointerCursor.y);
    if (x<0||x>width||y<0||y>height)return;
    ctx.save();ctx.setLineDash([5,5]);ctx.strokeStyle='#a8bdc0';ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,height);ctx.moveTo(0,y);ctx.lineTo(width,y);ctx.stroke();ctx.restore();
  }
  function drawChart(withCursor = true) {
    if (!ctx || width < 30 || height < 30) return;
    const dpr = canvas.width / width;
    ctx.setTransform(dpr,0,0,dpr,0,0);
    ctx.clearRect(0,0,width,height);
    ctx.fillStyle='#fff';ctx.fillRect(0,0,width,height);
    drawGrid();
    ctx.save();ctx.beginPath();ctx.rect(0,0,width,height);ctx.clip();
    for (const f of state.functions) if (f.visible) drawCurve(f);
    if (withCursor) drawCrosshair();
    ctx.restore();
    $('scaleInfo').textContent = `x: ${formatTick(width/state.viewport.sx)} · y: ${formatTick(height/state.viewport.sy)}`;
  }
  function queueDraw() {
    if (frameQueued) return;
    frameQueued = true;
    requestAnimationFrame(() => {frameQueued=false;drawChart();});
  }
  function fitGraph() {
    if (width < 30 || height < 30) return;
    const visible = state.functions.filter(f => f.visible);
    if (!visible.length) {state.viewport = {cx:0,cy:0,sx:width/14,sy:height/18};persist();queueDraw();return;}
    const maxDegree=Math.max(...visible.map(f=>f.degree));
    const spanX=maxDegree>=4?6:maxDegree===3?9:14;
    const left=-spanX/2,right=spanX/2;
    let minY=0,maxY=0;
    for (const f of visible) for(let i=0;i<=260;i++){
      const value=evaluate(f,left+(right-left)*i/260);
      if(Number.isFinite(value)){minY=Math.min(value,minY);maxY=Math.max(value,maxY);}
    }
    const pad=Math.max(2, (maxY-minY)*.14);
    state.viewport={cx:0,cy:(maxY+minY)/2,sx:width/spanX,sy:height/(maxY-minY+2*pad)};
    state.viewport.sy=Math.max(3,Math.min(2000,state.viewport.sy));
    persist();queueDraw();
  }
  function zoomAt(factor,screenX,screenY,targetX=screenX,targetY=screenY) {
    const x=worldX(screenX), y=worldY(screenY), v=state.viewport;
    v.sx=Math.max(3,Math.min(2000,v.sx*factor));
    v.sy=Math.max(3,Math.min(2000,v.sy*factor));
    v.cx=x-(targetX-width/2)/v.sx;
    v.cy=y+(targetY-height/2)/v.sy;
    persist();queueDraw();
  }
  $('zoomInButton').addEventListener('click',()=>zoomAt(1.3,width/2,height/2));
  $('zoomOutButton').addEventListener('click',()=>zoomAt(1/1.3,width/2,height/2));
  $('fitButton').addEventListener('click',()=>{fitGraph();showToast('محدودهٔ نمودار تنظیم شد.');});
  $('exportButton').addEventListener('click',()=>{
    drawChart(false);
    const a=document.createElement('a');a.download='polynomial-graph.png';a.href=canvas.toDataURL('image/png');
    document.body.appendChild(a);a.click();a.remove();queueDraw();showToast('تصویر نمودار ذخیره شد.');
  });
  canvas.addEventListener('wheel',event=>{
    event.preventDefault();
    const rect=canvas.getBoundingClientRect();
    zoomAt(Math.exp(-Math.max(-150,Math.min(150,event.deltaY))*0.0017),event.clientX-rect.left,event.clientY-rect.top);
  },{passive:false});
  function relativePoint(e) {const rect=canvas.getBoundingClientRect();return {x:e.clientX-rect.left,y:e.clientY-rect.top};}
  function setCursor(point) {
    pointerCursor={x:worldX(point.x),y:worldY(point.y)};
    $('graphCoordinates').querySelector('b').textContent=`x: ${formatTick(pointerCursor.x)}   y: ${formatTick(pointerCursor.y)}`;
    updateLegendHover();queueDraw();
  }
  canvas.addEventListener('pointerdown',event=>{
    if(event.button !== 0 && event.pointerType==='mouse') return;
    canvas.setPointerCapture(event.pointerId);
    activePointers.set(event.pointerId,relativePoint(event));
    if(event.pointerType!=='touch')setCursor(relativePoint(event));
    $('graphHint').hidden=true;
  });
  canvas.addEventListener('pointermove',event=>{
    const point=relativePoint(event);
    if(activePointers.has(event.pointerId)) {
      const before=[...activePointers.values()].map(p=>({...p}));
      activePointers.set(event.pointerId,point);
      const after=[...activePointers.values()];
      if(after.length===1) {
        const old=before[0];
        state.viewport.cx-=(point.x-old.x)/state.viewport.sx;
        state.viewport.cy+=(point.y-old.y)/state.viewport.sy;
      } else if(after.length>=2) {
        const p=before.slice(0,2),q=after.slice(0,2);
        const oldMid={x:(p[0].x+p[1].x)/2,y:(p[0].y+p[1].y)/2};
        const newMid={x:(q[0].x+q[1].x)/2,y:(q[0].y+q[1].y)/2};
        const distance=points=>Math.hypot(points[0].x-points[1].x,points[0].y-points[1].y);
        const oldDistance=distance(p),newDistance=distance(q);
        if(oldDistance>10&&newDistance>10)zoomAt(newDistance/oldDistance,oldMid.x,oldMid.y,newMid.x,newMid.y);
      }
      if(event.pointerType!=='touch')setCursor(point);
      queueDraw();
    } else if(event.pointerType!=='touch')setCursor(point);
  });
  const endPointer=event=>{
    if(activePointers.has(event.pointerId)) {activePointers.delete(event.pointerId);persist();}
    if(!activePointers.size && event.pointerType==='touch') {pointerCursor=null;updateLegendHover();queueDraw();}
  };
  canvas.addEventListener('pointerup',endPointer);
  canvas.addEventListener('pointercancel',endPointer);
  canvas.addEventListener('pointerleave',()=>{
    if(activePointers.size===0){pointerCursor=null;$('graphCoordinates').querySelector('b').textContent='x: —   y: —';updateLegendHover();queueDraw();}
  });
  canvas.tabIndex=0;
  canvas.addEventListener('keydown',event=>{
    const key=event.key;
    if(key==='+'||key==='=')zoomAt(1.3,width/2,height/2);
    else if(key==='-')zoomAt(1/1.3,width/2,height/2);
    else if(key==='Home')fitGraph();
    else if(key==='ArrowLeft')state.viewport.cx-=50/state.viewport.sx;
    else if(key==='ArrowRight')state.viewport.cx+=50/state.viewport.sx;
    else if(key==='ArrowUp')state.viewport.cy+=50/state.viewport.sy;
    else if(key==='ArrowDown')state.viewport.cy-=50/state.viewport.sy;
    else return;
    event.preventDefault();persist();queueDraw();
  });

  function updateConnection() {
    const online = navigator.onLine;
    $('connectionStatus').classList.toggle('offline',!online);
    $('connectionText').textContent=online?'آمادهٔ استفاده':'حالت آفلاین';
  }
  window.addEventListener('online',updateConnection);
  window.addEventListener('offline',updateConnection);
  window.addEventListener('beforeinstallprompt',event=>{
    event.preventDefault();installPrompt=event;$('installButton').hidden=false;
  });
  $('installButton').addEventListener('click',async()=>{
    if(!installPrompt){showToast('از منوی مرورگر گزینهٔ «افزودن به صفحهٔ اصلی» را انتخاب کنید.');return;}
    const prompt=installPrompt;installPrompt=null;
    $('installButton').hidden=true;
    await prompt.prompt();
  });
  window.addEventListener('appinstalled',()=>{$('installButton').hidden=true;installPrompt=null;showToast('برنامه نصب شد.');});
  if('serviceWorker' in navigator && (location.protocol==='https:' || location.hostname==='localhost' || location.hostname==='127.0.0.1')) {
    window.addEventListener('load',()=>navigator.serviceWorker.register('./sw.js').catch(err=>console.warn('Service Worker registration:',err)));
  }

  renderFunctions();updateInputMode();updateConnection();
  if(typeof ResizeObserver==='function')new ResizeObserver(resizeCanvas).observe(stage);
  window.addEventListener('resize',resizeCanvas);
  resizeCanvas();
})();
