"use strict";
/* =========================================================
   ASRAFIAS — a tiny lisp
   Reader (tokenizer + parser) -> Evaluator
   Representation: list = JS array; symbol = Sym; nil = empty list []
   ========================================================= */

class Sym { constructor(name){ this.name = name; } }
class AsrafiasReadError extends Error { constructor(msg, line){ super(msg); this.line = line||0; } }
class AsrafiasError extends Error { constructor(msg){ super(msg); } }

const isList   = v => Array.isArray(v);
const isNil    = v => Array.isArray(v) && v.length === 0;   /* nil === empty list */
const isTruthy = v => v !== false && !(Array.isArray(v) && v.length === 0);

function asrafiasEqual(a, b){
  if(Array.isArray(a) || Array.isArray(b)){
    if(Array.isArray(a) && Array.isArray(b)){
      if(a.length !== b.length) return false;
      for(let i=0;i<a.length;i++) if(!asrafiasEqual(a[i], b[i])) return false;
      return true;
    }
    return false;
  }
  if(a instanceof Sym) return b instanceof Sym && a.name === b.name;
  if(typeof a !== typeof b) return false;
  return a === b;
}

function pr_str(x, readable){
  if(x === true) return 'sotyo';
  if(x === false) return 'mittha';
  if(typeof x === 'number') return String(x);
  if(typeof x === 'string') return readable ? '"' + x.replace(/\\/g,'\\\\').replace(/"/g,'\\"') + '"' : x;
  if(x instanceof Sym) return x.name;
  if(Array.isArray(x)) return x.length === 0 ? 'nil' : '(' + x.map(e => pr_str(e, true)).join(' ') + ')';
  if(x instanceof AsrafiasFunction) return '#<fn ' + x.name + '>';
  if(x instanceof NativeFunction) return '#<builtin ' + x.name + '>';
  return String(x);
}

/* ---------- READER ---------- */
function tokenize(src){
  const tokens = [];
  let i = 0, line = 1;
  const delims = " \t\r\n()[]'\";";
  while(i < src.length){
    const c = src[i];
    if(c === '\n'){ line++; i++; continue; }
    if(c === ' ' || c === '\t' || c === '\r'){ i++; continue; }
    if(c === ';'){ while(i < src.length && src[i] !== '\n') i++; continue; }
    if(c === '(' || c === ')' || c === '[' || c === ']' || c === "'"){ tokens.push({t:c, line}); i++; continue; }
    if(c === '"'){
      let s = ''; i++;
      while(i < src.length && src[i] !== '"'){
        if(src[i] === '\\'){ i++; if(i < src.length){ s += src[i]==='n'?'\n':src[i]==='t'?'\t':src[i]==='r'?'\r':src[i]; i++; } continue; }
        if(src[i] === '\n') line++;
        s += src[i]; i++;
      }
      if(i >= src.length) throw new AsrafiasReadError("unterminated string", line);
      i++;
      tokens.push({t:'str', v:s, line});
      continue;
    }
    let a = '';
    while(i < src.length && !delims.includes(src[i])){ a += src[i]; i++; }
    tokens.push({t:'atom', v:a, line});
  }
  return tokens;
}

function classifyAtom(s){
  if(s === 'sotyo')  return true;
  if(s === 'mittha') return false;
  if(s === 'nil')   return [];            /* nil === empty list */
  if(/^[+-]?\d+(?:\.\d+)?$/.test(s)) return parseFloat(s);
  return new Sym(s);
}

class Reader {
  constructor(tokens){ this.tokens = tokens; this.pos = 0; }
  peek(){ return this.tokens[this.pos]; }
  next(){ return this.tokens[this.pos++]; }
  eof(){ return this.pos >= this.tokens.length; }
  readAll(){
    const forms = [];
    while(!this.eof()) forms.push(this.readForm());
    return forms;
  }
  readForm(){
    const tk = this.next();
    if(!tk) throw new AsrafiasReadError("unexpected end of input");
    if(tk.t === '(' || tk.t === '['){
      const close = tk.t === '(' ? ')' : ']';
      const list = [];
      while(true){
        const p = this.peek();
        if(!p) throw new AsrafiasReadError("unexpected end of input, expected '" + close + "'", tk.line);
        if(p.t === close){ this.next(); break; }
        if(p.t === ')' || p.t === ']') throw new AsrafiasReadError("mismatched '" + p.t + "' (expected '" + close + "')", p.line);
        list.push(this.readForm());
      }
      return list;
    }
    if(tk.t === ')' || tk.t === ']') throw new AsrafiasReadError("unexpected '" + tk.t + "'", tk.line);
    if(tk.t === "'"){ return [new Sym('bolo'), this.readForm()]; }
    if(tk.t === 'str') return tk.v;
    if(tk.t === 'atom') return classifyAtom(tk.v);
    throw new AsrafiasReadError("bad token");
  }
}

function read(src){
  const forms = new Reader(tokenize(src)).readAll();
  return forms;
}

/* ---------- ENVIRONMENT & FUNCTIONS ---------- */
class Env {
  constructor(parent = null){ this.vars = new Map(); this.parent = parent; }
  lookup(name){
    if(this.vars.has(name)) return this.vars.get(name);
    if(this.parent) return this.parent.lookup(name);
    throw new AsrafiasError("symbol '" + name + "' is not defined");
  }
  set(name, val){ this.vars.set(name, val); }
}
class AsrafiasFunction {
  constructor(params, body, env){ this.params = params; this.body = body; this.env = env; this.name = 'lambda'; }
}
class NativeFunction {
  constructor(name, fn){ this.name = name; this.fn = fn; }
}

/* ---------- INTERPRETER ---------- */
const SPECIAL = new Set(['deo','deokaj','kaj','jodi','dhoro','kor','bolo','ebong','ba']);

class Interpreter {
  constructor(){
    this.global = new Env();
    this.output = []; this.errors = []; this.steps = 0;
    this.MAX_STEPS = 400000; this.MAX_OUTPUT = 5000;
    this.installBuiltins();
  }
  run(forms){
    this.output = []; this.errors = []; this.steps = 0;
    try{ for(const f of forms) this.eval(f, this.global); }
    catch(e){
      if(e instanceof AsrafiasError || e instanceof AsrafiasReadError) this.errors.push({line:e.line||0, message:e.message});
      else if(e instanceof RangeError) this.errors.push({line:0, message:"call stack overflow — possible infinite recursion"});
      else this.errors.push({line:0, message:String(e.message || e)});
    }
    return {output:this.output, errors:this.errors};
  }
  tick(){ if(++this.steps > this.MAX_STEPS) throw new AsrafiasError("step limit exceeded — possible infinite recursion"); }

  eval(ast, env){
    this.tick();
    if(typeof ast === 'number') return ast;
    if(typeof ast === 'string') return ast;
    if(typeof ast === 'boolean') return ast;
    if(ast instanceof Sym) return env.lookup(ast.name);
    if(Array.isArray(ast)){
      if(ast.length === 0) return ast;            /* nil self-evaluates */
      const head = ast[0];
      if(head instanceof Sym && SPECIAL.has(head.name)) return this.special(head.name, ast, env);
      const fn = this.eval(head, env);
      const args = ast.slice(1).map(a => this.eval(a, env));
      return this.applyFn(fn, args);
    }
    throw new AsrafiasError("cannot evaluate: " + pr_str(ast, true));
  }

  applyFn(fn, args){
    if(fn instanceof NativeFunction) return fn.fn(args, this);
    if(fn instanceof AsrafiasFunction){
      if(args.length !== fn.params.length)
        throw new AsrafiasError("function '" + fn.name + "' expects " + fn.params.length + " arg(s), got " + args.length);
      const child = new Env(fn.env);
      for(let i=0;i<fn.params.length;i++) child.set(fn.params[i].name, args[i]);
      let result = [];
      for(const form of fn.body) result = this.eval(form, child);
      return result;
    }
    throw new AsrafiasError("cannot call " + pr_str(fn, true) + " (not a function)");
  }

  special(name, form, env){
    const args = form.slice(1);
    switch(name){
      case 'deo': {
        const sym = args[0];
        if(!(sym instanceof Sym)) throw new AsrafiasError("deo expects a symbol");
        const val = args.length > 1 ? this.eval(args[1], env) : [];
        this.global.set(sym.name, val);
        return val;
      }
      case 'deokaj': {
        const sym = args[0];
        if(!(sym instanceof Sym)) throw new AsrafiasError("deokaj expects a name symbol");
        const params = args[1];
        if(!Array.isArray(params)) throw new AsrafiasError("deokaj parameters must be a list, e.g. [x y]");
        const body = args.slice(2);
        const fn = new AsrafiasFunction(params, body, env);
        fn.name = sym.name;
        this.global.set(sym.name, fn);
        return fn;
      }
      case 'kaj': {
        let name = 'lambda', params, body;
        if(args[0] instanceof Sym){ name = args[0].name; params = args[1]; body = args.slice(2); }
        else { params = args[0]; body = args.slice(1); }
        if(!Array.isArray(params)) throw new AsrafiasError("kaj parameters must be a list, e.g. [x y]");
        for(const p of params) if(!(p instanceof Sym)) throw new AsrafiasError("kaj parameter must be a symbol");
        const fn = new AsrafiasFunction(params, body, env);
        fn.name = name;
        return fn;
      }
      case 'jodi': {
        const test = this.eval(args[0], env);
        if(isTruthy(test)) return args.length > 1 ? this.eval(args[1], env) : [];
        return args.length > 2 ? this.eval(args[2], env) : [];
      }
      case 'dhoro': {
        const bindings = args[0];
        if(!Array.isArray(bindings)) throw new AsrafiasError("dhoro bindings must be a list, e.g. [x 1 y 2]");
        if(bindings.length % 2 !== 0) throw new AsrafiasError("dhoro bindings must be pairs of name and value");
        const child = new Env(env);
        for(let i=0;i<bindings.length;i+=2){
          if(!(bindings[i] instanceof Sym)) throw new AsrafiasError("dhoro binding name must be a symbol");
          const val = this.eval(bindings[i+1], child);
          child.set(bindings[i].name, val);
        }
        let result = [];
        for(let i=1;i<args.length;i++) result = this.eval(args[i], child);
        return result;
      }
      case 'kor': {
        let result = [];
        for(const a of args) result = this.eval(a, env);
        return result;
      }
      case 'bolo': return args[0];
      case 'ebong': {
        let result = true;
        for(const a of args){ result = this.eval(a, env); if(!isTruthy(result)) return result; }
        return result;
      }
      case 'ba': {
        let result = [];
        for(const a of args){ result = this.eval(a, env); if(isTruthy(result)) return result; }
        return result;
      }
    }
    throw new AsrafiasError("unknown special form: " + name);
  }

  installBuiltins(){
    const g = this.global;
    const nb = (name, fn) => g.set(name, new NativeFunction(name, fn));
    const numErr = (op, v) => { throw new AsrafiasError("'" + op + "' expects numbers, got " + pr_str(v, true)); };
    const needNums = (op, args) => { for(const a of args) if(typeof a !== 'number') numErr(op, a); };

    nb('jog', args => { let s=0; for(const a of args){ if(typeof a!=='number') numErr('jog', a); s+=a; } return s; });
    nb('gun', args => { let p=1; for(const a of args){ if(typeof a!=='number') numErr('gun', a); p*=a; } return p; });
    nb('biyog', args => { if(!args.length) throw new AsrafiasError("'biyog' needs at least 1 arg"); needNums('biyog', args);
      let r=args[0]; if(args.length===1) return -r; for(let i=1;i<args.length;i++) r-=args[i]; return r; });
    nb('vag', args => { if(!args.length) throw new AsrafiasError("'vag' needs at least 1 arg"); needNums('vag', args);
      let r=args[0]; if(args.length===1){ if(r===0) throw new AsrafiasError("division by zero"); return 1/r; }
      for(let i=1;i<args.length;i++){ if(args[i]===0) throw new AsrafiasError("division by zero"); r/=args[i]; } return r; });
    nb('vagshesh', args => { if(args.length!==2) throw new AsrafiasError("'vagshesh' expects 2 args"); needNums('vagshesh', args);
      if(args[1]===0) throw new AsrafiasError("modulo by zero"); return args[0] % args[1]; });

    nb('soman',  args => { for(let i=1;i<args.length;i++) if(!asrafiasEqual(args[i-1], args[i])) return false; return true; });
    nb('osoman', args => { if(args.length!==2) throw new AsrafiasError("'osoman' expects 2 args"); return !asrafiasEqual(args[0], args[1]); });

    const cmp = (op, fn) => nb(op, args => {
      if(args.length < 2) return true; needNums(op, args);
      for(let i=1;i<args.length;i++) if(!fn(args[i-1], args[i])) return false;
      return true;
    });
    cmp('<',  (a,b)=>a<b);
    cmp('>',  (a,b)=>a>b);
    cmp('<=', (a,b)=>a<=b);
    cmp('>=', (a,b)=>a>=b);

    nb('na', args => isTruthy(args[0]) ? false : true);
    nb('talika', args => args.slice());
    nb('prothom', args => { const l=args[0]; if(!Array.isArray(l)) throw new AsrafiasError("'prothom' expects a list"); return l.length ? l[0] : []; });
    nb('baki',  args => { const l=args[0]; if(!Array.isArray(l)) throw new AsrafiasError("'baki' expects a list"); return l.slice(1); });
    nb('jukto',  args => { if(args.length!==2) throw new AsrafiasError("'jukto' expects 2 args"); const [x,l]=args; if(!Array.isArray(l)) throw new AsrafiasError("'jukto' expects a list as 2nd arg"); return [x, ...l]; });
    nb('gono', args => { const l=args[0]; if(!Array.isArray(l)) throw new AsrafiasError("'gono' expects a list"); return l.length; });
    nb('tomo',   args => { if(args.length!==2) throw new AsrafiasError("'tomo' expects 2 args"); const [l,i]=args; if(!Array.isArray(l)) throw new AsrafiasError("'tomo' expects a list"); if(typeof i!=='number') throw new AsrafiasError("'tomo' index must be a number"); if(i<0||i>=l.length) return []; return l[i]; });
    nb('khali?', args => { const l=args[0]; if(!Array.isArray(l)) throw new AsrafiasError("'khali?' expects a list"); return l.length===0; });

    nb('rupantor', args => { if(args.length!==2) throw new AsrafiasError("'rupantor' expects a function and a list"); const [fn,l]=args; if(!Array.isArray(l)) throw new AsrafiasError("'rupantor' expects a list"); return l.map(x => this.applyFn(fn,[x])); });
    nb('beche', args => { if(args.length!==2) throw new AsrafiasError("'beche' expects a function and a list"); const [fn,l]=args; if(!Array.isArray(l)) throw new AsrafiasError("'beche' expects a list"); return l.filter(x => isTruthy(this.applyFn(fn,[x]))); });
    nb('milao', args => { if(args.length!==3) throw new AsrafiasError("'milao' expects a function, init and a list"); const [fn,init,l]=args; if(!Array.isArray(l)) throw new AsrafiasError("'milao' expects a list"); let acc=init; for(const x of l) acc=this.applyFn(fn,[acc,x]); return acc; });
    nb('prayog',  args => { if(args.length<2) throw new AsrafiasError("'prayog' expects a function and a list"); const fn=args[0]; const coll=args[args.length-1]; if(!Array.isArray(coll)) throw new AsrafiasError("'prayog' last arg must be a list"); const pre=args.slice(1,-1); return this.applyFn(fn, [...pre, ...coll]); });

    nb('porisor', args => {
      if(args.length<1 || args.length>3) throw new AsrafiasError("'porisor' expects 1 to 3 args"); needNums('porisor', args);
      let start=0, end=args[0], step=1;
      if(args.length===2){ start=args[0]; end=args[1]; }
      if(args.length===3){ start=args[0]; end=args[1]; step=args[2]; }
      if(step===0) throw new AsrafiasError("'porisor' step cannot be 0");
      const out=[]; if(step>0){ for(let i=start;i<end;i+=step) out.push(i); } else { for(let i=start;i>end;i+=step) out.push(i); }
      return out;
    });

    nb('lekha', args => args.map(a => pr_str(a, false)).join(''));
    nb('dekhao', args => { if(this.output.length < this.MAX_OUTPUT) this.output.push(args.map(a => pr_str(a, false)).join(' ')); return []; });

    nb('joro?', args => { if(typeof args[0]!=='number') throw new AsrafiasError("'joro?' expects a number"); return args[0]%2===0; });
    nb('bijoro?',  args => { if(typeof args[0]!=='number') throw new AsrafiasError("'bijoro?' expects a number"); return args[0]%2!==0; });
    nb('shunno?', args => typeof args[0]==='number' && args[0]===0);
    nb('nil?',  args => isNil(args[0]));
    nb('dhoron',  args => typeOf(args[0]));
  }
}

function typeOf(v){
  if(Array.isArray(v)) return v.length===0 ? 'nil' : 'list';
  if(v instanceof Sym) return 'symbol';
  if(v instanceof AsrafiasFunction || v instanceof NativeFunction) return 'function';
  if(typeof v === 'number') return 'number';
  if(typeof v === 'string') return 'string';
  if(typeof v === 'boolean') return 'boolean';
  return 'unknown';
}

/* =========================================================
   UI layer
   ========================================================= */
const codeEl = document.getElementById('code');
const hlEl = document.getElementById('highlight');
const gutterEl = document.getElementById('gutterInner');
const runBtn = document.getElementById('runBtn');
const clearBtn = document.getElementById('clearBtn');
const samples = document.getElementById('samples');
const tabsEl = document.getElementById('tabs');

const esc = s => s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
const HL_KW = { deo:1, deokaj:1, kaj:1, jodi:1, dhoro:1, kor:1, bolo:1, ebong:1, ba:1, sotyo:1, mittha:1, nil:1 };

function highlight(code){
  const re = /(;[^\n]*)|("(?:\\.|[^"\\])*")|([()[\]'])|([+-]?\d+(?:\.\d+)?)|([^\s()[\]';"]+)/g;
  let out='', last=0, m;
  while((m = re.exec(code)) !== null){
    if(m.index > last) out += esc(code.slice(last, m.index));
    if(m[1])      out += '<span class="hl-comment">' + esc(m[1]) + '</span>';
    else if(m[2]) out += '<span class="hl-string">'  + esc(m[2]) + '</span>';
    else if(m[3]) out += '<span class="hl-delim">'   + esc(m[3]) + '</span>';
    else if(m[4]) out += '<span class="hl-number">'  + esc(m[4]) + '</span>';
    else if(m[5]) out += HL_KW[m[5]] ? '<span class="hl-keyword">' + esc(m[5]) + '</span>'
                                    : '<span class="hl-sym">' + esc(m[5]) + '</span>';
    last = re.lastIndex;
  }
  if(last < code.length) out += esc(code.slice(last));
  return out + '\n';
}
function updateGutter(){
  const n = codeEl.value.split('\n').length;
  let s=''; for(let i=1;i<=n;i++) s += i + '\n';
  gutterEl.textContent = s;
  document.getElementById('statLines').textContent = n;
}
function updateHighlight(){ hlEl.innerHTML = highlight(codeEl.value); updateGutter(); }
codeEl.addEventListener('input', updateHighlight);
codeEl.addEventListener('scroll', () => {
  hlEl.scrollTop = codeEl.scrollTop; hlEl.scrollLeft = codeEl.scrollLeft;
  gutterEl.style.transform = 'translateY(' + (-codeEl.scrollTop) + 'px)';
});
codeEl.addEventListener('keydown', e => {
  if((e.ctrlKey || e.metaKey) && e.key === 'Enter'){ e.preventDefault(); runProgram(); }
  if(e.key === 'Tab'){
    e.preventDefault();
    const s = codeEl.selectionStart, en = codeEl.selectionEnd;
    codeEl.value = codeEl.value.slice(0, s) + '  ' + codeEl.value.slice(en);
    codeEl.selectionStart = codeEl.selectionEnd = s + 2;
    updateHighlight();
  }
});

function switchTab(name){
  document.querySelectorAll('.tab').forEach(t => t.classList.toggle('active', t.dataset.tab === name));
  document.querySelectorAll('.tab-pane').forEach(p => p.classList.toggle('active', p.id === 'pane-' + name));
}
tabsEl.addEventListener('click', e => { const b = e.target.closest('.tab'); if(b) switchTab(b.dataset.tab); });

function formBadge(f){
  if(Array.isArray(f)) return f.length===0 ? ['nil','b-nil'] : ['list','b-list'];
  if(f instanceof Sym) return ['sym','b-sym'];
  if(typeof f==='number') return ['num','b-num'];
  if(typeof f==='string') return ['str','b-str'];
  if(typeof f==='boolean') return ['bool','b-bool'];
  return ['?','b-sym'];
}
function formValue(f){
  if(Array.isArray(f)) return f.length===0 ? 'nil' : '';
  if(f instanceof Sym) return f.name;
  if(typeof f==='number') return String(f);
  if(typeof f==='string') return '"' + f.replace(/\\/g,'\\\\').replace(/"/g,'\\"') + '"';
  if(typeof f==='boolean') return f ? 'sotyo' : 'mittha';
  return '';
}
function renderForm(f){
  const [label, bc] = formBadge(f);
  const val = formValue(f);
  let html = '<div class="tree-node"><div class="tree-row">' +
             '<span class="tree-badge ' + bc + '">' + label + '</span>' +
             (val !== '' ? '<span class="tree-value ' + (typeof f==='string'?'str':(typeof f==='number'?'num':'')) + '">' + esc(val) + '</span>' : '') +
             '</div>';
  if(Array.isArray(f) && f.length){
    html += '<div class="tree-children">';
    for(const k of f) html += renderForm(k);
    html += '</div>';
  }
  html += '</div>';
  return html;
}
function renderForms(forms){
  if(!forms.length){ document.getElementById('pane-forms').innerHTML = '<div class="empty-hint">no forms.</div>'; return; }
  let html = '<div class="tree"><div class="tree-node"><div class="tree-row"><span class="tree-badge b-list">program</span></div><div class="tree-children">';
  for(const f of forms) html += renderForm(f);
  html += '</div></div></div>';
  document.getElementById('pane-forms').innerHTML = html;
}
function renderOutput(out){
  const p = document.getElementById('pane-output');
  if(!out.length){ p.innerHTML = '<div class="empty-hint">print produced no output.</div>'; return; }
  p.innerHTML = '<div class="console">' + out.map(l => '<span class="ln">' + esc(l) + '</span>').join('') + '</div>';
}
function renderErrors(errs){
  const p = document.getElementById('pane-errors');
  if(!errs.length){ p.innerHTML = '<div class="err-empty">clean — no errors.</div>'; return; }
  p.innerHTML = errs.map(e =>
    '<div class="err-item"><div class="ewhere">' + (e.line ? 'line ' + e.line : 'runtime') + '</div>' +
    '<div class="emsg">' + esc(e.message) + '</div></div>'
  ).join('');
}

function runProgram(){
  const src = codeEl.value;
  const t0 = performance.now();
  let forms = null, readErrs = [];
  try{ forms = read(src); }
  catch(e){ if(e instanceof AsrafiasReadError) readErrs.push({line:e.line, message:e.message}); else readErrs.push({line:0, message:String(e.message||e)}); }

  let out = [], runErrs = [];
  if(forms && !readErrs.length){
    const interp = new Interpreter();
    const r = interp.run(forms);
    out = r.output; runErrs = r.errors;
  }

  const dt = (performance.now() - t0).toFixed(1);
  const allErrs = [...readErrs, ...runErrs];

  renderForms(forms || []);
  renderOutput(out);
  renderErrors(allErrs);

  const formCount = forms ? forms.length : 0;
  document.getElementById('cntForms').textContent = formCount;
  document.getElementById('cntOutput').textContent = out.length;
  document.getElementById('cntErrors').textContent = allErrs.length;
  document.getElementById('statForms').textContent = formCount;
  document.getElementById('statTime').textContent = dt;
  const sr = document.getElementById('statResult');
  if(allErrs.length){ sr.textContent = 'X ' + allErrs.length + ' error(s)'; sr.className = 'bad'; }
  else { sr.textContent = 'ok'; sr.className = 'ok'; }
  document.querySelector('.tab[data-tab="errors"]').classList.toggle('err', allErrs.length > 0);
  if(allErrs.length) switchTab('errors'); else switchTab('output');
}

runBtn.addEventListener('click', runProgram);
clearBtn.addEventListener('click', () => { codeEl.value = ''; updateHighlight(); codeEl.focus(); });

const SAMPLES = {
hello:
`; asrafias: a tiny lisp
(dekhao "hello, asrafias")
(dekhao (lekha "1 + 2 = " (jog 1 2)))
(dekhao (lekha "ebong sotyo mittha = " (ebong sotyo mittha)))
(dekhao (lekha "ba  mittha sotyo = " (ba mittha sotyo)))
`,
fact:
`; recursive factorial
(deokaj fact [n]
  (jodi (<= n 1) 1 (gun n (fact (biyog n 1)))))

(dekhao (lekha "fact 5 = " (fact 5)))
(dekhao (lekha "fact 7 = " (fact 7)))
`,
fib:
`; fibonacci by recursion
(deokaj fib [n]
  (jodi (< n 2) n (jog (fib (biyog n 1)) (fib (biyog n 2)))))

(deokaj fibs [limit]
  (rupantor fib (porisor limit)))

(dekhao (fibs 10))
`,
lists:
`; lists, rupantor, beche, milao
(deo nums (porisor 1 11))

(dekhao (lekha "nums     = " nums))
(dekhao (lekha "squares  = " (rupantor (kaj [x] (gun x x)) nums)))
(dekhao (lekha "evens    = " (beche joro? nums)))
(dekhao (lekha "sum      = " (milao jog 0 nums)))
(dekhao (lekha "product  = " (milao gun 1 nums)))
`,
closures:
`; functions that capture their environment
(deokaj make-adder [n]
  (kaj [x] (jog x n)))

(deo add5  (make-adder 5))
(deo add10 (make-adder 10))

(dekhao (add5 10))
(dekhao (add10 7))
(dekhao (lekha "5 + 100 = " (add5 100)))
`,
primes:
`; the sieve, recursively
(deokaj divides? [a b] (soman 0 (vagshesh b a)))

(deokaj has-divisor? [n i]
  (jodi (> (gun i i) n) mittha
      (jodi (divides? i n) sotyo
          (has-divisor? n (jog i 1)))))

(deokaj prime? [n]
  (jodi (< n 2) mittha (na (has-divisor? n 2))))

(dekhao (prime? 17))
(dekhao (prime? 15))
(dekhao (beche prime? (porisor 2 21)))
`
};
samples.addEventListener('change', () => {
  if(SAMPLES[samples.value]){ codeEl.value = SAMPLES[samples.value]; updateHighlight(); runProgram(); }
});

codeEl.value = SAMPLES.fact;
updateHighlight();
runProgram();
