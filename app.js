/* HWP 5 연간시간운영계획 시간표 읽기 — browser and node */
const HWPTT = (() => {
  const u16 = (d, o) => d[o] | (d[o + 1] << 8);
  const u32 = (d, o) => (d[o] | (d[o + 1] << 8) | (d[o + 2] << 16) | (d[o + 3] << 24)) >>> 0;
  const END = 0xFFFFFFFA;
  function cfb(d){
    const sig = [0xD0,0xCF,0x11,0xE0,0xA1,0xB1,0x1A,0xE1];
    if (!sig.every((b, i) => d[i] === b)) throw new Error('not-hwp');
    const ss = 1 << u16(d, 30), mss = 1 << u16(d, 32);
    const nfat = u32(d, 44), dirStart = u32(d, 48), cutoff = u32(d, 56), mfStart = u32(d, 60);
    let difStart = u32(d, 68); const ndif = u32(d, 72);
    const difat = []; for (let i = 0; i < 109; i++) difat.push(u32(d, 76 + i * 4));
    const sec = i => d.subarray((i + 1) * ss, (i + 2) * ss);
    for (let k = 0; k < ndif; k++){ const b = sec(difStart); for (let i = 0; i < ss / 4 - 1; i++) difat.push(u32(b, i * 4)); difStart = u32(b, ss - 4); }
    const fat = [];
    for (let k = 0; k < nfat; k++){ const b = sec(difat[k]); for (let i = 0; i < ss / 4; i++) fat.push(u32(b, i * 4)); }
    const chain = st => { const out = []; let g = 0; while (st < END && g++ < 1e6){ out.push(st); st = fat[st]; } return out; };
    const cat = parts => { const n = parts.reduce((a, p) => a + p.length, 0); const o = new Uint8Array(n); let p = 0; parts.forEach(x => { o.set(x, p); p += x.length; }); return o; };
    const dir = cat(chain(dirStart).map(sec));
    const ents = [];
    for (let i = 0; i * 128 < dir.length; i++){
      const e = dir.subarray(i * 128, i * 128 + 128);
      const nl = u16(e, 64); let name = '';
      for (let j = 0; j + 1 < Math.max(0, nl - 2); j += 2) name += String.fromCharCode(u16(e, j));
      ents.push({name, typ:e[66], left:u32(e, 68), right:u32(e, 72), child:u32(e, 76), start:u32(e, 116), size:u32(e, 120)});
    }
    const root = ents[0];
    const mini = root.start < END ? cat(chain(root.start).map(sec)) : new Uint8Array(0);
    const minifat = []; if (mfStart < END) chain(mfStart).forEach(s => { const b = sec(s); for (let i = 0; i < ss / 4; i++) minifat.push(u32(b, i * 4)); });
    const read = e => {
      if (e.size < cutoff){ const parts = []; let st = e.start, g = 0; while (st < END && g++ < 1e6){ parts.push(mini.subarray(st * mss, (st + 1) * mss)); st = minifat[st]; } return cat(parts).subarray(0, e.size); }
      return cat(chain(e.start).map(sec)).subarray(0, e.size);
    };
    const files = {};
    const walk = (idx, prefix, depth) => {
      if (idx === 0xFFFFFFFF || idx >= ents.length || depth > 64) return;
      const e = ents[idx]; walk(e.left, prefix, depth + 1); walk(e.right, prefix, depth + 1);
      if (e.typ === 2) files[prefix + e.name] = e; else if (e.typ === 1) walk(e.child, prefix + e.name + '/', depth + 1);
    };
    walk(root.child, '', 0);
    return {names:Object.keys(files), read:n => read(files[n])};
  }
  async function inflateRaw(bytes){
    const ds = new DecompressionStream('deflate-raw');
    const stream = new Blob([bytes]).stream().pipeThrough(ds);
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }
  function paraText(b){
    let s = '', i = 0; const n = b.length >> 1;
    while (i < n){
      const c = u16(b, i * 2);
      if (c < 32){
        if (c === 0 || c === 10 || c === 13 || (c >= 24 && c <= 31)){ if (c === 10 || c === 13) s += '\n'; i += 1; }
        else { if (c === 9) s += '\t'; i += 8; }
      } else { s += String.fromCharCode(c); i += 1; }
    }
    return s;
  }
  function tablesOf(data){
    const tables = []; let cur = null, cell = null, i = 0;
    while (i + 4 <= data.length){
      const h = u32(data, i); i += 4;
      const tag = h & 0x3FF; let size = h >>> 20;
      if (size === 0xFFF){ size = u32(data, i); i += 4; }
      const b = data.subarray(i, i + size); i += size;
      if (tag === 77 && b.length >= 8){ cur = {rows:u16(b, 4), cols:u16(b, 6), cells:[]}; tables.push(cur); cell = null; }
      else if (tag === 72 && cur && b.length >= 16){ cell = {c:u16(b, 8), r:u16(b, 10), cs:u16(b, 12), rs:u16(b, 14), t:''}; cur.cells.push(cell); }
      else if (tag === 67 && cell) cell.t += paraText(b);
    }
    return tables;
  }
  const SUBJ_CH = '국수사과영체음미도자동진융봉창통실';
  const pad = n => String(n).padStart(2, '0');
  const ymd = d => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
  function interpret(t){
    const at = {}; t.cells.forEach(c => { at[c.r + ',' + c.c] = c; });
    const txt = (r, c) => { const x = at[r + ',' + c]; return x ? x.t.replace(/\r/g, '').trim() : ''; };
    const all = t.cells.map(c => c.t).join(' ');
    const ym = all.match(/(\d{4})\s*학년도\s*(\d)\s*학기/); if (!ym) return null;
    const year = +ym[1], term = +ym[2];
    const hdr = t.cells.find(c => c.t.trim() === '월'); if (!hdr) return null;
    const h = hdr.r;
    const dayCols = ['월','화','수','목','금'].map(w => t.cells.find(c => c.r === h && c.t.trim() === w));
    if (dayCols.some(x => !x)) return null;
    const noteCell = t.cells.find(c => c.r === h && /비\s*고/.test(c.t));
    const rangeCell = t.cells.find(c => c.r === h && /기\s*간/.test(c.t));
    const weekCell = t.cells.find(c => c.r === h && c.t.trim() === '주');
    const prow = t.cells.filter(c => c.r === h + 1).sort((a, b) => a.c - b.c);
    const periods = dayCols.map(dc => prow.filter(p => p.c >= dc.c && p.c < dc.c + dc.cs));
    const titleCell = t.cells.find(c => /학년.*반/.test(c.t) && c.r < h);
    const weeks = [];
    for (let r = h + 2; r < t.rows; r++){
      const range = rangeCell ? txt(r, rangeCell.c) : '';
      const m = range.match(/(\d{1,2})\s*\.\s*(\d{1,2})/); if (!m) continue;
      const mo = +m[1], da = +m[2];
      let d = new Date(mo >= 3 ? year : year + 1, mo - 1, da);
      if (d.getDay() === 6) d.setDate(d.getDate() + 2); else if (d.getDay() === 0) d.setDate(d.getDate() + 1);
      else d.setDate(d.getDate() - (d.getDay() - 1));
      const days = periods.map(ps => {
        const s = ps.map(p => txt(r, p.c).replace(/\s+/g, ''));
        const joined = s.join('');
        if (joined && [...joined].some(ch => !SUBJ_CH.includes(ch)) && s.every(x => x.length <= 1)) return {off:joined};
        while (s.length < 6) s.push('');
        return {s};
      });
      const note = noteCell ? txt(r, noteCell.c) : '';
      const events = [];
      note.split('\n').forEach(line => {
        const em = line.trim().match(/^(\d{1,2})\.\s*(\d{1,2})\s*(?:\([^)]*\))?\s*(.+)$/);
        if (em){ const eM = +em[1]; events.push({date:ymd(new Date(eM >= 3 ? year : year + 1, eM - 1, +em[2])), text:em[3].trim()}); }
      });
      weeks.push({no:weekCell ? (+txt(r, weekCell.c) || weeks.length + 1) : weeks.length + 1, mon:ymd(d), range:range.replace(/\s+/g, ' ').trim(), days, note, events});
    }
    if (!weeks.length) return null;
    return {key:`${year}-${term}`, label:`${year}학년도 ${term}학기`, title:titleCell ? titleCell.t.trim() : '', weeks};
  }
  async function parse(bytes){
    const f = cfb(bytes);
    const head = f.read('FileHeader');
    if (!head || head.length < 40) throw new Error('not-hwp');
    if (u32(head, 36) & 2) throw new Error('password');
    const compressed = u32(head, 36) & 1;
    const secs = f.names.filter(n => /^BodyText\/Section\d+$/.test(n)).sort((a, b) => +a.match(/\d+$/)[0] - +b.match(/\d+$/)[0]);
    if (!secs.length) throw new Error('no-body');
    const terms = [];
    for (const n of secs){
      let raw = f.read(n);
      if (compressed) raw = await inflateRaw(raw);
      tablesOf(raw).forEach(t => { const x = interpret(t); if (x) terms.push(x); });
    }
    if (!terms.length) throw new Error('no-timetable');
    return terms;
  }
  return {parse};
})();

(() => {
var BUD = {}, ROS = {};
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const pad = n => String(n).padStart(2, '0');
const ymd = d => `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())}`;
const fromYmd = s => { const [y,m,d] = s.split('-').map(Number); return new Date(y, m-1, d); };
const addDays = (d, n) => { const x = new Date(d); x.setDate(x.getDate()+n); return x; };
const today = () => { const d = new Date(); d.setHours(0,0,0,0); return d; };
const WD = '일월화수목금토';
const fmtMD = s => { const d = fromYmd(s); return `${d.getMonth()+1}/${d.getDate()} (${WD[d.getDay()]})`; };
const fmtLong = s => { const d = fromYmd(s); return `${d.getMonth()+1}월 ${d.getDate()}일 ${WD[d.getDay()]}요일`; };
const dayDiff = s => Math.round((fromYmd(s) - today()) / 86400000);
const byTime = (a, b) => (a.time || '99') < (b.time || '99') ? -1 : (a.time || '99') > (b.time || '99') ? 1 : (a.createdAt || 0) - (b.createdAt || 0);

const HOLIDAYS = {
  '2026-01-01':'신정','2026-02-16':'설날 연휴','2026-02-17':'설날','2026-02-18':'설날 연휴','2026-03-01':'삼일절','2026-03-02':'대체공휴일',
  '2026-05-05':'어린이날','2026-05-24':'부처님오신날','2026-05-25':'대체공휴일','2026-06-03':'지방선거','2026-06-06':'현충일',
  '2026-08-15':'광복절','2026-08-17':'대체공휴일','2026-09-24':'추석 연휴','2026-09-25':'추석','2026-09-26':'추석 연휴',
  '2026-07-17':'제헌절','2026-10-03':'개천절','2026-10-05':'대체공휴일','2026-10-09':'한글날','2026-12-25':'성탄절',
  '2027-01-01':'신정','2027-02-06':'설날 연휴','2027-02-07':'설날','2027-02-08':'설날 연휴','2027-02-09':'대체공휴일','2027-03-01':'삼일절',
  '2027-05-05':'어린이날','2027-05-13':'부처님오신날','2027-06-06':'현충일','2027-07-17':'제헌절','2027-08-15':'광복절','2027-08-16':'대체공휴일',
  '2027-09-14':'추석 연휴','2027-09-15':'추석','2027-09-16':'추석 연휴','2027-10-03':'개천절','2027-10-04':'대체공휴일',
  '2027-10-09':'한글날','2027-10-11':'대체공휴일','2027-12-25':'성탄절','2027-12-27':'대체공휴일'
};
const CATS = ['출결','상담','생활','행발','학부모','수업','할일','메모'];
const CATVAR = {'출결':'--c-att','상담':'--c-cns','생활':'--c-life','학부모':'--c-par','수업':'--c-cls','할일':'--c-todo','메모':'--c-memo','행발':'--c-hb'};
const catStyle = c => `style="--c:var(${CATVAR[c] || '--c-memo'})"`;

const S = {
  space:'grade', db:null, user:null, dl:null, uid:null, canWrite:true, privateOk:false,
  settings:{gradeName:'3학년', classCount:4, lunchAfter:3},
  events:[], tasks:[], notices:[], links:[], daily:null,
  profile:{myClass:'', roster:[]}, journal:[], sheet:{items:[], values:{}},
  month:(() => { const d = today(); return new Date(d.getFullYear(), d.getMonth(), 1); })(),
  selDate:ymd(today()), taskFilter:'open', meTab:'day', jDate:ymd(today()), selStu:null, onlyMissing:false,
  jForced:null, gaType:'event', armed:null, editTask:null, editEntry:null, dailyDirty:false,
  pending:new Set(), unsubDaily:null, unsubDay:null, dailyToday:null,
  notes:{items:[]}, day:{}, tdSrc:'all', tdHigh:false, cnsF:'all',
  stage:{notice:[], j:[], cns:[], stu:[]}, dailyImgs:[], dailyDrops:[], editImgs:[], editDrops:[], assets:null,
  ttplan:{terms:[]}, ttIdx:{}, ttMon:null, ttTerm:null, ttCal:null, ttCalOpen:false,
  route:'grade', page:'main', tabs:[], rows:[], tabId:null, unsubRows:null, focusRow:null, editCols:null, newTpl:'blank'
};

/* ---------- parsing ---------- */
function mkDate(m, d, base){
  let dt = new Date(base.getFullYear(), m-1, d);
  if (dt < addDays(base, -180)) dt = new Date(base.getFullYear()+1, m-1, d);
  else if (dt > addDays(base, 185)) dt = new Date(base.getFullYear()-1, m-1, d);
  return dt;
}
/* 명부 이름으로 학생 찾기: 성까지 쓴 이름, 그리고 반에서 겹치지 않는 이름(성 뺀 것) */
function namesIn(s){
  const ro = (S.profile.roster || []).filter(r => r.name && r.name.length >= 2);
  const out = [];
  ro.forEach(r => { if (s.includes(r.name)) out.push(r.no); });
  const given = {};
  ro.forEach(r => { if (r.name.length >= 3){ const g = r.name.slice(1); given[g] = given[g] ? -1 : r.no; } });
  Object.entries(given).forEach(([g, no]) => {
    if (no === -1 || out.includes(no)) return;
    const full = ro.find(r => r.no === no).name;
    const t = s.split(full).join(' ');
    if (new RegExp('(^|[^가-힣])' + g).test(t)) out.push(no);
  });
  return out;
}
function parseLine(raw, opts = {}){
  const base = today();
  let s = ' ' + raw + ' ';
  let date = null, time = null, end = null, every = null, eom = false;
  s = s.replace(/#?매\s*주(마다)?/, () => { every = 'w'; return ' '; });
  if (!every) s = s.replace(/#?매\s*(월|달)(마다)?/, () => { every = 'm'; return ' '; });
  if (every === 'm'){
    s = s.replace(/말\s*일/, () => { eom = true; return ' '; });
    s = s.replace(/(?<![\d\/.월])\s(\d{1,2})\s*일(?![요])/, (all, d) => { const t = new Date(base.getFullYear(), base.getMonth(), +d); date = t < new Date(base.getFullYear(), base.getMonth(), base.getDate()) ? new Date(base.getFullYear(), base.getMonth() + 1, +d) : t; return ' '; });
    if (eom){ date = new Date(base.getFullYear(), base.getMonth() + 1, 0); }
  }
  s = s.replace(/20\d\d\s*(?:[.\/-]|년)\s*(?=\d{1,2}\s*(?:[.\/-]|월))/g, ' ');
  const take = (re, fn) => { const m = s.match(re); if (m){ fn(m); s = s.replace(m[0], ' '); return true; } return false; };
  const mkEnd = (sm, sd, em, ed) => { const a = mkDate(sm, sd, base); let b = new Date(a.getFullYear(), (em || sm) - 1, ed); if (b < a) b = new Date(a.getFullYear() + 1, (em || sm) - 1, ed); return [a, b]; };
  take(/(\d{1,2})\s*월\s*(\d{1,2})\s*일\s*(?:\([^)]*\))?\s*[~∼～-]\s*(?:(\d{1,2})\s*월\s*)?(\d{1,2})\s*일(?:\s*\([^)]*\))?(\s*까지)?/, m => { [date, end] = mkEnd(+m[1], +m[2], m[3] && +m[3], +m[4]); }) ||
  take(/(?<![\d:])(\d{1,2})\s*[\/.]\s*(\d{1,2})\.?\s*(?:\([^)]*\))?\s*[~∼～-]\s*(?:(\d{1,2})\s*[\/.]\s*)?(\d{1,2})(?![\d:])\.?(?:\s*\([^)]*\))?(\s*까지)?/, m => { [date, end] = mkEnd(+m[1], +m[2], m[3] && +m[3], +m[4]); });
  date ||
  take(/(\d{1,2})\s*월\s*(\d{1,2})\s*일(?:\s*\([월화수목금토일]\))?(\s*까지)?/, m => { date = mkDate(+m[1], +m[2], base); }) ||
  take(/(?<![\d:])(\d{1,2})\s*[\/.]\s*(\d{1,2})(?![\d:])\.?(?:\s*\([월화수목금토일]\))?(\s*까지)?/, m => { date = mkDate(+m[1], +m[2], base); }) ||
  take(/(다다음\s*주|다음\s*주|담주|이번\s*주)?\s*([월화수목금토일])요일(\s*까지)?/, m => {
    const idx = WD.indexOf(m[2]);
    if (m[1]){
      const mon = addDays(base, -((base.getDay()+6) % 7));
      const off = (idx + 6) % 7;
      const wk = /다다음/.test(m[1]) ? 14 : /이번/.test(m[1]) ? 0 : 7;
      date = addDays(mon, off + wk);
    } else {
      date = addDays(base, (idx - base.getDay() + 7) % 7);
    }
  }) ||
  take(/(오늘|내일|모레|글피)(\s*까지)?/, m => { date = addDays(base, {'오늘':0,'내일':1,'모레':2,'글피':3}[m[1]]); });

  take(/(오전|오후|아침|낮|저녁|밤)?\s*(\d{1,2})\s*시(?!간)\s*(?:(\d{1,2})\s*분|(반))?/, m => {
    let h = +m[2]; const mi = m[3] ? +m[3] : (m[4] ? 30 : 0);
    if (/오후|낮|저녁|밤/.test(m[1] || '') && h < 12) h += 12;
    else if (!m[1] && h >= 1 && h <= 6) h += 12;
    if (h < 24 && mi < 60) time = `${pad(h)}:${pad(mi)}`;
  }) ||
  take(/(?<![\d.\/])(\d{1,2}):(\d{2})(?!\d)/, m => {
    let h = +m[1]; const mi = +m[2];
    if (h >= 1 && h <= 6) h += 12;
    if (h < 24 && mi < 60) time = `${pad(h)}:${pad(mi)}`;
  });

  let prio = null;
  s = s.replace(/!\s*(높음|중요|급함|보통|낮음)/, (_, t) => { prio = /높음|중요|급함/.test(t) ? '높음' : t; return ' '; });
  const tags = [];
  s = s.replace(/#(\S+)/g, (_, t) => { tags.push(t); return ' '; });
  if (!prio && tags.some(t => /^(중요|높음|급함)$/.test(t))) prio = '높음';
  let who = null;
  s = s.replace(/@\s*(전체|\d{1,2}\s*반?)/, (_, t) => { who = t === '전체' ? '전체' : parseInt(t, 10) + '반'; return ' '; });
  if (!who) s = s.replace(/@(\S+)/, (all, t) => { const c = clsCanon(t); if (c && c !== t || clsNames().includes(t)){ who = c; return ' '; } return all; });
  const students = [];
  if (opts.students){
    s = s.replace(/(\d{1,2})\s*번(?!째)/g, (_, n) => { const k = +n; if (!students.includes(k)) students.push(k); return ' '; });
    namesIn(s).forEach(k => { if (!students.includes(k)) students.push(k); });
  }
  let text = s.replace(/\s+/g, ' ').trim().replace(/^까지\s*/, '').replace(/^[,·]\s*/, '');
  const lead = text.match(/^(출결|상담|생활|행발|행동발달|학부모|수업|할일|할 일|메모)\s*[:·]?\s+/);
  if (lead){ const c = lead[1] === '행동발달' ? '행발' : lead[1] === '할 일' ? '할일' : lead[1]; tags.unshift(c); text = text.slice(lead[0].length); }
  if (end && date && end <= date) end = null;
  if (every && !date) date = new Date(base.getFullYear(), base.getMonth(), base.getDate());
  return { date: date ? ymd(date) : null, end: end ? ymd(end) : null, time, tags, who, students, text, prio,
           repeat: tags.some(t => /^(반복|매년)$/.test(t)), every, eom:eom || undefined };
}
/* 매주·매월 할 일: 끝내면 다음 차례를 새로 만들어요 */
const EVERY_NAME = {w:'매주', m:'매월'};
function nextDue(k, every, eom){
  const d = fromYmd(k);
  if (every === 'w') return ymd(addDays(d, 7));
  if (eom) return ymd(new Date(d.getFullYear(), d.getMonth() + 2, 0));
  const n = new Date(d.getFullYear(), d.getMonth() + 1, 1), last = new Date(n.getFullYear(), n.getMonth() + 1, 0).getDate();
  return ymd(new Date(n.getFullYear(), n.getMonth(), Math.min(d.getDate(), last)));
}
async function spawnNext(kind, x){
  if (!x || !x.every || x.spawned) return;
  const tk = ymd(today()); let n = nextDue((kind === 'task' ? x.due : x.date) || tk, x.every, x.eom);
  for (let i = 0; i < 60 && n < tk; i++) n = nextDue(n, x.every, x.eom);
  try {
    if (kind === 'task'){
      await S.db.collection('tasks').add({title:x.title, due:n, who:x.who || '전체', repeat:!!x.repeat, every:x.every, eom:!!x.eom, prio:x.prio || '보통', kind:x.kind || null, done:false, note:x.note || '', createdBy:S.uid, createdAt:Date.now()});
      await S.db.doc('tasks/' + x.id).update({spawned:true});
    } else {
      await S.db.doc(PROFILE()).collection('journal').add({date:n, end:null, time:x.time || null, cat:'할일', text:x.text, students:[], att:null, prio:x.prio || '보통', area:x.area || '', imgs:[], every:x.every, eom:!!x.eom, done:false, createdAt:Date.now()});
      await S.db.doc(PROFILE()).collection('journal').doc(x.id).update({spawned:true});
    }
    toast(`${EVERY_NAME[x.every]} 할 일이라 다음 차례(${fmtMD(n)})를 만들어 뒀어요.`);
  } catch (e){ wErr(e, kind === 'task'); }
}
function inferCat(text, tags, forced, hasStu){
  if (forced) return forced;
  for (const t of tags){ const n = t.replace(/\s/g, ''); if (CATS.includes(n)) return n; if (n === '할일' || n === '할것' || ['학급', '학년', '학교', '업무', '연수', '개인'].includes(n)) return '할일'; }
  if (/결석|지각|조퇴|결과|출석인정/.test(text) || (hasStu && /체험학습/.test(text))) return '출결';
  if (/상담/.test(text)) return '상담';
  if (/학부모|어머니|아버지|보호자|전화|문자|연락|하이톡|알림톡/.test(text)) return '학부모';
  if (/다툼|싸움|싸웠|칭찬|사과|화해|생활지도|다쳐|다침|보건실|울었|놀림/.test(text)) return '생활';
  if (/수업|단원|진도|평가|과제|숙제|받아쓰기/.test(text)) return '수업';
  return '메모';
}
function inferAtt(text, hasStu = true){
  const k = (text.match(/결석|지각|조퇴|결과/) || [])[0] || (hasStu && /체험학습/.test(text) ? '결석' : null);
  if (!k) return null;
  let r = '기타';
  if (/질병|아파|아픔|아프|병원|열이|감기|장염|두통|복통|진료/.test(text)) r = '질병';
  else if (/미인정|무단/.test(text)) r = '미인정';
  else if (/체험학습|출석인정|인정\s*결석|학교장\s*허가|경조사|전염|감염/.test(text)) r = '출석인정';
  return { kind:k, reason:r };
}

/* ---------- helpers ---------- */
let toastTimer;
function toast(msg){ const t = $('#toast'); t.textContent = msg; t.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => { t.hidden = true; }, 3200); }
function banner(msg){
  const w = window.__gasWho;
  if (!msg && w && w.deployOk === false) msg = w.note || '만든 선생님이 배포 설정을 "웹 앱에 액세스하는 사용자"로 바꿔야 열려요.';
  if (!msg && window.__gasWhoErr) msg = '교무수첩 서버에 연결하지 못했어요. ' + window.__gasWhoErr;
  if (!msg && w && w.email && w.sharedOk === false) msg = `지금 ${w.email} 계정으로는 열 수 있는 학년 공간이 없어요. 나의 공간은 그대로 쓸 수 있어요.`;
  $('#banner-text').textContent = msg || ''; $('#banner').hidden = !msg;
  const bg = $('#bn-grade'); if (bg) bg.hidden = !(w && w.email && w.sharedOk === false && w.deployOk !== false);
}
function stuName(no){ const r = (S.profile.roster || []).find(x => x.no === no); return r && r.name ? `${no}번 ${r.name}` : `${no}번`; }
/* 반 이름: 학교가 "사랑반·나눔반"처럼 이름을 쓰면 설정의 반 이름으로 보여 줘요. 안에서는 "1반, 2반…" 순서로 저장해요. */
const clsNames = () => (Array.isArray(S.settings.classNames) ? S.settings.classNames : []).map(x => String(x || '').trim());
function clsLabel(v){
  v = String(v || ''); const m = v.match(/^(\d{1,2})반$/);
  if (m){ const nm = clsNames()[+m[1] - 1]; if (nm) return nm; }
  return v;
}
function clsCanon(v){
  v = String(v || '').trim(); if (!v) return '';
  const i = clsNames().findIndex(x => x && (x === v || x.replace(/\s+/g, '') === v.replace(/\s+/g, '')));
  if (i >= 0) return (i + 1) + '반';
  const m = v.match(/^(\d{1,2})\s*반?$/); if (m) return (+m[1]) + '반';
  return v;
}
function classOptions(sel, withAll = true){
  const n = Math.max(1, Math.min(20, +S.settings.classCount || 4));
  let h = withAll ? `<option value="전체">학년 전체</option>` : `<option value="">고르기</option>`;
  for (let i = 1; i <= n; i++) h += `<option value="${i}반" ${sel === i+'반' ? 'selected' : ''}>${esc(clsLabel(i + '반'))}</option>`;
  if (sel && sel !== '전체' && !/^\d{1,2}반$/.test(sel)) h += `<option value="${esc(sel)}" selected>${esc(sel)}</option>`;
  return h;
}
function wErr(e, shared){
  const c = e && e.code;
  if (c === 'read_only'){ toast('지난 학년도 기록은 볼 수만 있어요.'); return; }
  if (c === 'quota_exceeded') toast('저장 공간이 가득 찼어요. 오래된 기록을 지운 뒤 다시 저장해 주세요.');
  else if (c === 'invalid_argument' && shared){ S.canWrite = false; document.body.classList.add('ro'); renderStrip(); renderTabPage(); toast('학년 공간을 고칠 권한이 없어요. 만든 선생님께 편집자로 초대해 달라고 해 주세요.'); }
  else if (c === 'invalid_argument') toast('저장하지 못했어요. 나의 공간에 쓰려면 이 페이지의 편집 권한이 필요해요.');
  else if (c === 'revoked') banner('접근 권한이 바뀌어 더 이상 저장할 수 없어요.');
  else toast('저장하지 못했어요. 잠시 뒤 다시 시도해 주세요.');
}
const writers = {};
function queueSet(path, dataFn, shared){
  if (S.arc){ toast('지난 학년도 기록은 볼 수만 있어요.'); return; }
  const w = writers[path] || (writers[path] = {busy:false, again:false});
  w.dataFn = dataFn;
  if (w.busy){ w.again = true; return; }
  const run = async () => {
    w.busy = true;
    try { await S.db.doc(path).set(w.dataFn()); } catch (e) { wErr(e, shared); }
    w.busy = false;
    if (w.again){ w.again = false; run(); }
  };
  run();
}
const busy = path => writers[path] && (writers[path].busy || writers[path].again);
async function resolveNames(){
  if (!S.user) return;
  const els = $$('[data-uid]'); const ids = [...new Set(els.map(e => e.dataset.uid).filter(Boolean))];
  if (!ids.length) return;
  const ps = await S.user.profiles(ids);
  els.forEach(e => { const p = ps[e.dataset.uid]; e.textContent = p && p.name ? p.name : (p && p.isMe ? '나' : '학년 선생님'); });
}
function author(uid){ return uid ? `<span data-uid="${esc(uid)}">…</span>` : '학년 시트에서 옮김'; }
function csv(rows){ return '\uFEFF' + rows.map(r => r.map(v => { const s = String(v ?? ''); return /[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s; }).join(',')).join('\r\n'); }
async function save(filename, data){
  if (!S.dl){ toast('이 화면에서는 파일을 받을 수 없어요. Claude에서 열어 주세요.'); return; }
  try { await S.dl.save({filename, data}); toast('파일을 받았어요.'); }
  catch (e){ if (e && e.code === 'declined') return; if (e && e.code === 'rate_limited') toast('잠시 뒤 다시 눌러 주세요.'); else toast('파일을 만들지 못했어요.'); }
}

/* ---------- timetable (file + edits) ---------- */
const SUBJ_NAME = {'국':'국어','수':'수학','사':'사회','과':'과학','영':'영어','체':'체육','음':'음악','미':'미술','도':'도덕','자':'자율·자치','동':'동아리','진':'진로','융':'학교자율','봉':'봉사','창':'창체','통':'통합'};
const lunchAt = () => Math.max(1, Math.min(5, parseInt(S.settings.lunchAfter, 10) || 3));
const expand = x => SUBJ_NAME[(x || '').trim()] || (x || '').trim();
const mondayOf = k => { const d = fromYmd(k); const w = d.getDay(); return ymd(addDays(d, w === 0 ? -6 : 1 - w)); };
const TTPLAN = () => `data/users/${S.uid}/ttplan`;
function buildTtIdx(){
  S.ttIdx = {};
  (S.ttplan.terms || []).forEach((t, ti) => (t.weeks || []).forEach((w, wi) => { S.ttIdx[w.mon] = {ti, wi}; }));
}
const weekAt = mon => { const x = S.ttIdx[mon]; return x ? S.ttplan.terms[x.ti].weeks[x.wi] : null; };
function subjFor(k){
  const d = fromYmd(k), wd = d.getDay();
  if (wd === 0 || wd === 6) return {s:[], src:null};
  const w = weekAt(mondayOf(k));
  if (w && w.days && w.days[wd - 1]){
    const day = w.days[wd - 1];
    if (day.off) return {off:day.off, src:'file'};
    return {s:(day.s || []).slice(0, 6), src:'file', week:w};
  }
  const base = (S.profile.timetable || {})[wd];
  return {s:base || [], src:base && base.some(Boolean) ? 'basic' : null};
}
function schoolEvents(k){
  const w = weekAt(mondayOf(k));
  if (!w) return [];
  return (w.events || []).filter(e => e.date === k).map(e => e.text);
}
function parseNoteEvents(note, mon){
  const y0 = fromYmd(mon);
  const out = [];
  (note || '').split('\n').forEach(line => {
    const m = line.trim().match(/^(\d{1,2})\s*[.\/]\s*(\d{1,2})\s*(?:\([^)]*\))?\s*(.+)$/);
    if (!m) return;
    let d = new Date(y0.getFullYear(), +m[1] - 1, +m[2]);
    if (d - y0 > 200 * 864e5) d = new Date(y0.getFullYear() - 1, +m[1] - 1, +m[2]);
    else if (y0 - d > 200 * 864e5) d = new Date(y0.getFullYear() + 1, +m[1] - 1, +m[2]);
    out.push({date:ymd(d), text:m[3].trim()});
  });
  return out;
}
function saveTtplan(){ buildTtIdx(); queueSet(TTPLAN(), () => S.ttplan, false); }
function ensureWeek(mon){
  let w = weekAt(mon); if (w) return w;
  let t = S.ttplan.terms.find(x => x.key === 'manual');
  if (!t){ t = {key:'manual', label:'직접 만든 주', title:'', weeks:[]}; S.ttplan.terms.push(t); }
  const base = S.profile.timetable || {};
  const e = addDays(fromYmd(mon), 4);
  w = {no:null, mon, range:`${fromYmd(mon).getMonth()+1}.${fromYmd(mon).getDate()}-${e.getMonth()+1}.${e.getDate()}`,
    days:[1, 2, 3, 4, 5].map(i => { const k = ymd(addDays(fromYmd(mon), i - 1)); return HOLIDAYS[k] ? {off:HOLIDAYS[k]} : {s:Array.from({length:6}, (_, p) => (base[i] || [])[p] || '')}; }),
    note:'', events:[]};
  t.weeks.push(w); buildTtIdx();
  return w;
}
async function importHwp(file){
  if (!S.uid){ toast('로그인한 상태로 열어야 시간표를 저장할 수 있어요.'); return; }
  if (typeof DecompressionStream === 'undefined'){ toast('이 브라우저에서는 파일을 읽을 수 없어요. 크롬이나 엣지, 최신 사파리에서 열어 주세요.'); return; }
  if (!/\.hwp$/i.test(file.name)){ toast('한글(.hwp) 파일만 읽을 수 있어요. .hwpx라면 한글에서 "다른 이름으로 저장 → .hwp"로 바꿔 주세요.'); return; }
  toast('시간표 파일을 읽는 중…');
  let terms;
  try { terms = await HWPTT.parse(new Uint8Array(await file.arrayBuffer())); }
  catch (e){
    const m = e && e.message;
    toast(m === 'password' ? '암호가 걸린 파일은 읽을 수 없어요. 암호를 풀고 다시 올려 주세요.'
      : m === 'no-timetable' ? '이 파일에서 요일·교시가 있는 시간표 표를 찾지 못했어요.'
      : '파일을 읽지 못했어요. 한글(.hwp) 시간표 파일인지 확인해 주세요.');
    return;
  }
  terms.forEach(t => { S.ttplan.terms = (S.ttplan.terms || []).filter(x => x.key !== t.key); S.ttplan.terms.push(t); });
  S.ttplan.terms.sort((a, b) => a.key < b.key ? -1 : 1);
  S.ttplan.file = file.name; S.ttplan.importedAt = Date.now();
  if (terms[0].title) S.ttplan.title = terms[0].title;
  saveTtplan();
  const n = terms.reduce((a, t) => a + t.weeks.length, 0);
  toast(`${terms.map(t => t.label).join(', ')} 시간표 ${n}주를 반영했어요.`);
  renderMe();
}

/* ---------- images ---------- */
const IMGC = new Map();
const imgKey = r => r.t + ':' + r.id;
const imgUrl = r => r.t === 'a' ? '/_blob/' + r.id : (IMGC.get(imgKey(r)) || '');
function thumbsHtml(refs, rm){
  return (refs || []).map((r, i) => {
    const u = imgUrl(r);
    return `<span class="thumb"><img data-img="${esc(imgKey(r))}" ${u ? `src="${esc(u)}"` : ''} alt="붙인 사진 ${i + 1}" loading="lazy">${rm ? `<button type="button" class="x" data-rmimg="${esc(rm)}" data-i="${i}" aria-label="사진 빼기">×</button>` : ''}</span>`;
  }).join('');
}
const imgLoading = new Set();
function hydrateImgs(){
  if (!S.db) return;
  document.querySelectorAll('img[data-img]:not([src])').forEach(img => {
    const k = img.dataset.img, t = k.slice(0, 1), id = k.slice(2);
    if (IMGC.has(k)){ img.src = IMGC.get(k); return; }
    if (imgLoading.has(k) || (t === 'p' && !S.uid)) return;
    imgLoading.add(k);
    const path = t === 's' ? 'images/' + id : `data/users/${S.uid}/img-${id}`;
    S.db.doc(path).get().then(snap => {
      const d = snap.exists ? snap.data().data : '';
      if (d){ IMGC.set(k, d); document.querySelectorAll('img[data-img]').forEach(x => { if (x.dataset.img === k) x.src = d; }); }
      else document.querySelectorAll('img[data-img]').forEach(x => { if (x.dataset.img === k){ const th = x.closest('.thumb'); if (th) th.classList.add('broken'); } });
    }).catch(() => {}).finally(() => imgLoading.delete(k));
  });
}
let hydrateQueued = false;
new MutationObserver(() => { if (hydrateQueued) return; hydrateQueued = true; requestAnimationFrame(() => { hydrateQueued = false; hydrateImgs(); }); })
  .observe(document.body, {childList:true, subtree:true});
document.addEventListener('error', e => { const t = e.target; if (t && t.matches && t.matches('img[data-img]')){ const th = t.closest('.thumb'); if (th) th.classList.add('broken'); } }, true);
function compressImage(file){
  return new Promise((res, rej) => {
    const url = URL.createObjectURL(file); const im = new Image();
    im.onload = () => {
      URL.revokeObjectURL(url);
      const w = im.naturalWidth, h = im.naturalHeight; let max = 1600, q = .82, out = '';
      for (let k = 0; k < 9; k++){
        const sc = Math.min(1, max / Math.max(w, h)); const c = document.createElement('canvas');
        c.width = Math.max(1, Math.round(w * sc)); c.height = Math.max(1, Math.round(h * sc));
        const x = c.getContext('2d'); x.fillStyle = '#fff'; x.fillRect(0, 0, c.width, c.height); x.drawImage(im, 0, 0, c.width, c.height);
        out = c.toDataURL('image/jpeg', q);
        if (out.length < 230000) return res(out);
        if (q > .56) q -= .1; else max = Math.round(max * .8);
      }
      res(null);
    };
    im.onerror = () => { URL.revokeObjectURL(url); rej({code:'type'}); };
    im.src = url;
  });
}
async function storeImage(file, scope){
  if (!/^image\//.test(file.type || '')) throw {code:'type'};
  if (scope === 'shared' && S.assets && ['image/png','image/jpeg','image/gif','image/webp'].includes(file.type) && file.size <= 20 * 1024 * 1024){
    try { const r = await S.assets.upload(file, {type:file.type}); return {t:'a', id:r.id}; }
    catch (e){ if (e && (e.code === 'quota_or_state' || e.code === 'rate_limited')) throw e; }
  }
  const data = await compressImage(file); if (!data) throw {code:'too_large'};
  const id = 'i' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
  if (scope === 'shared'){ await S.db.doc('images/' + id).set({data, createdBy:S.uid, createdAt:Date.now()}); IMGC.set('s:' + id, data); return {t:'s', id}; }
  await S.db.doc(`data/users/${S.uid}/img-${id}`).set({data, createdAt:Date.now()}); IMGC.set('p:' + id, data); return {t:'p', id};
}
async function dropImage(r){
  try {
    if (r.t === 'a' && S.assets) await S.assets.delete(r.id);
    else if (r.t === 's') await S.db.doc('images/' + r.id).delete();
    else if (r.t === 'p' && S.uid) await S.db.doc(`data/users/${S.uid}/img-${r.id}`).delete();
  } catch (e) {}
}
function imgErr(e){
  const c = e && e.code;
  toast(c === 'too_large' ? '사진이 너무 커요. 더 작게 잘라서 붙여 주세요.' : c === 'type' ? '사진 파일만 붙일 수 있어요.'
    : (c === 'quota_or_state' || c === 'quota_exceeded') ? '사진을 둘 공간이 가득 찼어요. 쓰지 않는 사진을 지워 주세요.'
    : c === 'invalid_argument' ? '사진을 저장할 권한이 없어요.' : '사진을 올리지 못했어요. 다시 붙여 주세요.');
}
function filesFromClipboard(e){
  const items = [...((e.clipboardData && e.clipboardData.items) || [])];
  return items.filter(i => i.kind === 'file' && /^image\//.test(i.type)).map(i => i.getAsFile()).filter(Boolean);
}
async function uploadAll(files, scope){
  if (!S.db || (scope === 'private' && !S.uid)){ toast('로그인한 상태로 열어야 사진을 붙일 수 있어요.'); return []; }
  if (scope === 'shared' && !S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return []; }
  toast(`사진 ${files.length}장 올리는 중…`);
  const out = [];
  for (const f of files){ try { out.push(await storeImage(f, scope)); } catch (e){ imgErr(e); } }
  if (out.length) toast(`사진 ${out.length}장을 붙였어요.`);
  return out;
}
function renderStage(name){ const el = $('#' + name + '-thumbs'); if (el) el.innerHTML = thumbsHtml(S.stage[name], 'stage|' + name); }
function renderDailyThumbs(){ $('#d-thumbs').innerHTML = thumbsHtml(S.dailyImgs, S.canWrite ? 'daily' : ''); }
function renderEditThumbs(){ $('#e-thumbs').innerHTML = thumbsHtml(S.editImgs, 'edit'); }
function markDailyDirty(){ S.dailyDirty = true; $('#d-meta').textContent = '저장하지 않은 내용이 있어요'; }
function imageTarget(name){
  if (name === 'notice') return {scope:'shared', add:refs => { S.stage.notice.push(...refs); renderStage('notice'); }};
  if (name === 'j' || name === 'cns' || name === 'stu') return {scope:'private', add:refs => { S.stage[name].push(...refs); renderStage(name); }};
  if (name === 'ops') return {scope:'shared', add:refs => { S.stage.ops = (S.stage.ops || []).concat(refs); renderStage('ops'); }};
  if (name === 'mo') return {scope:'private', add:refs => { const r = rt(), k = ymd(today()); const cap = $('#mo-new').value.trim().slice(0, 200); r.extra = Object.assign({}, r.extra, {[k]:(r.extra[k] || []).concat([{id:rid(), name:cap, imgs:refs}])}); $('#mo-new').value = ''; saveRoutine(); renderMorning(false); toast('사진을 오늘 할 일에 붙였어요.'); }};
  if (name === 'eval') return {scope:'private', add:refs => { S.ev.imgs = (S.ev.imgs || []).concat(refs); evSave(); $('#ev-photos').open = true; renderEval(); toast(`평가 계획 사진 ${refs.length}장을 올렸어요.`); }};
  if (name === 'mops') return {scope:'private', add:refs => { S.stage.mops = (S.stage.mops || []).concat(refs); renderStage('mops'); }};
  if (name === 'gmemo') return {scope:'shared', add:async refs => { const cur = (S.gmemo && S.gmemo.imgs) || []; try { await S.db.doc('grade/memo').set(Object.assign({}, S.gmemo || {}, {imgs:cur.concat(refs), updatedAt:Date.now(), updatedBy:S.uid})); } catch (e){ wErr(e, true); } }};
  if (name === 'daily') return {scope:'shared', add:refs => { S.dailyImgs.push(...refs); markDailyDirty(); renderDailyThumbs(); }};
  if (name === 'edit') return {scope:'private', add:refs => { S.editImgs.push(...refs); renderEditThumbs(); }};
  if (name.startsWith('note:')){ const id = name.slice(5); return {scope:'private', add:refs => { const n = S.notes.items.find(x => x.id === id); if (!n) return; n.imgs = (n.imgs || []).concat(refs); saveNotes(); renderNotes(true); }}; }
  if (name.startsWith('cell:')){ const [, row, col] = name.split(':'); return {scope:'shared', add:async refs => {
    const rr = S.rows.find(x => x.id === row); const cur = rr && Array.isArray((rr.cells || {})[col]) ? rr.cells[col] : [];
    try { await S.db.doc(`tabs/${S.tabId}/rows/${row}`).update({cells:{[col]:cur.concat(refs)}}); } catch (e){ wErr(e, true); }
  }}; }
  return null;
}
async function attach(name, files){
  const t = imageTarget(name); if (!t || !files.length) return;
  const refs = await uploadAll(files, t.scope);
  if (refs.length) await t.add(refs);
}
function pasteTargetOf(el){
  if (!el || !el.closest) return null;
  if (el.closest('#n-form')) return 'notice';
  if (el.closest('#gm-edit')) return 'gmemo';
  if (el.closest('#ops-form')) return 'ops';
  if (el.closest('#mops-form')) return 'mops';
  if (el.closest('#p-eval')) return 'eval';
  if (el.closest('#mo-add')) return 'mo';
  if (el.id === 'd-plan' || el.id === 'd-notice') return 'daily';
  if (el.id === 'j-input') return 'j';
  if (el.id === 'cns-input') return 'cns';
  if (el.id === 'stu-input') return 'stu';
  if (el.id === 'e-text') return 'edit';
  const nt = el.closest('textarea[data-note]'); if (nt) return 'note:' + nt.dataset.note;
  const ic = el.closest('.imgcell'); if (ic) return `cell:${ic.dataset.row}:${ic.dataset.col}`;
  return null;
}
document.addEventListener('paste', e => {
  const files = filesFromClipboard(e); if (!files.length) return;
  const name = pasteTargetOf(e.target) || pasteTargetOf(document.activeElement); if (!name) return;
  const types = [...((e.clipboardData && e.clipboardData.types) || [])];
  if (!types.includes('text/plain')) e.preventDefault();
  attach(name, files);
});
let pickTarget = null;
function pickImages(name){ pickTarget = name; const p = $('#img-picker'); p.value = ''; p.click(); }
$('#img-picker').addEventListener('change', e => { const files = [...(e.target.files || [])]; if (pickTarget && files.length) attach(pickTarget, files); pickTarget = null; });
async function removeImg(key, i){
  const [kind, a, b] = key.split('|');
  if (kind === 'stage'){ S.stage[a] = S.stage[a] || []; const r = S.stage[a].splice(i, 1)[0]; renderStage(a); if (r) dropImage(r); }
  else if (kind === 'gmemo'){ const cur = ((S.gmemo && S.gmemo.imgs) || []).slice(); const r = cur.splice(i, 1)[0]; try { await S.db.doc('grade/memo').set(Object.assign({}, S.gmemo || {}, {imgs:cur, updatedAt:Date.now(), updatedBy:S.uid})); if (r) dropImage(r); } catch (e){ wErr(e, true); } }
  else if (kind === 'daily'){ const r = S.dailyImgs.splice(i, 1)[0]; if (r) S.dailyDrops.push(r); markDailyDirty(); renderDailyThumbs(); }
  else if (kind === 'edit'){ const r = S.editImgs.splice(i, 1)[0]; if (r) S.editDrops.push(r); renderEditThumbs(); }
  else if (kind === 'note'){ const n = S.notes.items.find(x => x.id === a); if (!n || !n.imgs) return; const r = n.imgs.splice(i, 1)[0]; saveNotes(); renderNotes(true); if (r) dropImage(r); }
  else if (kind === 'cell'){
    const rr = S.rows.find(x => x.id === a); const cur = rr && Array.isArray((rr.cells || {})[b]) ? rr.cells[b].slice() : [];
    const r = cur.splice(i, 1)[0];
    try { await S.db.doc(`tabs/${S.tabId}/rows/${a}`).update({cells:{[b]:cur}}); if (r) dropImage(r); } catch (e){ wErr(e, true); }
  }
}
function openLightbox(src){ if (!src) return; $('#lb-img').src = src; $('#lightbox').hidden = false; }

/* ---------- pages (tabs) ---------- */
const GPAGES = [['grade','오늘','main'],['calendar','달력','calendar'],['lessons','특별수업','lessons'],['tasks','할 일','tasks'],['notices','협의·공지','notices'],['links','수업자료','links'],['ops','운영자료','ops'],['budget','예산','budget'],['roster','명부','roster']];
const MPAGES = [['me','학급일지','day'],['me-plan','수업 계획','plan'],['me-eval','평가','eval'],['me-todo','할 일','todo'],['me-stu','학생별','stu'],['me-cns','상담일지','cns'],['me-att','출결','att'],['me-sheet','명렬표','sheet'],['me-tt','시간표','tt'],['me-budget','예산','budget'],['me-roster','명부','roster'],['me-ops','자료','mops']];
const JPAGES = [['me','오늘 수업','jday'],['me-jles','수업일지','jles'],['me-jprog','진도표','jprog'],['me-jcls','반별 명렬','jcls'],['me-jtt','시간표·시수','jtt'],['me-todo','할 일','todo'],['me-cns','상담일지','cns'],['me-budget','예산','budget'],['me-ops','자료','mops']];
const isJD = () => !!(S.profile && S.profile.role === 'jd');
const curMP = () => isJD() ? JPAGES : MPAGES;
const PAGE_DESC = {
  lessons:'강사 수업·장학·검사처럼 반마다 시간을 정하는 일정을 모아요. 전담 시간, 다른 특별 수업과 겹치면 빨갛게 알려 줘요.',
  main:'학년 선생님들이 함께 보고 고치는 곳이에요. 학생 개인 정보는 여기 적지 말아 주세요.',
  calendar:'날짜를 누르면 그날 학년 일정과 할 일이 아래에 열려요.',
  tasks:'누가, 무엇을, 언제까지 하는지 학년이 함께 봐요.',
  notices:'협의 결과와 학년 안내를 쌓아 두는 곳이에요.',
  daily:'날짜를 넘기며 학년 일일계획과 알림장을 써요.',
  links:'수업에 쓰는 자료 사이트와 영상 링크예요. 과목별로 나눠 봐요.',
  ops:'학교 운영 안내, 복무·결재, 문서 양식, 업무 자료를 모아 두는 곳이에요.',
  budget:'학년 예산과 반별(학급) 예산을 함께 관리해요. 쓴 돈을 적으면 잔액이 바로 바뀌어요.',
  roster:'반별 학생 명부예요. 스프레드시트에서 복사해 붙이면 반별로 나뉘어 들어가요.',
  tab:'학년 선생님 모두가 같은 표를 보고 고쳐요. 메인 페이지와 같은 기록을 써요.'
};
const routeOf = h => (h || '').replace(/^#/, '') || 'grade';
function go(r){
  if (routeOf(location.hash) !== r){ try { history.pushState(null, '', '#' + r); } catch (e){ try { location.hash = r; } catch (e2) {} } }
  if (S.route !== r || routeOf(location.hash) !== r) applyRoute(r);
}
document.addEventListener('click', e => {
  const a = e.target.closest('a[href^="#"]');
  if (!a || e.ctrlKey || e.metaKey || e.shiftKey) return;
  e.preventDefault();
  go(a.getAttribute('href').slice(1) || 'grade');
}, true);
const sortedTabs = () => S.tabs.slice().sort((a, b) => (a.createdAt || 0) - (b.createdAt || 0));
function applyRoute(r){
  let space = 'grade', page = 'main';
  let m = curMP().find(x => x[0] === r); const g = GPAGES.find(x => x[0] === r);
  let redirected = false;
  if (!m && (MPAGES.concat(JPAGES)).some(x => x[0] === r)){ if (!S.profileLoaded && !S.pendDone) S.pendRoute = r; r = 'me'; m = curMP()[0]; redirected = true; try { history.replaceState(null, '', '#me'); } catch (e){} }
  if (m){ space = 'me'; S.meTab = m[2]; }
  else if (g){ page = g[2]; if (r === 'links') S.linkSubj = 'all'; }
  else if (r === 'daily'){ r = 'calendar'; page = 'calendar'; }
  else if (/^links-[a-z]+$/.test(r) && SUBJ.some(x => 'links-' + x[0] === r)){ page = 'links'; S.linkSubj = r.slice(6); }
  else if (/^t-[A-Za-z0-9_-]+$/.test(r)){ page = 'tab'; if (S.tabId !== r.slice(2)){ S.tabId = r.slice(2); listenRows(); } }
  else r = 'grade';
  const changed = S.route !== r;
  S.route = r; S.space = space; S.page = page;
  /* 새로고침해도 보던 곳으로 돌아오게 기억해 둬요 */
  if (!redirected){ try { localStorage.setItem('gyomu.lastRoute', r); } catch (e){} }
  document.body.dataset.space = space;
  document.body.dataset.page = space === 'me' ? 'me' : page;
  try { placeGmemo(); } catch (e){}
  $('#v-grade').hidden = space !== 'grade'; $('#v-me').hidden = space !== 'me';
  $('#sw-grade').setAttribute('aria-pressed', space === 'grade'); $('#sw-me').setAttribute('aria-pressed', space === 'me');
  $$('#v-grade .pg').forEach(el => { el.hidden = !el.classList.contains('pg-' + page); });
  renderStrip(); renderPageHead();
  if (space === 'me') renderMe();
  else { renderCal(); renderDay(); if (page === 'tab') renderTabPage(); if (page === 'ops') renderOps(); if (page === 'lessons') renderLessons(); if (page === 'links' || page === 'main') renderLinks(); if (page === 'notices' || page === 'main'){ renderNotices(); resolveNames(); } if (page === 'budget' && BUD.g) BUD.g.render(); if (page === 'roster' && ROS.g) ROS.g.render(); }
  if (changed) window.scrollTo(0, 0);
}
/* 탭 숨기기·순서: 선생님마다 따로 기억해요 (다른 선생님 화면은 그대로) */
const tabPrefKey = () => S.space === 'grade' ? 'grade' : (isJD() ? 'jd' : 'me');
function tabItems(space){
  let items;
  if (space === 'grade') items = GPAGES.map(([r, n]) => ({key:r, href:r, name:pgName('grade', r, n), base:true})).concat(sortedTabs().map(t => ({key:'t:' + t.id, href:'t-' + t.id, name:t.name || '이름 없는 탭', base:false})));
  else items = curMP().map(([r, n]) => ({key:r, href:r, name:pgName('me', r, n), base:true}));
  const pf = ((S.profile || {}).tabPrefs || {})[space === 'grade' ? 'grade' : (isJD() ? 'jd' : 'me')] || {};
  const ord = pf.order || [], hid = new Set(pf.hidden || []);
  const pos = k => { const i = ord.indexOf(k); return i < 0 ? 1e4 : i; };
  items.forEach((x, i) => { x.i = i; x.hidden = hid.has(x.key) && i > 0; });
  if (ord.length) items.sort((a, b) => (pos(a.key) - pos(b.key)) || (a.i - b.i));
  return {items, custom:!!(ord.length || hid.size)};
}
function saveTabPrefs(items){
  const k = tabPrefKey(), tp = Object.assign({}, S.profile.tabPrefs || {});
  tp[k] = {order:items.map(x => x.key), hidden:items.filter(x => x.hidden).map(x => x.key)};
  S.profile.tabPrefs = tp; saveProfile(); renderStrip(); renderTabArrange();
}
/* 과목 숨기기·순서: 내 화면에만 */
function subjPref(){ return (((S.profile || {}).tabPrefs || {}).subj) || {}; }
function subjOrdered(){ const ord = subjPref().order || [], pos = k => { const i = ord.indexOf(k); return i < 0 ? 1e4 : i; }; return SUBJ.map((x, i) => [x, i]).sort((a, b) => (pos(a[0][0]) - pos(b[0][0])) || (a[1] - b[1])).map(x => x[0]); }
function saveSubjPref(order, hidden){ const tp = Object.assign({}, S.profile.tabPrefs || {}); tp.subj = {order, hidden}; S.profile.tabPrefs = tp; saveProfile(); renderSubjArrange(); renderLinks(); }
function renderSubjArrange(){
  const hid = new Set(subjPref().hidden || []), list = subjOrdered();
  $('#sa-list').innerHTML = list.map(([k, n], i) => `<div class="ta-row ${hid.has(k) ? 'off' : ''}"><label class="ta-name"><input type="checkbox" data-sah="${k}" ${hid.has(k) ? '' : 'checked'}> ${esc(n)}</label><button type="button" class="btn small" data-samv="${k}" data-d="-1" ${i === 0 ? 'disabled' : ''} aria-label="${esc(n)} 앞으로">↑</button><button type="button" class="btn small" data-samv="${k}" data-d="1" ${i === list.length - 1 ? 'disabled' : ''} aria-label="${esc(n)} 뒤로">↓</button></div>`).join('');
}
$('#link-subj').addEventListener('click', e => { if (e.target.id !== 'subj-arr') return; $('#dlg-subj').hidden = false; renderSubjArrange(); });
$('#dlg-subj').addEventListener('change', e => {
  const c = e.target.closest('[data-sah]'); if (!c) return;
  const hid = new Set(subjPref().hidden || []);
  c.checked ? hid.delete(c.dataset.sah) : hid.add(c.dataset.sah);
  saveSubjPref(subjOrdered().map(x => x[0]), [...hid]);
});
$('#dlg-subj').addEventListener('click', e => {
  const bt = e.target.closest('[data-samv]');
  if (bt){ const o = subjOrdered().map(x => x[0]), i = o.indexOf(bt.dataset.samv), j = i + +bt.dataset.d; if (i < 0 || j < 0 || j >= o.length) return; [o[i], o[j]] = [o[j], o[i]]; saveSubjPref(o, subjPref().hidden || []); const nb = $(`#sa-list [data-samv="${bt.dataset.samv}"][data-d="${bt.dataset.d}"]`); if (nb && !nb.disabled) nb.focus(); return; }
  if (e.target.id === 'sa-reset'){ const tp = Object.assign({}, S.profile.tabPrefs || {}); delete tp.subj; S.profile.tabPrefs = tp; saveProfile(); renderSubjArrange(); renderLinks(); toast('과목을 처음대로 돌렸어요.'); }
});
function renderTabArrange(){
  const box = $('#ta-list'); if (!box || $('#dlg-tabs').hidden) return;
  const {items} = tabItems(S.space);
  box.innerHTML = items.map((x, i) => `<div class="ta-row ${x.hidden ? 'off' : ''}">
    <label class="ta-name"><input type="checkbox" data-tah="${esc(x.key)}" ${x.hidden ? '' : 'checked'} ${x.i === 0 ? 'disabled title="첫 탭은 숨길 수 없어요"' : ''}> ${esc(x.name)}${x.base ? '' : ' <small class="hint">학년 탭</small>'}</label>
    <button type="button" class="btn small" data-tamv="${esc(x.key)}" data-d="-1" ${i === 0 ? 'disabled' : ''} aria-label="${esc(x.name)} 앞으로">↑</button><button type="button" class="btn small" data-tamv="${esc(x.key)}" data-d="1" ${i === items.length - 1 ? 'disabled' : ''} aria-label="${esc(x.name)} 뒤로">↓</button></div>`).join('');
}
$('#dlg-tabs').addEventListener('change', e => {
  const c = e.target.closest('[data-tah]'); if (!c) return;
  const {items} = tabItems(S.space), x = items.find(y => y.key === c.dataset.tah); if (!x) return;
  x.hidden = !c.checked; saveTabPrefs(items);
});
$('#dlg-tabs').addEventListener('click', e => {
  const b = e.target.closest('[data-tamv]');
  if (b){ const {items} = tabItems(S.space), i = items.findIndex(y => y.key === b.dataset.tamv), j = i + +b.dataset.d; if (i < 0 || j < 0 || j >= items.length) return; [items[i], items[j]] = [items[j], items[i]]; saveTabPrefs(items); const nb = $(`#ta-list [data-tamv="${CSS.escape(b.dataset.tamv)}"][data-d="${b.dataset.d}"]`); if (nb && !nb.disabled) nb.focus(); return; }
  if (e.target.id === 'ta-reset'){ const tp = Object.assign({}, S.profile.tabPrefs || {}); delete tp[tabPrefKey()]; S.profile.tabPrefs = tp; saveProfile(); renderStrip(); renderTabArrange(); toast('탭을 처음 순서로 돌렸어요.'); }
});
function renderStrip(){
  const cur = S.route;
  const {items, custom} = tabItems(S.space);
  const isCur = x => cur === x.href || (x.href === 'links' && /^links-/.test(cur));
  const sp = S.space === 'grade' ? 'grade' : 'me';
  let h = '', prevBase = true;
  items.filter(x => !x.hidden || isCur(x)).forEach(x => {
    if (sp === 'grade' && !custom && prevBase && !x.base) h += '<span class="stab-sep"></span>';
    prevBase = x.base;
    h += `<a class="stab" href="#${esc(x.href)}" data-ren="${esc(x.key)}" title="두 번 누르거나 오른쪽 클릭하면 이름을 바꿔요" ${isCur(x) ? 'aria-current="page"' : ''}>${esc(x.name)}</a>`;
  });
  if (sp === 'grade' && S.canWrite) h += '<button type="button" class="stab add" data-act="newtab">+ 새 탭</button>';
  if (S.uid) h += '<button type="button" class="stab add ta-open" data-act="tabarrange" title="탭 숨기기·순서 바꾸기">탭 정리</button>';
  if (S.renaming) return;
  $('#sheetbar').innerHTML = h;
  const c = $('#sheetbar [aria-current]');
  if (c){ const bar = $('#sheetbar'); const l = c.offsetLeft - bar.offsetLeft; if (l < bar.scrollLeft || l + c.offsetWidth > bar.scrollLeft + bar.clientWidth) bar.scrollLeft = l - 24; }
}
function termEnd(){
  const k = ymd(today()), c = [];
  ((S.ttplan && S.ttplan.terms) || []).forEach(t => (t.weeks || []).forEach(w => (w.events || []).forEach(e => { if (/방학식|종업식|졸업식/.test(e.text)) c.push({date:e.date, name:e.text}); })));
  (S.events || []).forEach(e => { if (/방학식|종업식/.test(e.title || '')) c.push({date:e.date, name:(e.title || '').replace(/^\[학사\]\s*/, '')}); });
  const fut = c.filter(x => x.date >= k).sort((a, b) => a.date < b.date ? -1 : a.date > b.date ? 1 : (/방학/.test(b.name) ? 1 : -1));
  return fut[0] || null;
}
function termCountdown(){
  const e = termEnd(); if (!e) return '';
  const k = ymd(today()), d = fromYmd(e.date), dd = dayDiff(e.date);
  let n = 0; for (let x = today(); ymd(x) <= e.date; x = addDays(x, 1)) if (isSchoolDay(ymd(x))) n++;
  const vac = /겨울|종업/.test(e.name) ? '겨울방학' : /여름/.test(e.name) ? '여름방학' : '방학';
  return `<span class="cd-i">이번 학기 등교일 <b>${n}일</b> 남음</span><span class="cd-i">${vac} <b>${d.getMonth() + 1}월 ${d.getDate()}일(${WD[d.getDay()]})</b> ${esc(e.name)}</span><span class="cd-i dday">${dd === 0 ? 'D-DAY' : 'D-' + dd}</span>`;
}
function renderPageHead(){
  const g = S.settings.gradeName || '3학년';
  let title = `${g} 공간`;
  if (S.page === 'tab'){ const t = S.tabs.find(x => x.id === S.tabId); title = t ? t.name : `${g} 탭`; }
  else if (S.page !== 'main'){ const p = GPAGES.find(x => x[2] === S.page); title = `${g} · ${p ? pgName('grade', p[0], p[1]) : ''}${S.page === 'links' && S.linkSubj && S.linkSubj !== 'all' ? ' · ' + subjName(S.linkSubj) : ''}`; }
  $('#g-heading').textContent = title;
  if (S.page === 'main'){ const t = termCountdown(); $('#g-desc').innerHTML = t; $('#g-desc').classList.toggle('cd', !!t); }
  else { $('#g-desc').textContent = PAGE_DESC[S.page] || ''; $('#g-desc').classList.remove('cd'); }
}

/* ---------- custom grade tabs ---------- */
const TYPE_LABEL = {text:'글', number:'숫자', date:'날짜', check:'체크', image:'사진'};
const cid = () => 'c' + Math.random().toString(36).slice(2, 8);
const TEMPLATES = [
  {key:'blank', name:'빈 표', desc:'항목 · 내용 · 메모', cols:[['항목','text'],['내용','text'],['메모','text']]},
  {key:'budget', name:'예산', desc:'날짜 · 항목 · 금액 · 집행', cols:[['날짜','date'],['항목','text'],['금액','number'],['집행','check'],['비고','text']]},
  {key:'supply', name:'학습준비물', desc:'준비물 · 수량 · 신청 반', cols:[['준비물','text'],['수량','number'],['신청 반','text'],['신청함','check'],['비고','text']]},
  {key:'check', name:'체크리스트', desc:'할 일 · 담당 · 마감', cols:[['할 일','text'],['담당','text'],['마감','date'],['끝냄','check']]},
  {key:'minutes', name:'협의록', desc:'날짜 · 안건 · 결정', cols:[['날짜','date'],['안건','text'],['결정한 것','text'],['담당','text']]},
  {key:'routine', name:'수업·놀이 루틴', desc:'이름 · 방법 · 준비물', cols:[['이름','text'],['방법','text'],['준비물','text'],['링크','text']]}
];
function listenRows(){
  if (!S.db || !S.tabId) return;
  if (S.unsubRows) S.unsubRows();
  const id = S.tabId; S.rows = [];
  S.unsubRows = S.db.collection(`tabs/${id}/rows`).onSnapshot(snap => {
    if (id !== S.tabId) return;
    S.rows = docs(snap); renderTabPage();
  }, () => {});
}
function renderTabList(){
  const tabs = sortedTabs();
  $('#tablist').innerHTML = tabs.length ? tabs.map(t => `<div class="li"><div class="main"><a class="title" href="#t-${esc(t.id)}" style="color:var(--accent)">${esc(t.name || '이름 없는 탭')}</a>
    <div class="meta">${(t.cols || []).filter(c => !c.hidden).map(c => esc(c.name)).join(' · ')}</div></div>${S.canWrite ? `<div class="acts"><button type="button" class="btn small danger" data-tab-del="${esc(t.id)}">지우기</button></div>` : ''}</div>`).join('')
    : '<p class="empty">예산, 학습준비물, 협의록처럼 학년이 함께 채우는 표를 탭으로 만들어 보세요. 위 탭 막대에 하나씩 생겨요.</p>';
}
function cellVal(r, c){ const v = (r.cells || {})[c.id]; return v === undefined || v === null ? '' : v; }
function renderTabPage(){
  if (S.page !== 'tab') return;
  renderPageHead();
  const t = S.tabs.find(x => x.id === S.tabId);
  if (!t){
    $('#tab-title').textContent = S.pending.has('tabs') || !S.db ? '불러오는 중…' : '없는 탭이에요';
    $('#tab-count').textContent = '';
    $('#tab-table').innerHTML = '<p class="empty">이 탭은 지워졌거나 아직 불러오지 못했어요. 위 탭 막대에서 다른 탭을 골라 주세요.</p>';
    $('#tab-edit').hidden = true; $('#tab-del').hidden = true; $('#row-add').hidden = true; $('#tab-addimg').hidden = true; $('#tab-budget').innerHTML = ''; return;
  }
  $('#tab-edit').hidden = false; $('#tab-del').hidden = false; $('#row-add').hidden = false;
  { const tb = (S.tabs || []).find(x => x.id === S.tabId); $('#tab-addimg').hidden = !tb || (tb.cols || []).some(c => c.type === 'image' && !c.hidden); }
  renderBudget(t);
  $('#tab-title').textContent = t.name;
  const ae = document.activeElement;
  if (ae && ae.matches('input') && ae.closest('#tab-table')) return;
  const cols = (t.cols || []).filter(c => !c.hidden);
  const rows = S.rows.slice().sort((a, b) => (a.order || 0) - (b.order || 0));
  $('#tab-count').textContent = `${rows.length}줄`;
  if (!cols.length){ $('#tab-table').innerHTML = '<p class="empty">보이는 열이 없어요. "탭·열 고치기"에서 열을 추가하거나 되살려 주세요.</p>'; return; }
  const dis = S.canWrite ? '' : 'disabled';
  const head = `<tr><th class="idx">#</th>${cols.map(c => `<th>${esc(c.name)}<small>${TYPE_LABEL[c.type] || ''}</small></th>`).join('')}${S.canWrite ? '<th class="del"></th>' : ''}</tr>`;
  const body = rows.map((r, i) => `<tr><td class="idx">${i + 1}</td>${cols.map(c => {
    const v = cellVal(r, c), a = `data-row="${esc(r.id)}" data-col="${esc(c.id)}" id="c-${esc(r.id)}-${esc(c.id)}" aria-label="${i + 1}번째 줄 ${esc(c.name)}"`;
    if (c.type === 'check') return `<td class="ck"><button type="button" class="tick" data-act="cell-tick" ${a} ${dis}>${v ? '✓' : ''}</button></td>`;
    if (c.type === 'number') return `<td><input type="number" inputmode="decimal" ${a} value="${esc(v)}" ${dis}></td>`;
    if (c.type === 'date') return `<td><input type="date" ${a} value="${esc(v)}" ${dis}></td>`;
    if (c.type === 'image'){
      const refs = Array.isArray(v) ? v : [];
      return `<td><div class="imgcell" ${S.canWrite ? 'tabindex="0"' : ''} data-row="${esc(r.id)}" data-col="${esc(c.id)}" aria-label="${i + 1}번째 줄 ${esc(c.name)}. 사진을 붙여넣거나 눌러서 고르세요">${thumbsHtml(refs, S.canWrite ? `cell|${r.id}|${c.id}` : '')}${refs.length ? '' : `<span class="ph">${S.canWrite ? '눌러서 고르거나 Ctrl+V' : ''}</span>`}</div></td>`;
    }
    return `<td><input type="text" ${a} value="${esc(v)}" ${dis}></td>`;
  }).join('')}${S.canWrite ? `<td class="del"><button type="button" class="xrow ${S.armed === 'row:' + r.id ? 'armed' : ''}" data-act="row-del" data-id="${esc(r.id)}" aria-label="${i + 1}번째 줄 지우기">${S.armed === 'row:' + r.id ? '지우기?' : '×'}</button></td>` : ''}</tr>`).join('');
  const needFoot = cols.some(c => c.type === 'number' || c.type === 'check');
  const foot = needFoot ? `<tfoot><tr><td class="idx">합계</td>${cols.map(c => {
    if (c.type === 'number'){ const sum = rows.reduce((s, r) => s + (Number(cellVal(r, c)) || 0), 0); return `<td class="num">${sum.toLocaleString('ko-KR')}</td>`; }
    if (c.type === 'check') return `<td style="text-align:center">${rows.filter(r => cellVal(r, c)).length}/${rows.length}</td>`;
    return '<td></td>';
  }).join('')}${S.canWrite ? '<td></td>' : ''}</tr></tfoot>` : '';
  $('#tab-table').innerHTML = `<div class="tablewrap"><table class="grid"><thead>${head}</thead><tbody>${body || `<tr><td colspan="${cols.length + 2}" class="hint" style="padding:14px">아직 줄이 없어요. 아래 "+ 줄 추가"를 눌러 주세요.</td></tr>`}</tbody>${foot}</table></div>`;
  if (S.focusRow){
    const f = $(`#tab-table input[data-row="${S.focusRow}"]`) || $(`#tab-table button[data-row="${S.focusRow}"]`);
    if (f){ S.focusRow = null; f.focus(); }
  }
}
function renderTplPicker(){
  $('#nt-tpls').innerHTML = TEMPLATES.map(t => `<button type="button" data-tpl="${t.key}" aria-pressed="${S.newTpl === t.key}">${t.name}<small>${t.desc}</small></button>`).join('');
}
function openNewTab(){
  if (!S.db || !S.canWrite){ toast('학년 탭을 만들려면 편집 권한이 필요해요.'); return; }
  S.newTpl = 'blank'; $('#nt-name').value = ''; renderTplPicker(); openDlg('#dlg-newtab');
}
function syncEditCols(){
  (S.editCols || []).forEach((c, i) => {
    const n = $('#tbc-name-' + i), t = $('#tbc-type-' + i);
    if (n) c.name = n.value.trim() || c.name; if (t) c.type = t.value;
  });
}
function renderEditCols(){
  $('#tb-cols').innerHTML = S.editCols.map((c, i) => `<div class="row ${c.hidden ? 'gone' : ''}">
    <input type="text" id="tbc-name-${i}" value="${esc(c.name)}" aria-label="열 이름" ${c.hidden ? 'disabled' : ''}>
    <select id="tbc-type-${i}" style="width:auto" aria-label="열 종류" ${c.hidden ? 'disabled' : ''}>${Object.entries(TYPE_LABEL).map(([k, v]) => `<option value="${k}" ${c.type === k ? 'selected' : ''}>${v}</option>`).join('')}</select>
    <button type="button" class="btn small" data-colx="${i}">${c.hidden ? '되살리기' : '빼기'}</button></div>`).join('');
}

/* ---------- grade render ---------- */
function renderHeader(){
  const g = S.settings.gradeName || '3학년';
  $('#brand-name').textContent = `${g} 교무수첩`;
  $('#g-heading').textContent = `${g} 공간`;
  const d = today(); $('#brand-date').textContent = `${d.getFullYear()}. ${d.getMonth()+1}. ${d.getDate()}. ${WD[d.getDay()]}요일`;
  $('#me-class').textContent = isJD() ? `${(S.jd && S.jd.subject) || '교과'} 전담` : S.profile.myClass ? `${g} ${clsLabel(S.profile.myClass)}` : '우리 반';
  const ask = $('#cls-ask');
  if (ask){
    ask.hidden = !(S.uid && S.profileLoaded && !S.arc && ((!S.profile.myClass && !isJD()) || S.clsAsk));
    const jb = $('#cls-ask-jd'); if (jb) jb.textContent = isJD() ? '담임으로 바꾸기' : '교과 전담이에요';
    ask.querySelector('b').textContent = isJD() ? '담임 선생님이 되셨나요?' : '몇 반 선생님인가요?';
    if (!ask.hidden && document.activeElement !== $('#cls-ask-sel')) $('#cls-ask-sel').innerHTML = classOptions(S.profile.myClass, false);
  }
  if (typeof renderMotto === 'function') try { renderMotto(); } catch (e){}
}
const EV_KINDS = [['submit','제출'],['event','행사'],['meet','회의·협의'],['work','업무·마감'],['class','수업·평가'],['parent','학부모'],['trip','출장·연수'],['off','휴업·방학'],['etc','기타']];
function guessKind(t){
  t = String(t || '');
  if (/휴업|방학|공휴|재량휴/.test(t)) return 'off';
  if (/협의|회의|위원회|연수회|워크숍/.test(t)) return 'meet';
  if (/출장|연수|교육청|컨설팅/.test(t)) return 'trip';
  if (/학부모|상담주간|총회|공개의 날/.test(t)) return 'parent';
  if (/평가|공개수업|수업 공개|진단|시험/.test(t)) return 'class';
  if (/제출|회신|수합|올리기|내기/.test(t)) return 'submit';
  if (/마감|까지|입력|보고|신청/.test(t)) return 'work';
  if (/행사|축제|운동회|체험|학예|입학|졸업|소풍|발표회|대회|식$|기념일|임장/.test(t)) return 'event';
  return 'etc';
}
const evKind = e => (EV_KINDS.some(k => k[0] === e.kind) ? e.kind : guessKind(e.title));
const tkKind = t => (EV_KINDS.some(k => k[0] === t.kind) ? t.kind : guessKind(t.title));
const kindName = k => (EV_KINDS.find(x => x[0] === k) || ['', '기타'])[1];
function renderKindPick(){
  const el = $('#ga-kind'); if (!el) return;
  el.hidden = false;
  const cur = S.gaKind || 'auto';
  el.innerHTML = `<button type="button" data-kind="auto" aria-pressed="${cur === 'auto'}" title="내용을 보고 색을 정해요">자동</button>` + EV_KINDS.map(([k, n]) => `<button type="button" class="k-${k}" data-kind="${k}" aria-pressed="${cur === k}" title="${n}"><i></i>${n}</button>`).join('');
}
function renderCal(){
  const m = S.month, wk = S.calView === 'week';
  $$('#cal-view button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === (wk ? 'week' : 'month')));
  $('#cal-prev').setAttribute('aria-label', wk ? '지난주' : '지난달'); $('#cal-next').setAttribute('aria-label', wk ? '다음 주' : '다음 달');
  $('#cal').classList.toggle('week', wk);
  $('#cal-legend').innerHTML = EV_KINDS.map(([k, n]) => `<span class="k-${k}"><i></i>${n}</span>`).join('');
  let start, weeks;
  if (wk){ const sd = fromYmd(S.selDate); start = addDays(sd, -sd.getDay()); weeks = 1; const e = addDays(start, 6); $('#cal-title').textContent = `${start.getMonth() + 1}.${start.getDate()} ~ ${e.getMonth() + 1}.${e.getDate()}`; }
  else { $('#cal-title').textContent = `${m.getFullYear()}. ${pad(m.getMonth()+1)}`; start = addDays(m, -m.getDay()); weeks = addDays(start, 35).getMonth() === m.getMonth() ? 6 : 5; }
  const tdy = ymd(today());
  let h = '<div class="cal-head">' + [...WD].map((w, i) => `<div class="${i === 0 ? 'sun' : i === 6 ? 'sat' : ''}">${w}</div>`).join('') + '</div><div class="cal-body">';
  for (let i = 0; i < weeks * 7; i++){
    const d = addDays(start, i), k = ymd(d), hol = HOLIDAYS[k];
    const evs = S.events.filter(e => e.date === k).sort(byTime);
    const tks = S.tasks.filter(t => t.due === k);
    const items = [
      ...evs.map(e => wk ? `<span class="it ev k-${evKind(e)} ${e.done ? 'done' : ''}">${e.time ? `<small>${e.time}</small> ` : ''}${esc(e.title)}</span>` : `<span class="it ev k-${evKind(e)} ${e.done ? 'done' : ''}" title="${esc((e.time ? e.time + ' ' : '') + e.title)}">${esc(e.title)}${e.time ? `<small> ${e.time}</small>` : ''}</span>`),
      ...tks.map(t => `<span class="it tk k-${tkKind(t)} ${t.done ? 'done' : ''}" title="${esc(kindName(tkKind(t)) + ' · ' + t.title)}">${t.done ? '☑' : '☐'} ${esc(t.title)}</span>`),
      ...Object.entries(lsOn(k).reduce((m, l) => { (m[l.prog] = m[l.prog] || []).push(l); return m; }, {})).map(([p, ls]) => `<span class="it ls" title="${esc(p + ' · ' + ls.map(l => clsLabel(l.cls) + ' ' + lsPerLabel(l.pers)).join(', '))}">${esc(p)} ${wk ? ls.map(l => esc(clsLabel(l.cls)) + ' ' + l.pers.join(',')).join(' · ') : ls.length + '반'}</span>`)
    ];
    const cls = ['cell', !wk && d.getMonth() !== m.getMonth() ? 'out' : '', k === tdy ? 'today' : '', k === S.selDate ? 'sel' : '',
      (d.getDay() === 0 || hol) ? 'red' : d.getDay() === 6 ? 'blue' : ''].join(' ');
    const label = `${d.getMonth()+1}월 ${d.getDate()}일${hol ? ' ' + hol : ''}, 일정 ${evs.length}개, 할 일 ${tks.length}개`;
    h += `<button type="button" class="${cls}" data-date="${k}" aria-label="${esc(label)}"><span class="dnum">${d.getDate()}</span>${hol ? `<span class="hol">${hol}</span>` : ''}${wk ? items.join('') : items.slice(0, 3).join('')}${!wk && items.length > 3 ? `<span class="more">+${items.length - 3}</span>` : ''}<span class="dots">${evs.slice(0,3).map(() => '<i></i>').join('')}${tks.slice(0,2).map(() => '<i class="t"></i>').join('')}</span></button>`;
  }
  $('#cal').innerHTML = h + '</div>';
}
function dueLabel(t){
  if (!t.due) return '';
  const n = dayDiff(t.due);
  if (t.done) return `<span class="mono">${fmtMD(t.due)}</span>`;
  if (n < 0) return `<span class="chip red">${fmtMD(t.due)} · ${-n}일 지남</span>`;
  if (n === 0) return `<span class="chip red">오늘까지</span>`;
  return `<span class="chip">${fmtMD(t.due)} · D-${n}</span>`;
}
function taskRow(t){
  const del = S.armed === 'task:' + t.id;
  return `<div class="li ${t.done ? 'done' : ''}">
    <button type="button" class="chk ${t.done ? 'on' : ''}" data-act="task-toggle" data-id="${t.id}" aria-label="${t.done ? '안 끝낸 일로 되돌리기' : '끝냄'}" ${S.canWrite ? '' : 'disabled'}></button>
    <div class="main">
      <button type="button" class="linkbtn title" data-act="task-edit" data-id="${t.id}"><span class="kdot k-${tkKind(t)}"></span>${esc(t.title)}</button>
      <div class="meta">${t.hold ? '<span class="chip warn">보류</span>' : dueLabel(t)}<span class="chip acc">${esc(clsLabel(t.who || '전체'))}</span>${S.canWrite ? `<select class="ksel" data-tk-kind="${t.id}" aria-label="할 일 색 바꾸기">${EV_KINDS.map(([k, n]) => `<option value="${k}" ${tkKind(t) === k ? 'selected' : ''}>${n}</option>`).join('')}</select>` : `<span class="chip">${kindName(tkKind(t))}</span>`}${t.repeat ? '<span class="chip">매년</span>' : ''}${t.every ? `<span class="chip">↻ ${EVERY_NAME[t.every]}</span>` : ''}${t.hold && S.canWrite ? `<button type="button" class="btn small" data-act="task-hold" data-id="${t.id}">다시 하기</button>` : ''}</div>
      ${t.note ? `<div class="note">${linkify(esc(t.note))}</div>` : ''}
    </div></div>`;
}
function renderTasks(){
  const my = S.profile.myClass;
  let list = S.tasks.slice();
  const f = S.taskFilter;
  if (f === 'open') list = list.filter(t => !t.done && !t.hold);
  if (f === 'hold') list = list.filter(t => !t.done && t.hold);
  if (f === 'mine') list = list.filter(t => !t.done && !t.hold && (t.who === '전체' || !t.who || (my && t.who === my)));
  if (f === 'repeat') list = list.filter(t => t.repeat);
  if (f === 'done') list = list.filter(t => t.done);
  const dk = t => t.due || '9999-99-99';
  list.sort(f === 'done' ? (a, b) => (b.doneAt || 0) - (a.doneAt || 0) : (a, b) => dk(a) < dk(b) ? -1 : dk(a) > dk(b) ? 1 : (a.createdAt || 0) - (b.createdAt || 0));
  $('#task-count').textContent = `남은 일 ${S.tasks.filter(t => !t.done).length}`;
  $('#repeat-tools').hidden = f !== 'repeat';
  let empty = '아직 할 일이 없어요. 바로 위 칸에 "11/27까지 동의서 수합"처럼 적어 보세요.';
  if (f === 'mine' && !my) empty = '나의 공간 → 우리 반 명단에서 맡은 반을 고르면 우리 반 일만 모아 보여요.';
  else if (f === 'mine') empty = `${my}이 맡은 남은 일이 없어요.`;
  else if (f === 'repeat') empty = '"매년"으로 표시한 일이 여기 모여요. 할 일을 눌러 "해마다 돌아오는 일"에 체크해 보세요.';
  else if (f === 'done') empty = '끝낸 일이 아직 없어요.';
  else if (f === 'hold') empty = '보류한 일이 없어요. "끝낼 일"에서 "보류"를 누르면 여기로 빠져요.';
  const subs = S.events.filter(e => evKind(e) === 'submit' && (f === 'done' ? e.done : f === 'repeat' || f === 'hold' ? false : !e.done) && (f !== 'mine' || isMineWho(e.who)));
  const merged = list.map(t => ({t, k:f === 'done' ? -(t.doneAt || 0) : dk(t)})).concat(subs.map(e => ({e, k:f === 'done' ? -(e.doneAt || 0) : e.date}))).sort((a, b) => a.k < b.k ? -1 : a.k > b.k ? 1 : 0);
  const subRow = e => { const n = dayDiff(e.date); return `<div class="li ${e.done ? 'done' : ''}"><button type="button" class="chk ${e.done ? 'on' : ''}" data-act="event-done" data-id="${e.id}" aria-label="${e.done ? '안 낸 것으로 되돌리기' : '제출 끝냄'}" ${S.canWrite ? '' : 'disabled'}></button>
    <div class="main"><div class="title"><span class="kdot k-submit"></span>${esc(e.title)}</div><div class="meta"><span class="chip ksub">제출 ${fmtMD(e.date)}${e.time ? ' ' + e.time : ''}</span>${!e.done && n < 0 ? `<span class="chip red">${-n}일 지남</span>` : ''}<span class="chip acc">${esc(clsLabel(e.who || '전체'))}</span></div></div></div>`; };
  $('#task-count').textContent = `남은 일 ${S.tasks.filter(t => !t.done && !t.hold).length + S.events.filter(e => evKind(e) === 'submit' && !e.done).length}`;
  $('#tasks').innerHTML = merged.length ? merged.map(x => x.t ? taskRow(x.t) : subRow(x.e)).join('') : `<p class="empty">${empty}</p>`;
}
function renderNotices(){
  const ae = document.activeElement;
  if (ae && $('#notices').contains(ae) && ae.matches('input, textarea')){ S.noticeLater = true; return; }
  S.noticeLater = false;
  const allN = S.notices;
  const usedK = NK.filter(k => allN.some(n => nkOf(n) === k));
  if (S.nk && S.nk !== 'all' && !usedK.includes(S.nk)) S.nk = 'all';
  $('#nk-tabs').hidden = usedK.length < 2;
  $('#nk-tabs').innerHTML = [['all', `전체 <small>${allN.length}</small>`]].concat(usedK.map(k => [k, `${k} <small>${allN.filter(n => nkOf(n) === k).length}</small>`])).map(([k, t]) => `<button type="button" class="stab" data-nk="${k}" ${(S.nk || 'all') === k ? 'aria-current="page"' : ''}>${t}</button>`).join('');
  if ($('#n-kind') && !$('#n-kind').options.length) $('#n-kind').innerHTML = '<option value="auto">알아서</option>' + NK.map(k => `<option>${k}</option>`).join('');
  const list = S.notices.filter(n => !S.nk || S.nk === 'all' || nkOf(n) === S.nk).slice().sort((a, b) => (b.pinned ? 1 : 0) - (a.pinned ? 1 : 0) || (b.createdAt || 0) - (a.createdAt || 0));
  $('#notice-count').textContent = list.length ? String(list.length) : '';
  const onMain = S.page === 'main' || !S.page;
  const MAIN_N = 4;
  const shown = onMain ? list.slice(0, MAIN_N) : list;
  const more = list.length - shown.length;
  $('#notices').innerHTML = (list.length ? shown.map(n => {
    const armed = S.armed === 'notice:' + n.id;
    const canDel = S.canWrite && (!n.createdBy || n.createdBy === S.uid || S.isOwner);
    return `<div class="li notice ${n.pinned ? 'pinned' : ''}"><div class="main">
      <div class="title">${n.pinned ? '<span class="pin">고정 </span>' : ''}${nkOf(n) !== '공지' ? `<span class="chip nk">${nkOf(n)}</span> ` : ''}${esc(n.title)}</div>
      ${n.body ? `<div class="body">${linkify(esc(n.body))}</div>` : ''}
      ${n.imgs && n.imgs.length ? `<div class="thumbs">${thumbsHtml(n.imgs)}</div>` : ''}
      <div class="meta">${author(n.createdBy)} · <span class="mono">${n.createdAt ? fmtMD(ymd(new Date(n.createdAt))) : ''}</span>${n.poll ? '<span class="chip main-only">투표</span>' : ''}${(c => c ? `<span class="chip main-only">댓글 ${c}</span>` : '')(Object.values(n.comments || {}).filter(x => x && x.text).length)}</div>
      ${pollHtml(n)}${commentsHtml(n)}
    </div>${canDel ? `<div class="acts">
      <select class="ksel" data-nk-set="${n.id}" aria-label="종류 바꾸기">${NK.map(k => `<option ${nkOf(n) === k ? 'selected' : ''}>${k}</option>`).join('')}</select>
      ${!n.poll && S.canWrite && (n.createdBy === S.uid || S.isOwner) ? `<button type="button" class="btn small" data-act="poll-open" data-id="${n.id}">투표 붙이기</button>` : ''}
      <button type="button" class="btn small" data-act="notice-pin" data-id="${n.id}">${n.pinned ? '고정 풀기' : '고정'}</button>
      <button type="button" class="btn small ${armed ? 'armed' : 'danger'}" data-act="notice-del" data-id="${n.id}">${armed ? '정말 삭제' : '삭제'}</button></div>` : ''}</div>`;
  }).join('') : '<p class="empty">협의 결과나 학년 안내를 여기 남겨 두면 메신저에서 다시 찾지 않아도 돼요.</p>') + (more > 0 ? `<a class="n-more" href="#notices">지난 공지 ${more}개 더 보기 →</a>` : '');
}
const SUBJ = [['kor','국어'],['math','수학'],['soc','사회'],['sci','과학'],['eng','영어'],['mus','음악'],['art','미술'],['pe','체육'],['eth','도덕'],['cre','창체'],['etc','공통·기타']];
const subjName = k => (SUBJ.find(x => x[0] === k) || [null, '공통·기타'])[1];
function guessSubj(t){ t = String(t || ''); const m = [['kor',/국어|받아쓰기|문해|독서|글쓰기/],['math',/수학|연산|분수|도형|구구/],['soc',/사회|지도|역사/],['sci',/과학|실험/],['eng',/영어|english|phonics/i],['mus',/음악|리코더|노래|악기/],['art',/미술|그리기|만들기/],['pe',/체육|놀이체육|줄넘기/],['eth',/도덕|인성/],['cre',/창체|자율|동아리|진로|안전/]].find(([, re]) => re.test(t)); return m ? m[0] : 'etc'; }
function renderLinks(){
  const onPage = S.page === 'links';
  const cur = onPage ? (S.linkSubj || 'all') : 'all';
  const all = S.links.slice().sort((a, b) => (a.createdAt || 0) - (b.createdAt || 0));
  const subjOf = l => l.subj || guessSubj(l.title + ' ' + l.url);
  const list = cur === 'all' ? all : all.filter(l => subjOf(l) === cur);
  const cnt = {}; all.forEach(l => { const k = subjOf(l); cnt[k] = (cnt[k] || 0) + 1; });
  $('#link-subj').hidden = !onPage;
  const subjHid = new Set((((S.profile || {}).tabPrefs || {}).subj || {}).hidden || []);
  if (onPage) $('#link-subj').innerHTML = [['all', '전체']].concat(subjOrdered()).filter(([k]) => !subjHid.has(k) || k === cur).map(([k, n]) => `<a class="stab" href="#${k === 'all' ? 'links' : 'links-' + k}" ${cur === k ? 'aria-current="page"' : ''}>${n}${k === 'all' ? ` <small>${all.length}</small>` : cnt[k] ? ` <small>${cnt[k]}</small>` : ''}</a>`).join('') + (S.uid ? '<button type="button" class="stab add" id="subj-arr" title="과목 숨기기·순서 바꾸기" style="margin-left:auto;color:var(--muted)">과목 정리</button>' : '');
  if (document.activeElement !== $('#l-subj')) $('#l-subj').innerHTML = SUBJ.map(([k, n]) => `<option value="${k}" ${(cur === 'all' ? 'etc' : cur) === k ? 'selected' : ''}>${n}</option>`).join('');
  $('#link-count').textContent = all.length ? String(all.length) : '';
  const unitMode = onPage && cur !== 'all' && cur !== 'etc' && cur !== 'cre';
  $('#unit-bar').hidden = !unitMode; $('#l-addbox').hidden = unitMode;
  if (unitMode){ renderUnits(cur, list); return; }
  $('#links').innerHTML = list.length ? list.map(l => {
    const armed = S.armed === 'link:' + l.id;
    const ok = /^https?:\/\//i.test(l.url || '');
    return `<div class="li"><div class="main">
      ${ok ? `<a class="title" href="${esc(l.url)}" target="_blank" rel="noopener noreferrer" style="color:var(--accent)">${esc(l.title || l.url)}</a>` : `<span class="title">${esc(l.title)}</span>`}
      <div class="meta" style="overflow-wrap:anywhere">${onPage && S.canWrite ? `<select class="lsubj" data-link-subj="${l.id}" aria-label="과목 바꾸기">${SUBJ.map(([k, n]) => `<option value="${k}" ${subjOf(l) === k ? 'selected' : ''}>${n}</option>`).join('')}</select>` : `<span class="chip">${subjName(subjOf(l))}</span>`}${esc((l.url || '').replace(/^https?:\/\//, '').slice(0, 60))}</div>
    </div>${S.canWrite ? `<div class="acts"><button type="button" class="btn small ${armed ? 'armed' : 'danger'}" data-act="link-del" data-id="${l.id}">${armed ? '정말 삭제' : '삭제'}</button></div>` : ''}</div>`;
  }).join('') : `<p class="empty">${cur === 'all' ? '자주 여는 자료 사이트나 영상 링크를 모아 두세요.' : subjName(cur) + ' 자료가 아직 없어요. 아래 "+ 링크 추가"에서 과목을 ' + subjName(cur) + '(으)로 골라 넣어 주세요.'}</p>`;
}
$('#links').addEventListener('change', async e => { const sel = e.target.closest('[data-link-subj]'); if (!sel) return; try { await S.db.doc('links/' + sel.dataset.linkSubj).update({subj:sel.value}); } catch (er){ wErr(er, true); } });
/* ---------- 수업자료: 과목별 단원 목차 ---------- */
/* 출판사별 목차. 확인한 것만 넣어요. 없으면 "목차 고치기"로 한 번 붙여 넣어요 */
const UNIT_LIB = {
  '3': {
    math:{'지학사':{'1':['1. 덧셈과 뺄셈', '2. 평면도형', '3. 나눗셈', '4. 곱셈', '5. 길이와 시간', '6. 분수와 소수', '프로젝트'], '2':['1. 곱셈', '2. 원', '3. 나눗셈', '4. 무게와 들이', '5. 분수', '6. 그림그래프', '프로젝트']}},
    mus:{'지학사':{'1':['1. 음악과 만나요', '2. 음악을 열어요', '3. 음악과 놀아요', '4. 음악을 나누어요'], '2':['1. 음악과 만나요', '2. 음악을 열어요', '3. 음악과 놀아요', '4. 음악을 나누어요']}},
    pe:{'지학사':{'1':['1. 운동', '2. 스포츠', '3. 표현'], '2':['1. 운동', '2. 스포츠', '3. 표현']}},
    sci:{'아이스크림미디어':{'1':['1. 힘과 우리 생활', '2. 동물의 생활', '3. 식물의 생활', '4. 생물의 한살이'], '2':['안전하게 탐구하기', '1. 물체와 물질', '2. 지구와 바다', '3. 소리의 성질', '4. 감염병과 건강한 생활']}},
    kor:{'국정':{'1':['1. 생생하게 표현해요', '2. 분명하고 유창하게', '3. 짜임새 있는 글, 재미와 감동이 있는 글', '4. 중요한 내용을 찾아요', '5. 인물에게 마음을 전해요', '6. 자신 있게 읽고 써요', '독서 단원', '매체 단원'], '2':['독서 단원: 계획대로 차근차근 읽어요', '1. 경험과 관련지으며 이해해요', '2. 유창하게 읽고 발표해요', '3. 정확하게 글을 써요', '매체 단원: 온라인 상황에서 글을 써요', '4. 서로 존중하며 대화해요', '5. 사전으로 여는 세상', '6. 감상과 표현의 즐거움']}},
    eth:{'국정':{'1':['1. 나를 찾아 떠나는 여행', '2. 성실하게 사는 삶', '3. 함께하는 우리 가족', '4. 인공지능 로봇 연구소에 가요'], '2':['5. 너와 나의 공감', '6. 함께 가는 공정의 길', '7. 생명을 소중히 여기는 우리', '8. 더 나은 세상을 위한 탐구']}},
    soc:{'천재교과서(박)':{'1':['1. 우리가 사는 곳', '2. 일상에서 만나는 과거'], '2':['1. 사회 변화와 다양한 문화', '2. 옛날과 오늘날의 생활 모습']}},
    eng:{'천재교과서(함)':{'1':['1. Hello, ABC!', '2. Hi, I\'m Momo', 'Special 1', '3. What\'s This?', '4. Stand Up, Please', 'Special 2', '5. How Many Cows?', '6. Do You Have a Pencil?', 'Special 3'], '2':['7. What Color Is It?', '8. I Like Apples', 'Special 4', '9. Wow, It\'s Big!', '10. Can You Jump?', 'Special 5', '11. He\'s My Dad', '12. How\'s the Weather?', 'Special 6', 'Review']}},
    art:{'동아출판':{'1':['1. 조형 요소와 놀자', '2. 생활 속 미술 만나기', '3. 수채로 표현하기', '4. 움직이는 장난감', '5. 미술 작품 속으로', '창의·융합 프로젝트: 미술관과 박물관을 찾아서', '미술 탐험대: 마티스의 종이 오리기', '미술 놀이터: 꿀렁꿀렁 물 만난 그림'], '2':['6. 온몸으로 느껴요', '7. 자세히 보아요', '8. 함께 사는 우리 마을', '9. 디지털 도구로 그려요', '10. 먹으로 그린 그림', '창의·융합 프로젝트: 세계 명절 음식 만나기', '미술 탐험대: 신사임당의 초충도', '미술 놀이터: 팡팡! 풍선 폭죽 만들기']}}
  }
};
const UN = {open:new Set(), add:null, edit:false};
const gradeNum = () => { const m = String(S.settings.gradeName || '').match(/(\d)/); return m ? m[1] : '3'; };
const curSem = () => { const m = today().getMonth() + 1; return m >= 3 && m <= 7 ? '1' : '2'; };
function unitCfg(subj){ const u = (S.gunits || {})[subj] || {}; return {pub:u.pub || '', custom:u.custom || {}}; }
function unitLibPubs(subj){ return Object.keys(((UNIT_LIB[gradeNum()] || {})[subj]) || {}); }
function unitList(subj, sem){
  const c = unitCfg(subj), lib = (((UNIT_LIB[gradeNum()] || {})[subj] || {})[c.pub] || {})[sem];
  return (lib && lib.length ? lib : (c.custom[sem] || [])).slice();
}
async function unitSave(subj, patch){
  S.gunits = S.gunits || {}; S.gunits[subj] = Object.assign({}, S.gunits[subj] || {}, patch);
  try { await S.db.doc('grade/units').set(JSON.parse(JSON.stringify(S.gunits))); } catch (e){ wErr(e, true); }
}
function renderUnits(subj, list){
  const sem = UN.sem || curSem(), c = unitCfg(subj), pubs = unitLibPubs(subj), units = unitList(subj, sem);
  const can = S.canWrite;
  $('#unit-bar').innerHTML = `<div class="un-bar">
    <div class="seg" role="group" aria-label="학기">${['1', '2'].map(x => `<button type="button" data-unsem="${x}" aria-pressed="${sem === x}">${gradeNum()}-${x}</button>`).join('')}</div>
    <label class="row" style="gap:6px">출판사 <select id="un-pub" ${can ? '' : 'disabled'} style="width:auto"><option value="">${pubs.length ? '고르기' : '직접 만든 목차'}</option>${pubs.map(p => `<option ${c.pub === p ? 'selected' : ''}>${esc(p)}</option>`).join('')}<option value="__own" ${(c.pub && !pubs.includes(c.pub)) || UN.own ? 'selected' : ''}>${c.pub && !pubs.includes(c.pub) ? esc(c.pub) + ' (직접)' : '목록에 없어요'}</option></select></label>${UN.own ? `<input id="un-pubname" placeholder="출판사 이름 (예: 천재교과서)" style="width:180px" value="${esc(c.pub && !pubs.includes(c.pub) ? c.pub : '')}">` : ''}
    <span class="grow"></span>${can ? `<button type="button" class="btn small" id="un-jdo" title="학년 진도표(한글 파일)에서 모든 과목 단원을 한 번에 가져와요">진도표 올리기</button><button type="button" class="btn small" id="un-edit">${units.length ? '목차 고치기' : '목차 넣기'}</button>` : ''}</div>
    ${UN.edit ? `<div class="un-edit"><p class="hint" style="margin:0 0 4px">${esc(subjName(subj))} ${gradeNum()}-${sem} 단원을 한 줄에 하나씩 적거나 붙여 넣어요. 교과서 차례에서 단원 이름만 복사해 와도 돼요. 동학년 모두에게 같이 보여요.</p>
      <textarea id="un-text" rows="7" placeholder="1. 물체와 물질&#10;2. 지구와 바다&#10;3. 소리의 성질">${esc(units.join('\n'))}</textarea>
      <div class="row" style="margin-top:6px"><span class="grow"></span><button type="button" class="btn small" id="un-cancel">취소</button><button type="button" class="btn small primary" id="un-save">저장</button></div></div>` : ''}`;
  const keyOf = l => l.unit && l.unit.startsWith(sem + '|') ? l.unit.slice(2) : (l.unit ? '__other' : '');
  const groups = [['', '단원 무관']].concat(units.map((u, i) => [u, u]));
  const linkChip = l => `<a class="un-chip" href="${esc(/^https?:\/\//i.test(l.url || '') ? l.url : '#')}" target="_blank" rel="noopener noreferrer" title="${esc(l.url || '')}"><i></i>${esc(l.title || l.url)}</a>`;
  const rowLinks = key => list.filter(l => keyOf(l) === key);
  let h = groups.map(([key, name], gi) => {
    const ls = rowLinks(key), open = UN.open.has(gi);
    const nm0 = String(name).match(/^\s*(\d+)\s*[.)]?\s/);
    const num = gi === 0 || !nm0 ? `<span class="un-dot" ${gi === 0 ? '' : 'style="background:var(--warn)"'}></span>` : `<span class="un-n">${String(+nm0[1]).padStart(2, '0')}</span>`;
    const nm = gi === 0 ? name : name.replace(/^\s*\d+\s*[.)]?\s+/, '');
    return `<div class="un-row ${open ? 'open' : ''}"><div class="un-head" data-untg="${gi}">${num}<b>${esc(nm)}</b><span class="un-chips">${ls.slice(0, 6).map(linkChip).join('')}${ls.length > 6 ? `<span class="hint">+${ls.length - 6}</span>` : ''}</span><button type="button" class="un-plus" data-untg="${gi}" aria-label="${esc(nm)} ${open ? '접기' : '펼치기'}">${open ? '−' : '+'}</button></div>
      ${open ? `<div class="un-body">${ls.map(l => `<div class="un-li">${linkChip(l)}<span class="hint un-url">${esc((l.url || '').replace(/^https?:\/\//, ''))}</span><span class="grow"></span>${can ? `<select class="lsubj" data-unmove="${l.id}" aria-label="단원 옮기기"><option value="">단원 무관</option>${units.map(u => `<option value="${esc(u)}" ${keyOf(l) === u ? 'selected' : ''}>${esc(u.replace(/^\s*\d+\s*[.)]\s*/, ''))}</option>`).join('')}</select><button type="button" class="btn small ${S.armed === 'link:' + l.id ? 'armed' : 'danger'}" data-act="link-del" data-id="${l.id}">${S.armed === 'link:' + l.id ? '정말 삭제' : '삭제'}</button>` : ''}</div>`).join('') || '<p class="hint" style="margin:2px 0">아직 자료가 없어요.</p>'}
        ${can ? `<form class="un-add" data-unadd="${esc(key)}"><input type="text" placeholder="자료 이름" aria-label="자료 이름"><input type="text" inputmode="url" placeholder="https:// 주소" aria-label="자료 주소"><button type="submit" class="btn small primary">넣기</button></form>` : ''}</div>` : ''}</div>`;
  }).join('');
  const other = list.filter(l => keyOf(l) === '__other');
  if (other.length) h += `<p class="hint" style="margin:8px 0 0">다른 학기 단원에 넣은 자료 ${other.length}개는 ${gradeNum()}-${sem === '1' ? '2' : '1'}을 누르면 보여요.</p>`;
  if (!units.length && !UN.edit) h = `<div class="jd-empty" style="margin-bottom:8px">${esc(subjName(subj))} ${gradeNum()}-${sem} 목차가 아직 없어요.${can ? ' 위 "진도표 올리기"로 학년 진도표(한글 파일)를 올리면 모든 과목 단원이 한 번에 들어가요. "목차 넣기"로 단원 이름을 직접 붙여 넣어도 돼요. 동학년 모두에게 같이 보여요.' : ''}</div>` + h;
  $('#links').innerHTML = `<div class="un-list">${h}</div>`;
}
$('#unit-bar').addEventListener('click', async e => {
  const sb = e.target.closest('[data-unsem]'); if (sb){ UN.sem = sb.dataset.unsem; UN.open.clear(); renderLinks(); return; }
  const subj = S.linkSubj;
  if (e.target.id === 'un-edit'){ UN.edit = !UN.edit; renderLinks(); if (UN.edit) $('#un-text').focus(); return; }
  if (e.target.id === 'un-cancel'){ UN.edit = false; renderLinks(); return; }
  if (e.target.id === 'un-jdo'){ $('#un-file').value = ''; $('#un-file').click(); return; }
  if (e.target.id === 'un-save'){
    const sem = UN.sem || curSem(), lines = $('#un-text').value.split('\n').map(x => x.replace(/\s+/g, ' ').trim()).filter(Boolean).slice(0, 40);
    const c = unitCfg(subj), custom = Object.assign({}, c.custom, {[sem]:lines});
    const libHas = unitLibPubs(subj).includes(c.pub);
    UN.edit = false; await unitSave(subj, {custom, pub:libHas ? '' : c.pub}); renderLinks(); toast(`${subjName(subj)} ${gradeNum()}-${sem} 단원 ${lines.length}개를 넣었어요.`);
  }
});
$('#unit-bar').addEventListener('change', async e => {
  if (e.target.id !== 'un-pub' && e.target.id !== 'un-pubname') return;
  let v = e.target.value;
  if (e.target.id === 'un-pubname'){ await unitSave(S.linkSubj, {pub:e.target.value.trim()}); UN.own = false; renderLinks(); return; }
  if (v === '__own'){ UN.own = true; renderLinks(); const i = $('#un-pubname'); if (i) i.focus(); return; }
  UN.own = false; await unitSave(S.linkSubj, {pub:v}); renderLinks();
});
/* 진도표(.hwp/.hwpx)에서 과목별 "단원명" 칸을 모아 목차로 넣어요 */
function cfbStreams(buf){
  const dv = new DataView(buf), u8 = new Uint8Array(buf), END = 0xFFFFFFFA;
  if (dv.getUint32(0, true) !== 0xE011CFD0) throw new Error('cfb');
  const ss = 1 << dv.getUint16(30, true), mss = 1 << dv.getUint16(32, true), q = ss / 4;
  const nfat = dv.getUint32(44, true), dirStart = dv.getUint32(48, true), cutoff = dv.getUint32(56, true), miniStart = dv.getUint32(60, true);
  let x = dv.getUint32(68, true), nd = dv.getUint32(72, true);
  const off = i => 512 + i * ss, fatSecs = [];
  for (let k = 0; k < 109; k++) fatSecs.push(dv.getUint32(76 + k * 4, true));
  while (x < END && nd-- > 0){ for (let k = 0; k < q - 1; k++) fatSecs.push(dv.getUint32(off(x) + k * 4, true)); x = dv.getUint32(off(x) + ss - 4, true); }
  const fat = new Uint32Array(nfat * q);
  fatSecs.slice(0, nfat).forEach((f, j) => { for (let k = 0; k < q; k++) fat[j * q + k] = dv.getUint32(off(f) + k * 4, true); });
  const cat = parts => { const o = new Uint8Array(parts.reduce((a, p) => a + p.length, 0)); let p = 0; parts.forEach(s => { o.set(s, p); p += s.length; }); return o; };
  const chain = st => { const ps = []; let g = 0; while (st < END && g++ < 1e6){ ps.push(u8.subarray(off(st), off(st) + ss)); st = fat[st]; } return cat(ps); };
  const dirs = chain(dirStart), dd = new DataView(dirs.buffer, dirs.byteOffset, dirs.byteLength), ents = [];
  for (let i = 0; i < dirs.length / 128; i++){
    const b = i * 128, nl = dd.getUint16(b + 64, true);
    let name = ''; for (let j = 0; j + 2 < nl; j += 2) name += String.fromCharCode(dd.getUint16(b + j, true));
    ents.push({name, typ:dirs[b + 66], l:dd.getUint32(b + 68, true), r:dd.getUint32(b + 72, true), c:dd.getUint32(b + 76, true), st:dd.getUint32(b + 116, true), sz:dd.getUint32(b + 120, true)});
  }
  const ministream = chain(ents[0].st), mf = miniStart < END ? chain(miniStart) : new Uint8Array(0), mdv = new DataView(mf.buffer, mf.byteOffset, mf.byteLength);
  const read = e => {
    if (e.sz < cutoff){ const ps = []; let st = e.st, g = 0; while (st < END && g++ < 1e6){ ps.push(ministream.subarray(st * mss, (st + 1) * mss)); st = mdv.getUint32(st * 4, true); } return cat(ps).subarray(0, e.sz); }
    return chain(e.st).subarray(0, e.sz);
  };
  const out = {}, seen = new Set();
  const walk = (i, pre) => { if (i >= END || seen.has(i) || !ents[i]) return; seen.add(i); const e = ents[i]; walk(e.l, pre); walk(e.r, pre); const p = pre + '/' + e.name; if (e.typ === 2) out[p] = () => read(e); if (e.typ === 1) walk(e.c, p); };
  walk(ents[0].c, '');
  return out;
}
/* 뒤에 남는 바이트가 있어도 풀린 데까지는 써요 (크롬은 이때 오류를 내요) */
async function inflateLoose(u8){
  const rd = new Blob([u8]).stream().pipeThrough(new DecompressionStream('deflate-raw')).getReader(), ps = [];
  try { for (;;){ const {done, value} = await rd.read(); if (done) break; ps.push(value); } } catch (e){ if (!ps.length) throw e; }
  const o = new Uint8Array(ps.reduce((a, p) => a + p.length, 0)); let p = 0; ps.forEach(x => { o.set(x, p); p += x.length; }); return o;
}
async function hwp5Tables(buf){
  const fs = cfbStreams(buf); if (!fs['/FileHeader']) throw new Error('hwp');
  const comp = fs['/FileHeader']()[36] & 1;
  const secs = Object.keys(fs).filter(p => /^\/BodyText\/Section\d+$/.test(p)).sort((a, b) => +a.split('Section')[1] - +b.split('Section')[1]);
  const tables = [];
  for (const p of secs){
    let b = fs[p]();
    if (comp) b = await inflateLoose(b);
    const dv = new DataView(b.buffer, b.byteOffset, b.byteLength), stack = [];
    let cell = null, i = 0;
    while (i + 4 <= b.length){
      const h = dv.getUint32(i, true), tag = h & 0x3FF, lv = (h >>> 10) & 0x3FF; let sz = h >>> 20; i += 4;
      if (sz === 0xFFF){ sz = dv.getUint32(i, true); i += 4; }
      while (stack.length && lv < stack[stack.length - 1].lv) stack.pop();
      const tb = stack[stack.length - 1];
      if (tag === 77){ const t = {lv, cells:[]}; tables.push(t); stack.push(t); cell = null; }
      else if (tag === 72 && tb && lv === tb.lv && sz >= 16){ cell = {c:dv.getUint16(i + 8, true), r:dv.getUint16(i + 10, true), t:''}; tb.cells.push(cell); }
      else if (tag === 67 && cell){
        let s = '', j = i; const e = i + sz;
        while (j + 1 < e){ const c = dv.getUint16(j, true); if ((c >= 1 && c <= 8) || c === 11 || c === 12 || (c >= 14 && c <= 23)) j += 16; else if (c === 9){ s += ' '; j += 16; } else if (c === 10 || c === 13){ s += ' '; j += 2; } else { if (c >= 32) s += String.fromCharCode(c); j += 2; } }
        cell.t = (cell.t + ' ' + s).replace(/\s+/g, ' ').trim();
      }
      i += sz;
    }
  }
  return tables.map(t => t.cells);
}
function hwpxTables(xmls){
  const tables = [], lname = el => el.localName, kids = (el, n) => [...el.children].filter(c => lname(c) === n);
  const cellText = tc => [...tc.getElementsByTagNameNS('*', 'p')].map(p => [...p.getElementsByTagNameNS('*', 't')].map(t => t.textContent).join('')).join(' ').replace(/\s+/g, ' ').trim();
  xmls.forEach(xml => {
    const doc = new DOMParser().parseFromString(xml, 'application/xml');
    [...doc.getElementsByTagNameNS('*', 'tbl')].forEach(tbl => {
      tables.push(kids(tbl, 'tr').flatMap((tr, ri) => kids(tr, 'tc').map(tc => { const a = kids(tc, 'cellAddr')[0]; return {c:+(a && a.getAttribute('colAddr') || 0), r:+(a && a.getAttribute('rowAddr') || ri), t:cellText(tc)}; })));
    });
  });
  return tables;
}
const JDO_SUBJ = {'국어':'kor', '수학':'math', '사회':'soc', '과학':'sci', '영어':'eng', '음악':'mus', '미술':'art', '체육':'pe', '도덕':'eth'};
const JDO_SKIP = /^(준비|실천|다가가기|이해하기\s*\d*|실천하기|돌아보기|단원\s*도입|단원\s*마무리|학습\s*내용\s*정리|단원명|단원)$/;
function jdoParse(tables){
  const res = {}; let subj = null, col = null, sem = '', grade = '';
  tables.forEach(cells => {
    const head = cells.find(x => /^단원(명)?$/.test(x.t.replace(/\s/g, '')));
    cells.forEach(x => {
      if (head && x.r >= head.r) return;
      const m = x.t.match(/^\s*([가-힣]+)\s*(?:\(.*?\))?\s*(?:교육과정|연간\s*지도\s*계획|진도표)/); if (m) subj = JDO_SUBJ[m[1]] || '';
      const s = x.t.match(/(\d)\s*학기/); if (s) sem = s[1];
      const g = x.t.match(/(\d)\s*학년/); if (g) grade = g[1];
    });
    if (head) col = head.c;
    if (!subj || col == null) return;
    const list = res[subj] = res[subj] || [];
    cells.filter(x => x.c === col && (!head || x.r > head.r)).sort((a, b) => a.r - b.r).forEach(x => {
      const t = x.t.replace(/\s+/g, ' ').trim();
      if (!t || /^[◆※]/.test(t) || JDO_SKIP.test(t) || list.includes(t)) return;
      list.push(t);
    });
  });
  Object.keys(res).forEach(k => { res[k] = res[k].slice(0, 40); if (!res[k].length) delete res[k]; });
  return {units:res, sem, grade};
}
$('#un-file').addEventListener('change', async e => {
  const f = e.target.files && e.target.files[0]; if (!f || !S.canWrite) return;
  try {
    const buf = await f.arrayBuffer();
    let tables;
    if (new DataView(buf).getUint32(0, true) === 0xE011CFD0) tables = await hwp5Tables(buf);
    else { const xs = await unzipText(buf, n => /^Contents\/section\d+\.xml$/.test(n)); tables = hwpxTables(Object.keys(xs).sort((a, b) => a.localeCompare(b, 'en', {numeric:true})).map(k => xs[k])); }
    const {units, sem:fs, grade} = jdoParse(tables), keys = Object.keys(units);
    if (!keys.length){ toast('진도표에서 "단원명" 칸을 찾지 못했어요. 과목 이름과 "단원명" 칸이 있는 한글 표인지 확인해 주세요.'); return; }
    const sem = fs || UN.sem || curSem(), done = [], kept = [];
    S.gunits = S.gunits || {};
    keys.forEach(k => {
      const c = unitCfg(k), lib = (((UNIT_LIB[gradeNum()] || {})[k] || {})[c.pub] || {})[sem];
      if (lib && lib.length){ kept.push(subjName(k)); return; }
      S.gunits[k] = Object.assign({}, S.gunits[k] || {}, {custom:Object.assign({}, c.custom, {[sem]:units[k]})});
      done.push(subjName(k));
    });
    if (done.length){ try { await S.db.doc('grade/units').set(JSON.parse(JSON.stringify(S.gunits))); } catch (er){ wErr(er, true); } }
    UN.sem = sem; UN.open.clear(); renderLinks();
    toast(`${gradeNum()}-${sem} ${done.length ? done.join('·') + ' 단원을 넣었어요.' : '새로 넣은 과목이 없어요.'}${kept.length ? ` ${kept.join('·')}은(는) 고른 출판사 목차가 있어서 그대로 뒀어요.` : ''}${grade && grade !== gradeNum() ? ` (파일은 ${grade}학년 진도표예요)` : ''}`);
  } catch (er){ console.error(er); toast('파일을 읽지 못했어요. 한글 파일(.hwp, .hwpx)인지 확인해 주세요.'); }
});
$('#links').addEventListener('click', e => {
  const tg = e.target.closest('[data-untg]'); if (!tg || e.target.closest('a')) return;
  const i = +tg.dataset.untg; UN.open.has(i) ? UN.open.delete(i) : UN.open.add(i); renderLinks();
});
$('#links').addEventListener('submit', async e => {
  const f = e.target.closest('[data-unadd]'); if (!f) return; e.preventDefault();
  const [ti, ui] = f.querySelectorAll('input'); let url = ui.value.trim(), title = ti.value.trim();
  if (url && !/^https?:\/\//i.test(url)) url = 'https://' + url;
  if (!url){ toast('주소를 적어 주세요.'); ui.focus(); return; }
  const key = f.dataset.unadd, sem = UN.sem || curSem();
  try { await S.db.collection('links').add({title:title || url, url, subj:S.linkSubj, unit:key ? sem + '|' + key : '', createdBy:S.uid, createdAt:Date.now()}); toast('자료를 넣었어요.'); }
  catch (er){ wErr(er, true); }
});
$('#links').addEventListener('change', async e => {
  const sel = e.target.closest('[data-unmove]'); if (!sel) return;
  const sem = UN.sem || curSem();
  try { await S.db.doc('links/' + sel.dataset.unmove).update({unit:sel.value ? sem + '|' + sel.value : ''}); } catch (er){ wErr(er, true); }
});
function renderDay(){
  const dp = document.querySelector('.daypanel'); if (dp) dp.classList.toggle('is-today', S.selDate === ymd(today()));
  const k = S.selDate;
  $('#day-title').textContent = fmtLong(k);
  $('#day-hol').textContent = HOLIDAYS[k] || '';
  const evs = S.events.filter(e => e.date === k).sort(byTime);
  const tks = S.tasks.filter(t => t.due === k);
  const rows = evs.map(e => {
    const armed = S.armed === 'event:' + e.id;
    const kd = evKind(e);
    return `<div class="li ${e.done ? 'done' : ''}"><span class="time">${e.time || '종일'}</span><div class="main"><div class="title"><span class="kdot k-${kd}"></span>${esc(e.title)}${kd === 'submit' ? ` <button type="button" class="btn small" data-act="event-done" data-id="${e.id}" ${S.canWrite ? '' : 'disabled'}>${e.done ? '제출함 ✓' : '제출 끝냄'}</button>` : ''}</div>
      <div class="meta"><span class="chip acc">${esc(clsLabel(e.who || '전체'))}</span>${S.canWrite ? `<select class="ksel" data-ev-kind="${e.id}" aria-label="일정 색 바꾸기">${EV_KINDS.map(([k, n]) => `<option value="${k}" ${kd === k ? 'selected' : ''}>${n}</option>`).join('')}</select>` : `<span class="chip">${kindName(kd)}</span>`}</div></div>
      <div class="acts">${calBtn('ev:' + e.id)}${S.canWrite ? `<button type="button" class="btn small ${armed ? 'armed' : 'danger'}" data-act="event-del" data-id="${e.id}">${armed ? '정말 삭제' : '삭제'}</button>` : ''}</div></div>`;
  }).concat(tks.map(taskRow));
  $('#day-items').innerHTML = rows.length ? rows.join('') : `<p class="empty">이 날 학년 일정이 없어요.${S.canWrite ? ' 위 칸에 날짜 없이 적으면 이 날에 들어가요.' : ''}</p>`;
  const d = S.daily;
  if (!S.dailyDirty){
    $('#d-plan').value = d ? (d.plan || '') : '';
    $('#d-notice').value = d ? (d.notice || '') : '';
    S.dailyImgs = d && Array.isArray(d.imgs) ? d.imgs.slice() : [];
  }
  renderDailyThumbs();
  $('#d-meta').innerHTML = d && d.updatedAt ? `마지막 저장 ${author(d.updatedBy)} · <span class="mono">${new Date(d.updatedAt).toLocaleTimeString('ko-KR', {hour:'2-digit', minute:'2-digit'})}</span>` : (S.dailyDirty ? '저장하지 않은 내용이 있어요' : '');
}
function renderGaPreview(){
  const v = $('#ga-input').value.trim();
  if (!v){ $('#ga-preview').innerHTML = ''; return; }
  const p = parseLine(v);
  const chips = [];
  if (S.gaType === 'event'){
    chips.push(`<span class="chip acc">날짜 <b>${fmtMD(p.date || S.selDate)}</b>${p.date ? '' : ' (고른 날)'}</span>`);
    chips.push(`<span class="chip">시각 <b>${p.time || '종일'}</b></span>`);
    const kk = S.gaKind && S.gaKind !== 'auto' ? S.gaKind : guessKind(p.text);
    chips.push(`<span class="chip kchip k-${kk}"><i></i>${kindName(kk)}${S.gaKind && S.gaKind !== 'auto' ? '' : ' (자동)'}</span>`);
  } else {
    chips.push(`<span class="chip acc">마감 <b>${p.date ? fmtMD(p.date) : '없음'}</b></span>`);
    if (p.repeat) chips.push('<span class="chip">매년</span>');
    if (p.every) chips.push(`<span class="chip">↻ ${EVERY_NAME[p.every]}${p.eom ? ' 말일' : ''}</span>`);
    const kk = S.gaKind && S.gaKind !== 'auto' ? S.gaKind : guessKind(p.text);
    chips.push(`<span class="chip kchip k-${kk}"><i></i>${kindName(kk)}${S.gaKind && S.gaKind !== 'auto' ? '' : ' (자동)'}</span>`);
  }
  chips.push(`<span class="chip">대상 <b>${esc(p.who ? clsLabel(p.who) : '학년 전체')}</b></span>`);
  chips.push(`<span class="chip">내용 <b>${esc(p.text || '—')}</b></span>`);
  $('#ga-preview').innerHTML = chips.join('');
}
function renderGradeToday(){
  const d = today(), k = ymd(d);
  $('#th-m').textContent = `${d.getFullYear()}년 ${d.getMonth()+1}월`;
  $('#th-day').textContent = d.getDate();
  $('#th-wd').textContent = WD[d.getDay()] + '요일' + (HOLIDAYS[k] ? ' · ' + HOLIDAYS[k] : '');
  const evs = S.events.filter(e => e.date === k).sort(byTime);
  const dueToday = S.tasks.filter(t => !t.done && t.due === k);
  const late = S.tasks.filter(t => !t.done && t.due && t.due < k);
  let h = evs.map(e => `<div class="th-ev"><span class="th-time">${e.time || '종일'}</span><span class="th-title">${esc(e.title)}</span>${e.who && e.who !== '전체' ? `<span class="chip acc">${esc(clsLabel(e.who))}</span>` : ''}</div>`).join('');
  /* 오늘 마감인 학년 할 일은 오른쪽 '이번 주까지 끝낼 일'에 보여요 */
  if (!h){
    const next = S.events.filter(e => e.date > k).sort((a, b) => a.date < b.date ? -1 : a.date > b.date ? 1 : byTime(a, b))[0];
    h = `<p class="th-empty">오늘은 학년 일정이 없어요.</p>` + (next ? `<p class="hint" style="margin:0">다음 일정 · <span class="mono">${fmtMD(next.date)}</span> ${next.time ? next.time + ' ' : ''}${esc(next.title)}</p>` : '');
  }
  $('#th-list').innerHTML = h;
  renderWeekTasks();
  const dt = S.dailyToday;
  $('#th-alrim').innerHTML = dt && dt.notice ? esc(dt.notice) : (dt && dt.imgs && dt.imgs.length ? '' : '<span class="hint">아직 오늘 알림장이 없어요.</span>');
  $('#th-thumbs').innerHTML = thumbsHtml(dt && dt.imgs);
  renderMeal();
}
function weekEnd(){ const d = today(); return ymd(addDays(d, (7 - d.getDay()) % 7)); }
function weekFri(){ const d = today(); const n = (5 - d.getDay() + 7) % 7; return ymd(addDays(d, d.getDay() === 6 ? 6 : n)); }
const isMineWho = w => !w || w === '전체' || (S.profile.myClass && w === S.profile.myClass);
function dueHtml(mineOnly, lim){
  const k = ymd(today()), we0 = weekEnd(), we = ymd(addDays(fromYmd(we0), 7));
  const okWho = x => !mineOnly || isMineWho(x.who);
  const subs = S.events.filter(e => evKind(e) === 'submit' && e.date && e.date <= we && !e.done && e.date >= ymd(addDays(today(), -60)) && okWho(e)).map(e => ({id:e.id, title:e.title, due:e.date, time:e.time, who:e.who, ev:true}));
  const open = S.tasks.filter(t => !t.done && !t.hold && t.due && t.due <= we && okWho(t)).concat(subs).sort((a, b) => a.due < b.due ? -1 : a.due > b.due ? 1 : (a.prio === '높음' ? -1 : 1));
  const wkStart = ymd(addDays(fromYmd(we0), -6));
  const doneWk = S.tasks.filter(t => t.done && t.doneAt && ymd(new Date(t.doneAt)) >= wkStart && okWho(t)).concat(S.events.filter(e => e.done && e.doneAt && ymd(new Date(e.doneAt)) >= wkStart && okWho(e)));
  const holdN = S.tasks.filter(t => !t.done && t.hold && okWho(t)).length;
  const laterN = S.tasks.filter(t => !t.done && !t.hold && t.due && t.due > we && okWho(t)).length + S.events.filter(e => evKind(e) === 'submit' && !e.done && e.date > we && okWho(e)).length;
  const dis = S.canWrite ? '' : 'disabled';
  const row = t => {
    const n = dayDiff(t.due), late = n < 0;
    const lab = late ? `<span class="chip red">${-n}일 밀림</span>` : n === 0 ? '<span class="chip red">오늘</span>' : `<span class="chip">${WD[fromYmd(t.due).getDay()]} · D-${n}</span>`;
    if (t.ev) return `<div class="wk-t sub ${late ? 'late' : ''}"><button type="button" class="chk" data-act="event-done" data-id="${t.id}" aria-label="제출 끝냄" ${dis}></button>
      <div class="m"><span class="t"><span class="kdot k-submit"></span>${esc(t.title)}</span><span class="meta"><span class="chip ksub">제출 ${fmtMD(t.due)}${t.time ? ' ' + t.time : ''}</span>${late ? lab : n === 0 ? lab : ''}${t.who && t.who !== '전체' ? `<span class="chip acc">${esc(clsLabel(t.who))}</span>` : ''}</span></div></div>`;
    const tk = tkKind(t);
    return `<div class="wk-t ${late ? 'late' : ''} ${tk === 'submit' ? 'sub' : ''}"><button type="button" class="chk" data-act="task-toggle" data-id="${t.id}" aria-label="끝냄" ${dis}></button>
      <div class="m"><span class="t"><span class="kdot k-${tk}"></span>${t.prio === '높음' ? '★ ' : ''}${esc(t.title)}${t.every ? ` <small title="${EVERY_NAME[t.every]} 반복">↻</small>` : ''}</span><span class="meta">${tk === 'submit' ? `<span class="chip ksub">제출 ${fmtMD(t.due)}</span>${late || n === 0 ? lab : ''}` : lab}${t.who && t.who !== '전체' ? `<span class="chip acc">${esc(clsLabel(t.who))}</span>` : ''}</span></div>
      ${S.canWrite ? `<button type="button" class="btn small" data-act="task-defer" data-id="${t.id}" title="다음 주 같은 요일로 미루기">미루기</button><button type="button" class="btn small" data-act="task-hold" data-id="${t.id}" title="지금은 못 하는 일로 빼 두기">보류</button>` : ''}</div>`;
  };
  const grp = [['밀린 일', open.filter(t => t.due < k)], ['이번 주', open.filter(t => t.due >= k && t.due <= we0)], ['다음 주', open.filter(t => t.due > we0)]].filter(g => g[1].length);
  if (lim){
    const flat = []; grp.forEach(([n, l]) => l.forEach(t => flat.push([n, t])));
    const show = flat.slice(0, lim), more = flat.length - show.length;
    const html = show.length ? show.map(([n, t]) => `<div class="wk-cell"><span class="wk-gl ${n === '밀린 일' ? 'late' : ''}">${n}</span>${row(t)}</div>`).join('') + (more || holdN ? `<a class="wk-more" href="#tasks">${more ? `+${more}개 더` : ''}${more && holdN ? '<br>' : ''}${holdN ? `<small>보류 ${holdN}</small>` : ''}</a>` : '')
      : `<p class="th-empty" style="font-size:13.5px;margin:0">다음 주까지 끝낼 학년 일이 없어요.${laterN ? ` <a class="hint" href="#tasks">그 뒤 ${laterN}개 →</a>` : ''}</p>`;
    return {html, n:open.length, cols:show.length + (more || holdN ? 1 : 0)};
  }
  const html = (open.length ? grp.map(([n, l]) => `<h4 class="wk-g">${n} <span>${l.length}</span></h4>` + l.map(row).join('')).join('') : '<p class="th-empty" style="font-size:14px">다음 주까지 끝낼 학년 일이 없어요.</p>')
    + (laterN ? `<a class="hint wk-later" href="#tasks">그 뒤에 할 일 ${laterN}개 더 보기 →</a>` : '')
    + (holdN ? `<a class="hint wk-later" href="#tasks" data-hold-link="1">보류한 일 ${holdN}개 →</a>` : '')
    + (doneWk.length ? `<p class="hint wk-done">이번 주 끝낸 일 ${doneWk.length}개 · ${doneWk.slice(0, 4).map(t => esc(t.title)).join(', ')}${doneWk.length > 4 ? ' …' : ''}</p>` : '');
  return {html, n:open.length};
}
const WIDE_MQ = window.matchMedia ? matchMedia('(min-width:1500px)') : {matches:false};
function renderWeekTasks(){
  const wide = WIDE_MQ.matches, r = dueHtml(false, wide ? 3 : 0);
  $('#th-wk-n').textContent = r.n ? `${r.n}개 남음` : '';
  $('#th-wk').innerHTML = r.html; $('#th-wk').classList.toggle('row1', wide); $('#th-wk').style.setProperty('--n', r.cols || 1);
  if (S.space === 'me') renderMeGrade();
}
/* 큰 모니터 학년 첫 화면: 학년 참고사항을 입력 칸 아래로 옮겨요 */
function placeGmemo(){
  const card = document.querySelector('.gmemo-card'), add = document.querySelector('#v-grade .addcard'); if (!card || !add) return;
  if (!placeGmemo.home) placeGmemo.home = {parent:card.parentElement, next:card.nextElementSibling};
  const wide = WIDE_MQ.matches && document.body.dataset.page === 'main';
  if (wide && card.previousElementSibling !== add) add.after(card);
  else if (!wide && card.parentElement !== placeGmemo.home.parent) placeGmemo.home.parent.insertBefore(card, placeGmemo.home.next);
}
try { WIDE_MQ.addEventListener('change', () => { renderWeekTasks(); placeGmemo(); }); } catch (e){}
function renderMeGrade(){
  const el = $('#me-grade'); if (!el) return;
  const my = S.profile.myClass;
  const r = dueHtml(true);
  $('#mg-due-n').textContent = r.n ? `${r.n}개` : '';
  $('#mg-due').innerHTML = r.html;
  const k = ymd(today()), until = ymd(addDays(today(), 7));
  const evs = S.events.filter(e => e.date >= k && e.date <= until && isMineWho(e.who) && evKind(e) !== 'submit').sort((a, b) => a.date < b.date ? -1 : a.date > b.date ? 1 : byTime(a, b));
  $('#mg-ev').innerHTML = evs.length ? evs.map(e => `<li class="${e.done ? 'done' : ''}"><span class="d mono">${mdShort(e.date)}(${WD[fromYmd(e.date).getDay()]})</span><span class="t"><span class="kdot k-${evKind(e)}"></span>${esc(e.title)}${e.time ? ` <small class="mono">${e.time}</small>` : ''}${e.who && e.who !== '전체' ? ` <span class="chip acc">${esc(clsLabel(e.who))}</span>` : ''}</span></li>`).join('') : '<li class="hint">앞으로 7일 동안 학년 일정이 없어요.</li>';
  $('#mg-who').textContent = my ? `학년 전체 + ${my}` : '학년 전체 (명부 탭에서 맡은 반을 고르면 우리 반 일도 모여요)';
}
function renderGrade(){ renderKindPick(); renderGMemo(); renderHeader(); renderTabList(); renderPageHead(); renderGradeToday(); renderCal(); renderDay(); renderTasks(); renderNotices(); renderLinks(); resolveNames(); }

/* ---------- me render ---------- */
function attLabel(a){ return a ? (a.reason === '출석인정' ? `출석인정 ${a.kind}` : `${a.reason}${a.kind}`) : ''; }
const mdShort = k => { const d = fromYmd(k); return `${d.getMonth()+1}/${d.getDate()}`; };
const covers = (e, k) => e.date === k || !!(e.end && e.date && e.date <= k && k <= e.end);
function prioTag(p){ return p === '높음' ? '<span class="prio-high">높음</span>' : p === '낮음' ? '<span class="prio-low">낮음</span>' : ''; }
function entryRow(e, showDate){
  const stu = (e.students || []).map(stuName).join(', ');
  const isTodo = e.cat === '할일';
  const left = isTodo ? `<button type="button" class="chk ${e.done ? 'on' : ''}" data-act="entry-toggle" data-id="${e.id}" aria-label="끝냄 표시"></button>`
    : `<span class="time">${showDate ? (e.date ? mdShort(e.date) + (e.end ? '~' + mdShort(e.end) : '') : '') : (e.end ? '~' + mdShort(e.end) : (e.time || ''))}</span>`;
  return `<div class="li entry ${isTodo && e.done ? 'done' : ''}">${left}
    <div class="main">
      <div class="meta" style="margin-top:0"><span class="pill" ${catStyle(e.cat)}>${e.cat}</span>${e.area ? `<span class="chip">${esc(e.area)}</span>` : ''}${e.hold ? '<span class="chip warn">보류</span>' : ''}${(e.cat === '상담' || e.cat === '학부모') && cnsWay(e.text) ? `<span class="chip way">${cnsWay(e.text)}</span>` : ''}${prioTag(e.prio)}${e.att ? `<span class="pill" ${catStyle('출결')}>${attLabel(e.att)}</span>` : ''}${(e.students || []).map(n => `<button type="button" class="stu-link" data-open-stu="${n}" title="학생 카드 열기">${esc(stuName(n))}</button>`).join('')}${(showDate || isTodo) && e.time ? `<span class="mono">${e.time}</span>` : ''}${isTodo && showDate && !e.date ? '<span>언젠가</span>' : ''}</div>
      <div class="title" style="font-weight:500">${linkify(esc(e.text)) || (e.imgs && e.imgs.length ? '' : '<span class="hint">(내용 없음)</span>')}</div>
      ${e.imgs && e.imgs.length ? `<div class="thumbs">${thumbsHtml(e.imgs)}</div>` : ''}
    </div>
    <div class="acts">${e.date && !(isTodo && e.done) ? calBtn('j:' + e.id) : ''}<button type="button" class="btn small" data-act="entry-edit" data-id="${e.id}">고치기</button></div></div>`;
}
function myTodos(){
  const my = S.profile.myClass;
  const out = [];
  if (S.tdSrc !== 'grade') S.journal.filter(e => e.cat === '할일' && !e.done && !e.hold).forEach(e => out.push({src:'me', id:e.id, title:e.text, due:e.date || null, prio:e.prio || '보통', time:e.time, tag:e.area || '나', area:e.area || '', every:e.every}));
  if (S.tdSrc !== 'me') S.tasks.filter(t => !t.done && !t.hold && (t.who === '전체' || !t.who || (my && t.who === my))).forEach(t => out.push({src:'grade', id:t.id, title:t.title, due:t.due || null, prio:t.prio || '보통', tag:'학년 · ' + (t.who || '전체'), every:t.every}));
  return out;
}
function renderToday(){
  const k = ymd(today());
  const evs = S.events.filter(e => e.date === k).sort(byTime);
  const sf = subjFor(k), sev = schoolEvents(k);
  $('#s-ev-n').textContent = evs.length + sev.length;
  const ttLine = sf.off ? `<li class="late"><span class="d">수업</span><span class="t">${esc(sf.off)}</span></li>`
    : (sf.s || []).some(Boolean) ? `<li><span class="d">시간표</span><span class="t mono">${esc((sf.s || []).filter(Boolean).join(' · '))}</span></li>` : '';
  const pls = planOn(k), gev = gEventsOn(k);
  $('#s-ev-n').textContent = evs.length + sev.length + pls.length + gev.length;
  const mls = S.profile.myClass ? lsOn(k, clsCanon(S.profile.myClass)) : [];
  $('#s-ev').innerHTML = ttLine + mls.map(l => `<li><span class="d">${lsPerLabel(l.pers)}</span><span class="t">${esc(l.prog)}${l.place ? ' · ' + esc(l.place) : ''}</span></li>`).join('') + '<li class="meal-today gas-only" hidden></li>' + pls.map(it => `<li><span class="d">평가</span><span class="t">${esc(it.name)}</span></li>`).join('') + gev.map(g => `<li><span class="d">${g.time || '구글'}</span><span class="t">${esc(g.title)} <span class="chip">구글</span></span></li>`).join('') + sev.map(t => `<li><span class="d">학교</span><span class="t">${esc(t)}</span></li>`).join('') +
    (evs.length ? evs.map(e => `<li><span class="d">${e.time || '종일'}</span><span class="t">${esc(e.title)}</span></li>`).join('') : (ttLine || sev.length ? '' : '<li class="hint">오늘은 일정이 없어요.</li>'));
  const src = S.tdSrc; S.tdSrc = 'all';
  const todo = myTodos().filter(t => t.src === 'me' && t.due && t.due <= ymd(addDays(today(), 2))).sort((a, b) => a.due < b.due ? -1 : a.due > b.due ? 1 : (a.prio === '높음' ? -1 : 1));
  const total = myTodos().filter(t => t.src === 'me').length; S.tdSrc = src;
  $('#s-tk-n').textContent = total;
  $('#s-tk').innerHTML = todo.length ? todo.slice(0, 5).map(t => {
    const n = dayDiff(t.due);
    return `<li class="${n < 0 ? 'late' : ''}"><span class="d">${n < 0 ? `${-n}일 지남` : n === 0 ? '오늘' : 'D-' + n}</span><span class="t">${t.prio === '높음' ? '★ ' : ''}${esc(t.title)}</span><span class="d">${t.src === 'me' ? '나' : '학년'}</span></li>`;
  }).join('') + (todo.length > 5 ? `<li class="hint">외 ${todo.length - 5}개</li>` : '') : `<li class="hint">${total ? '모레까지 마감인 일은 없어요. 전체 ' + total + '개는 "할 일 모아 보기"에서.' : '남은 할 일이 없어요.'}</li>`;
  const lateN = S.journal.filter(e => e.cat === '할일' && !e.done && e.date && e.date < k).length;
  if (lateN) $('#s-tk').insertAdjacentHTML('beforeend', `<li class="late"><span class="t">밀린 내 할 일 ${lateN}개</span><button type="button" class="btn small" data-act="late-today">모두 오늘로</button></li>`);
  renderMeal(); renderRoutine(); renderMeGrade();
  const js = S.journal.filter(e => covers(e, k) && e.cat !== '할일').sort(byTime);
  $('#s-j-n').textContent = js.length;
  const att = js.filter(e => e.att);
  $('#s-j').innerHTML = js.length ? (att.length ? att.map(e => `<li><span class="d">${attLabel(e.att)}</span><span class="t">${esc((e.students || []).map(stuName).join(', ') || e.text)}</span></li>`).join('') : '') +
    `<li class="hint">${att.length ? '그 밖의 기록 ' + (js.length - att.length) + '개' : '출결 특이사항 없음 · 기록 ' + js.length + '개'}</li>` : '<li class="hint">아직 오늘 기록이 없어요.</li>';
}
function renderNotes(force){
  if (!force && document.activeElement && document.activeElement.closest('#notes')) return;
  if (force) $$('#notes textarea[data-note]').forEach(t => { const n = (S.notes.items || []).find(x => x.id === t.dataset.note); if (n && n.text !== t.value){ n.text = t.value; saveNotes(); } });
  const items = S.notes.items || [];
  $('#notes').innerHTML = items.length ? items.map(n => `<div class="note-card" style="--nc:var(--n${(n.color || 0) % 4})">
    <textarea id="nt-${esc(n.id)}" data-note="${esc(n.id)}" rows="4" aria-label="메모 내용" placeholder="여기에 적어요 (사진은 Ctrl+V)">${esc(n.text)}</textarea>
    ${(u => u.length ? `<div class="nlinks">${u.map(x => `<a class="autolink" href="${esc(/^www\./i.test(x) ? 'https://' + x : x)}" target="_blank" rel="noopener noreferrer">${esc(x.replace(/^https?:\/\//, '').slice(0, 40))}${x.replace(/^https?:\/\//, '').length > 40 ? '…' : ''}</a>`).join('')}</div>` : '')((String(n.text || '').match(/(?:https?:\/\/|www\.)[^\s<]+[^\s<.,;:!?)\]'"]/gi) || []).slice(0, 5))}
    <div class="thumbs">${thumbsHtml(n.imgs, 'note|' + n.id)}</div>
    <div class="acts"><span class="mono">${n.createdAt ? fmtMD(ymd(new Date(n.createdAt))) : ''}</span><span><button type="button" data-pick="note:${esc(n.id)}">사진</button> <button type="button" data-act="note-del" data-id="${esc(n.id)}">다 했어요</button></span></div></div>`).join('')
    : '<p class="empty" style="grid-column:1/-1">"김선생님께 과학실 열쇠 돌려드리기"처럼 잠깐 붙여 둘 메모를 남겨 보세요.</p>';
  renderNotesDone();
}
function renderNotesDone(){
  const done = S.notes.done || [], btn = $('#note-done-btn'), box = $('#notes-done');
  if (!done.length) S.notesDoneOpen = false;
  btn.hidden = !done.length; btn.textContent = `해결한 메모 ${done.length}`;
  const open = !!S.notesDoneOpen && done.length > 0;
  btn.setAttribute('aria-expanded', open); box.hidden = !open;
  if (!open) return;
  box.innerHTML = `<h3>해결한 메모 <span class="hint">"다 했어요"를 누른 메모가 여기 모여요</span></h3>` + done.map(n => {
    const armed = S.armed === 'notedone:' + n.id;
    return `<div class="li nd"><div class="main"><div class="body">${esc(n.text || '(사진 메모)')}</div>${n.imgs && n.imgs.length ? `<div class="thumbs">${thumbsHtml(n.imgs)}</div>` : ''}
      <div class="meta mono">${n.createdAt ? fmtMD(ymd(new Date(n.createdAt))) + ' 적음' : ''}${n.doneAt ? ' · ' + fmtMD(ymd(new Date(n.doneAt))) + ' 해결' : ''}</div></div>
      <div class="acts"><button type="button" class="btn small" data-act="note-back" data-id="${esc(n.id)}">다시 붙이기</button><button type="button" class="btn small ${armed ? 'armed' : 'danger'}" data-act="note-purge" data-id="${esc(n.id)}">${armed ? '정말 지우기' : '지우기'}</button></div></div>`;
  }).join('');
}
function renderCats(){
  $('#j-cats').innerHTML = CATS.map(c => `<button type="button" data-cat="${c}" ${catStyle(c)} aria-pressed="${S.jForced === c}">${c}</button>`).join('') +
    `<span class="hint" style="align-self:center">분류를 고르지 않으면 내용을 보고 정해요. 중요한 일은 !높음</span>`;
}
function renderJPreview(){
  const v = $('#j-input').value.trim();
  if (!v){ $('#j-preview').innerHTML = ''; return; }
  const p = parseLine(v, {students:true});
  const cat = inferCat(p.text, p.tags, S.jForced, p.students.length > 0);
  const att = cat === '출결' ? inferAtt(p.text, p.students.length > 0) : null;
  const chips = [`<span class="chip">날짜 <b>${p.date ? fmtMD(p.date) : cat === '할일' ? '언젠가' : fmtMD(S.jDate)}</b></span>`];
  if (p.time) chips.push(`<span class="chip">시각 <b>${p.time}</b></span>`);
  chips.push(`<span class="pill" ${catStyle(cat)}>${cat}</span>`);
  if (p.prio) chips.push(`<span class="chip ${p.prio === '높음' ? 'red' : ''}">중요도 <b>${p.prio}</b></span>`);
  if (att) chips.push(`<span class="pill" ${catStyle('출결')}>${attLabel(att)}</span>`);
  if (p.students.length) chips.push(`<span class="chip">학생 <b>${esc(p.students.map(stuName).join(', '))}</b></span>`);
  chips.push(`<span class="chip">내용 <b>${esc(p.text || '—')}</b></span>`);
  $('#j-preview').innerHTML = chips.join('');
}
const DAYPATH = k => `data/users/${S.uid}/d-${k}`;
function renderDayBoard(){
  const k = S.jDate, d = S.day || {};
  $('#j-date-label').textContent = fmtLong(k);
  $('#j-date').value = k;
  const sf = subjFor(k);
  const tt = sf.s || [];
  $('#plan-off').hidden = !sf.off; $('#plan-off').textContent = sf.off ? `${sf.off} · 수업이 없는 날이에요` : '';
  $('#plan-src').textContent = sf.src === 'file' ? `${sf.week && sf.week.no ? sf.week.no + '주 ' : ''}시간표 파일에서 가져온 과목이에요. 이 날만 바꿔도 돼요.` : sf.src === 'basic' ? '기본 시간표에서 가져온 과목이에요.' : '시간표 탭에서 시간표 파일을 올리면 과목이 채워져요.';
  const sev = schoolEvents(k);
  $('#school-ev').innerHTML = sev.map(t => `<span class="chip school">학교 행사 · ${esc(t)}</span>`).join('') + planOn(k).map(it => `<span class="chip">평가 · ${esc(it.name)}</span>`).join('') + gEventsOn(k).map(g => `<span class="chip">구글 · ${g.time ? g.time + ' ' : ''}${esc(g.title)}</span>`).join('');
  if (WK.mode === 'week') renderWeek();
  const act = document.activeElement;
  if (!(act && act.closest('#plan'))){
    const plan = d.plan || [];
    let h = '<thead><tr><th>교시</th><th>과목</th><th>주제</th><th>준비물 · 메모</th></tr></thead><tbody>';
    for (let i = 0; i < 6; i++){
      const p = plan[i] || {};
      const subj = p.s !== undefined && p.s !== null ? p.s : expand(tt[i]);
      if (i === lunchAt()) h += '<tr class="lunch"><td colspan="4">점심</td></tr>';
      h += `<tr><td>${i + 1}</td><td><input id="pl-s-${i}" data-pl="s" data-i="${i}" value="${esc(subj)}" placeholder="${esc(expand(tt[i]) || '과목')}" aria-label="${i + 1}교시 과목"></td><td><input id="pl-t-${i}" data-pl="t" data-i="${i}" value="${esc(p.t || '')}" aria-label="${i + 1}교시 주제"></td><td><input id="pl-p-${i}" data-pl="p" data-i="${i}" value="${esc(p.p || '')}" aria-label="${i + 1}교시 준비물"></td></tr>`;
    }
    $('#plan').innerHTML = h + '</tbody>';
  }
  if (act !== $('#day-memo')) $('#day-memo').value = d.memo || '';
  if (act !== $('#chk-name')) $('#chk-name').value = d.checkName || '';
  const list = S.journal.filter(e => covers(e, k) && !(e.cat === '할일' && e.date !== k)).sort((a, b) => (a.cat === '할일') - (b.cat === '할일') || byTime(a, b));
  const att = list.filter(e => e.att);
  $('#j-att').innerHTML = att.length ? att.map(e => `<span class="chip red">${esc((e.students || []).map(stuName).join(', ') || '학생')} · ${attLabel(e.att)}</span>`).join('') : '';
  $('#j-list').innerHTML = list.length ? list.map(e => entryRow(e, false)).join('') :
    `<p class="empty">${k === ymd(today()) ? '오늘 기록이 아직 없어요. 위 칸에 "3번 지각 병원 다녀옴"처럼 한 줄로 적어 보세요.' : '이 날 기록이 없어요.'}</p>`;
  const roster = S.profile.roster || [];
  if (!roster.length){ $('#stu-table').innerHTML = '<p class="empty">"명부" 탭에서 명단을 넣으면 학생 표가 생겨요.</p>'; return; }
  const attBy = {};
  att.forEach(e => (e.students || []).forEach(n => { attBy[n] = (attBy[n] ? attBy[n] + ', ' : '') + attLabel(e.att); }));
  const checks = d.checks || {};
  const attIx = attIndex();
  const cn = d.checkName || '과제';
  const done = roster.filter(r => checks[r.no]).length;
  $('#stu-table').innerHTML = `<div class="tablewrap"><table class="sheet"><thead><tr><th>번호</th><th>이름</th><th>출결</th><th>${esc(cn)}<span class="stat">${done}/${roster.length}</span></th></tr></thead><tbody>${roster.map(r => `<tr>
    <td class="mono">${r.no}</td><td class="name">${esc(r.name || '')}</td>
    <td>${attSelHtml(r.no, k, attIx)}</td>
    <td><button type="button" class="tick" data-act="day-check" data-no="${r.no}" aria-label="${r.no}번 ${esc(cn)}">${checks[r.no] ? '✓' : ''}</button></td></tr>`).join('')}</tbody></table></div>`;
}
function saveDay(){ const k = S.jDate; const data = Object.assign({}, S.day, {date:k}); queueSet(DAYPATH(k), () => data, false); }
function renderTodo(){
  const k = ymd(today()), wk = ymd(addDays(today(), 7));
  $$('#td-src button').forEach(b => b.setAttribute('aria-pressed', b.dataset.src === S.tdSrc));
  $('#td-high').checked = S.tdHigh;
  let items = myTodos();
  const areasUsed = TD_AREAS.filter(a => S.journal.some(e => e.cat === '할일' && !e.done && e.area === a));
  $('#td-area').hidden = !areasUsed.length;
  $('#td-area').innerHTML = [['all', '모든 분류']].concat(areasUsed.map(a => [a, a])).map(([k, n]) => `<button type="button" data-area="${k}" aria-pressed="${(S.tdArea || 'all') === k}">${n}</button>`).join('');
  if (S.tdArea && S.tdArea !== 'all') items = items.filter(i => i.src === 'me' && i.area === S.tdArea);
  if (S.tdHigh) items = items.filter(i => i.prio === '높음');
  const pr = p => p === '높음' ? 0 : p === '낮음' ? 2 : 1;
  items.sort((a, b) => (a.due || '9999') < (b.due || '9999') ? -1 : (a.due || '9999') > (b.due || '9999') ? 1 : pr(a.prio) - pr(b.prio));
  const groups = [
    ['late', '지났어요', items.filter(i => i.due && i.due < k)],
    ['today', '오늘', items.filter(i => i.due === k)],
    ['week', '7일 안에', items.filter(i => i.due && i.due > k && i.due <= wk)],
    ['later', '그 뒤', items.filter(i => i.due && i.due > wk)],
    ['none', '언젠가 (날짜 없음)', items.filter(i => !i.due)],
    ['hold', '보류', S.tdSrc === 'grade' ? [] : S.journal.filter(e => e.cat === '할일' && !e.done && e.hold && (!S.tdArea || S.tdArea === 'all' || e.area === S.tdArea)).map(e => ({src:'me', id:e.id, title:e.text, due:e.date || null, prio:e.prio || '보통', tag:e.area || '나', hold:true}))]
  ];
  const doneN = S.journal.filter(e => e.cat === '할일' && e.done).length;
  $('#td-donecount').textContent = doneN ? `끝낸 내 할 일 ${doneN}개` : '';
  const row = i => `<div class="li"><button type="button" class="chk" data-act="todo-toggle" data-src="${i.src}" data-id="${i.id}" aria-label="끝냄" ${i.src === 'grade' && !S.canWrite ? 'disabled' : ''}></button>
    <div class="main"><div class="title">${esc(i.title) || '<span class="hint">(내용 없음)</span>'}</div>
    <div class="meta">${prioTag(i.prio)}${i.due ? `<span class="mono">${fmtMD(i.due)}</span>` : ''}${i.time ? `<span class="mono">${i.time}</span>` : ''}<span class="chip ${i.src === 'grade' ? 'acc' : ''}">${esc(i.tag)}</span>${i.every ? `<span class="chip">↻ ${EVERY_NAME[i.every]}</span>` : ''}</div></div>
    <div class="acts">${i.src === 'me' && i.due && i.due < k ? `<button type="button" class="btn small" data-act="todo-today" data-id="${i.id}">오늘로</button>` : ''}${i.due ? calBtn((i.src === 'me' ? 'j:' : 'tk:') + i.id) : ''}
    ${i.src === 'me' ? `<button type="button" class="btn small" data-act="me-hold" data-id="${i.id}">${i.hold ? '다시 하기' : '보류'}</button>` : `<button type="button" class="btn small" data-act="task-hold" data-id="${i.id}" ${S.canWrite ? '' : 'disabled'}>보류</button>`}
    <button type="button" class="btn small" data-act="${i.src === 'me' ? 'entry-edit' : 'task-edit'}" data-id="${i.id}">고치기</button></div></div>`;
  const lateMine = items.filter(i => i.src === 'me' && i.due && i.due < k).length;
  const html = groups.filter(g => g[2].length).map(([key, name, list]) => `<div class="tdg ${key}"><h4>${name} <span class="n">${list.length}</span>${key === 'late' && lateMine ? `<span class="grow"></span><button type="button" class="btn small" data-act="late-today">내 것 모두 오늘로 (${lateMine})</button><button type="button" class="btn small" data-act="late-done">모두 끝냄</button>` : ''}</h4><div class="list">${list.map(row).join('')}</div></div>`).join('');
  $('#td-groups').innerHTML = html || '<p class="empty" style="margin-top:12px">남은 할 일이 없어요. 위 칸에 "금요일까지 계획서 올리기 !높음"처럼 적어 보세요.</p>';
}
function renderCns(){
  $$('#cns-filter button').forEach(b => b.setAttribute('aria-pressed', b.dataset.c === S.cnsF));
  $$('#cns-way button').forEach(b => b.setAttribute('aria-pressed', b.dataset.w === (S.cnsW || 'all')));
  const list = S.journal.filter(e => (S.cnsF === 'all' ? (e.cat === '상담' || e.cat === '학부모') : e.cat === S.cnsF) && (!S.cnsW || S.cnsW === 'all' || cnsWay(e.text) === S.cnsW))
    .sort((a, b) => (a.date || '') < (b.date || '') ? 1 : (a.date || '') > (b.date || '') ? -1 : -byTime(a, b));
  $('#cns-list').innerHTML = list.length ? list.map(e => entryRow(e, true)).join('') : '<p class="empty">아직 상담 기록이 없어요. "내일 15시 5번 학부모 상담 #상담"처럼 적으면 날짜까지 함께 남아요.</p>';
}
function renderTTWeek(){
  if (!S.ttMon) S.ttMon = mondayOf(ymd(today()));
  const mon = S.ttMon, w = weekAt(mon), tk = ymd(today());
  const x = S.ttIdx[mon], term = x ? S.ttplan.terms[x.ti] : null;
  const e = addDays(fromYmd(mon), 4);
  $('#tt-week-label').textContent = `${term && term.key !== 'manual' ? term.label.replace(/^\d{4}학년도 /, '') + ' ' : ''}${w && w.no ? w.no + '주 · ' : ''}${fromYmd(mon).getMonth()+1}.${fromYmd(mon).getDate()} ~ ${e.getMonth()+1}.${e.getDate()}`;
  renderTTNav();
  const ts = S.ttplan;
  $('#tt-source').textContent = ts.file ? `반영된 파일: ${ts.file}${ts.title ? ' · ' + ts.title : ''} · ${(ts.terms || []).filter(t => t.key !== 'manual').map(t => `${t.label} ${t.weeks.length}주`).join(', ')}` : '아직 올린 시간표 파일이 없어요.';
  if (document.activeElement && document.activeElement.closest('#tt-week')) return;
  if (document.activeElement !== $('#tt-note')) $('#tt-note').value = w ? (w.note || '') : '';
  $('#tt-note').disabled = !w;
  if (!w){
    $('#tt-week').innerHTML = `<p class="empty">이 주는 시간표 파일에 없어서 기본 시간표를 써요. <button type="button" class="btn small" data-act="tt-make">이 주 시간표 따로 만들기</button></p>`;
    return;
  }
  const days = [0, 1, 2, 3, 4].map(i => ({i, k:ymd(addDays(fromYmd(mon), i)), d:w.days[i] || {s:[]}}));
  let h = `<div class="tablewrap"><table class="ttw"><thead><tr><th>교시</th>${days.map(({i, k, d}) => `<th class="${k === tk ? 'today' : ''}">${WD[i + 1]}<small>${fromYmd(k).getMonth()+1}.${fromYmd(k).getDate()}</small><button type="button" class="dayact" data-act="tt-off" data-i="${i}">${d.off ? '수업일로' : '휴일로'}</button></th>`).join('')}</tr></thead><tbody>`;
  for (let p = 0; p < 6; p++){
    if (p === lunchAt()){ const on = days.filter(x => !x.d.off).length; h += `<tr class="lunch"><td class="p">점심</td>${on ? `<td colspan="${on}" style="background:var(--surface-2)"></td>` : ''}</tr>`; }
    h += `<tr><td class="p">${p + 1}</td>`;
    days.forEach(({i, d}) => {
      if (d.off){ if (p === 0) h += `<td class="off" rowspan="7"><input type="text" id="ttw-off-${i}" data-ttoff="${i}" value="${esc(d.off)}" aria-label="${WD[i + 1]}요일 휴일 이름"></td>`; return; }
      const v = (d.s || [])[p] || '';
      h += `<td><input type="text" id="ttw-${i}-${p}" data-tti="${i}" data-ttp="${p}" value="${esc(v)}" title="${esc(expand(v))}" aria-label="${WD[i + 1]}요일 ${p + 1}교시"></td>`;
    });
    h += '</tr>';
  }
  $('#tt-week').innerHTML = h + '</tbody></table></div>';
}
function weekLabel(mon){
  const x = S.ttIdx[mon]; if (!x) return '';
  const t = S.ttplan.terms[x.ti], w = t.weeks[x.wi];
  return `${t.key === 'manual' ? '직접' : t.label.replace(/^\d{4}학년도 /, '')} ${w.no ? w.no + '주' : ''}`.trim();
}
function renderTTNav(){
  const mon = S.ttMon;
  const opts = [];
  (S.ttplan.terms || []).forEach(t => {
    const ws = (t.weeks || []).slice().sort((a, b) => a.mon < b.mon ? -1 : 1);
    if (!ws.length) return;
    opts.push(`<optgroup label="${esc(t.key === 'manual' ? '직접 만든 주' : t.label)}">` + ws.map(w => {
      const e = addDays(fromYmd(w.mon), 4);
      return `<option value="${w.mon}" ${w.mon === mon ? 'selected' : ''}>${w.no ? w.no + '주 · ' : ''}${fromYmd(w.mon).getMonth()+1}.${fromYmd(w.mon).getDate()}~${e.getMonth()+1}.${e.getDate()}</option>`;
    }).join('') + '</optgroup>');
  });
  $('#ttw-pick').innerHTML = (S.ttIdx[mon] ? '' : '<option value="" selected>파일에 없는 주</option>') + opts.join('');
  $('#ttw-pick').hidden = !opts.length;
  if (document.activeElement !== $('#ttw-date')) $('#ttw-date').value = mon;
  $('#ttw-caltoggle').setAttribute('aria-expanded', S.ttCalOpen);
  $('#ttw-cal').hidden = !S.ttCalOpen;
  if (!S.ttCalOpen) return;
  if (!S.ttCal){ const d = fromYmd(mon); S.ttCal = new Date(d.getFullYear(), d.getMonth(), 1); }
  const m = S.ttCal, start = addDays(m, -m.getDay()), tk = ymd(today());
  const weeks = addDays(start, 35).getMonth() === m.getMonth() ? 6 : 5;
  let h = `<div class="head"><button type="button" class="btn small" data-act="mcal-prev" aria-label="지난달">‹</button><strong>${m.getFullYear()}. ${pad(m.getMonth()+1)}</strong><button type="button" class="btn small" data-act="mcal-next" aria-label="다음 달">›</button><span class="hint">날짜를 누르면 그 주로 가요</span></div>`;
  h += '<table class="mcal"><thead><tr><th></th>' + [...WD].map((w, i) => `<th class="${i === 0 ? 'sun' : i === 6 ? 'sat' : ''}">${w}</th>`).join('') + '</tr></thead><tbody>';
  for (let r = 0; r < weeks; r++){
    const rowMon = ymd(addDays(start, r * 7 + 1));
    h += `<tr class="${rowMon === mon ? 'sel' : ''}"><td class="wk">${esc(weekLabel(rowMon).replace(/^\S+ /, '')) || ''}</td>`;
    for (let c = 0; c < 7; c++){
      const d = addDays(start, r * 7 + c), k = ymd(d), sf = (c > 0 && c < 6) ? subjFor(k) : {};
      const cls = [d.getMonth() !== m.getMonth() ? 'out' : '', (c === 0 || HOLIDAYS[k] || sf.off) ? 'red' : c === 6 ? 'blue' : '', k === tk ? 'tdy' : '', schoolEvents(k).length ? 'ev' : ''].join(' ');
      const tip = [HOLIDAYS[k] || sf.off, ...schoolEvents(k)].filter(Boolean).join(', ');
      h += `<td class="${cls}"><button type="button" data-act="mcal-day" data-date="${k}" title="${esc(tip)}" aria-label="${d.getMonth()+1}월 ${d.getDate()}일${tip ? ', ' + esc(tip) : ''}">${d.getDate()}</button></td>`;
    }
    h += '</tr>';
  }
  $('#ttw-cal').innerHTML = h + '</tbody></table>';
}
function goTTWeek(mon){
  S.ttMon = mon;
  const d = fromYmd(mon); S.ttCal = new Date(d.getFullYear(), d.getMonth(), 1);
  const x = S.ttIdx[mon]; if (x) S.ttTerm = S.ttplan.terms[x.ti].key;
  renderTTWeek(); renderTTOverview();
}
function renderTTOverview(){
  const terms = (S.ttplan.terms || []).filter(t => (t.weeks || []).length);
  if (!terms.length){ $('#tt-terms').innerHTML = ''; $('#tt-overview').innerHTML = '<p class="empty">시간표 파일을 올리면 학기 전체 시간표가 여기에 한눈에 보여요.</p>'; $('#tt-counts').innerHTML = ''; return; }
  const tk = ymd(today()), curMon = mondayOf(tk);
  if (!S.ttTerm || !terms.some(t => t.key === S.ttTerm)){
    const hit = terms.find(t => t.weeks.some(w => w.mon === curMon)) || terms.find(t => t.weeks.some(w => w.mon > curMon)) || terms[terms.length - 1];
    S.ttTerm = hit.key;
  }
  $('#tt-terms').innerHTML = terms.map(t => `<button type="button" data-ttterm="${esc(t.key)}" aria-pressed="${t.key === S.ttTerm}">${esc(t.key === 'manual' ? '직접 만든 주' : t.label.replace(/^\d{4}학년도 /, ''))}</button>`).join('');
  const term = terms.find(t => t.key === S.ttTerm);
  const weeks = term.weeks.slice().sort((a, b) => a.mon < b.mon ? -1 : 1);
  let h = '<div class="tablewrap"><table class="tto"><thead><tr><th rowspan="2">주</th><th rowspan="2">기간</th>' +
    [1, 2, 3, 4, 5].map(i => `<th colspan="6" class="dg">${WD[i]}</th>`).join('') + '<th rowspan="2">학교 행사</th></tr><tr class="per">' +
    [1, 2, 3, 4, 5].map(() => [1, 2, 3, 4, 5, 6].map(p => `<th class="${p === 1 ? 'dg' : ''}">${p}</th>`).join('')).join('') + '</tr></thead><tbody>';
  const counts = {};
  weeks.forEach(w => {
    h += `<tr class="${w.mon === curMon ? 'cur' : ''} ${w.mon === S.ttMon ? 'sel' : ''}" data-act="tt-goweek" data-mon="${w.mon}"><td class="wk">${w.no || ''}</td><td class="rg">${esc(w.range || '')}</td>`;
    [0, 1, 2, 3, 4].forEach(i => {
      const d = w.days[i] || {s:[]}, k = ymd(addDays(fromYmd(w.mon), i));
      if (d.off){ h += `<td class="off dg" colspan="6">${esc(d.off)}</td>`; return; }
      const sub = d.s || [];
      for (let p = 0; p < 6; p++){
        const v = sub[p] || '';
        if (v) counts[expand(v)] = (counts[expand(v)] || 0) + 1;
        h += `<td class="s ${p === 0 ? 'dg' : ''} ${k === tk && v ? 'today' : ''}" title="${esc(expand(v))}">${esc(v)}</td>`;
      }
    });
    h += `<td class="nt">${esc((w.events || []).map(e => `${fromYmd(e.date).getMonth()+1}.${fromYmd(e.date).getDate()} ${e.text}`).join(' · '))}</td></tr>`;
  });
  $('#tt-overview').innerHTML = h + '</tbody></table></div>';
  const total = Object.values(counts).reduce((a, b) => a + b, 0);
  $('#tt-counts').innerHTML = `<span class="chip acc">${esc(term.key === 'manual' ? '직접 만든 주' : term.label.replace(/^\d{4}학년도 /, ''))} 과목별 시간 · 모두 <b>${total}</b></span>` +
    Object.entries(counts).sort((a, b) => b[1] - a[1]).map(([n, c]) => `<span class="chip">${esc(n)} <b>${c}</b></span>`).join('');
}
function renderTT(){
  renderTTWeek(); renderTTOverview();
  if (document.activeElement && document.activeElement.closest('#tt')) return;
  const tt = S.profile.timetable || {};
  let h = '<thead><tr><th>교시</th>' + [1, 2, 3, 4, 5].map(w => `<th>${WD[w]}</th>`).join('') + '</tr></thead><tbody>';
  for (let i = 0; i < 6; i++){
    h += `<tr><td class="mono">${i + 1}</td>` + [1, 2, 3, 4, 5].map(w => `<td><input type="text" id="tt-${w}-${i}" value="${esc((tt[w] || [])[i] || '')}" aria-label="${WD[w]}요일 ${i + 1}교시"></td>`).join('') + '</tr>';
  }
  $('#tt').innerHTML = h + '</tbody>';
}
function renderStu(){
  const roster = S.profile.roster || [];
  if (!roster.length){ $('#stu-form').hidden = true; $('#stu-grid').innerHTML = ''; $('#stu-detail').innerHTML = '<p class="empty">"명부" 탭에서 명단을 넣으면 학생마다 기록이 모여요.</p>'; return; }
  const counts = {};
  S.journal.forEach(e => (e.students || []).forEach(n => { counts[n] = (counts[n] || 0) + 1; }));
  const fix = relinkCandidates();
  $('#stu-relink').hidden = !fix.length;
  if (fix.length) $('#stu-relink').innerHTML = `<span>학생 이름으로 적었지만 학생 카드에 아직 이어지지 않은 기록이 ${fix.length}개 있어요.</span><button type="button" class="btn small primary" id="relink-go">학생 카드에 이어 붙이기</button>`;
  if ((S.selStu === null || !roster.some(r => r.no === S.selStu)) && roster.length) S.selStu = roster[0].no;
  $('#stu-grid').style.setProperty('--rows', Math.ceil(roster.length / 2));
  $('#stu-grid').innerHTML = roster.map(r => `<button type="button" data-stu="${r.no}" aria-pressed="${S.selStu === r.no}"><span>${esc(stuName(r.no))}</span><span class="n">${counts[r.no] || 0}</span></button>`).join('');
  $('#stu-form').hidden = S.selStu === null;
  if (S.selStu !== null) $('#stu-input').placeholder = `${stuName(S.selStu)} 기록 적기 (예: 쉬는 시간 다툼 후 화해함)`;
  if (S.selStu === null){ $('#stu-detail').innerHTML = '<p class="hint">학생을 누르면 그 학생의 기록이 날짜순으로 모이고, 바로 적을 수 있어요.</p>'; return; }
  const no = S.selStu, info = (S.profile.roster || []).find(r => r.no === no) || {};
  const all = S.journal.filter(e => (e.students || []).includes(no)).sort((a, b) => a.date < b.date ? 1 : a.date > b.date ? -1 : -byTime(a, b));
  const catT = {}; all.forEach(e => { catT[e.cat] = (catT[e.cat] || 0) + 1; });
  const cat = S.stuCat || 'all';
  const list = cat === 'all' ? all : all.filter(e => e.cat === cat);
  const ae = document.activeElement;
  const keepHb = ae && ae.id === 'stu-hb';
  const facts = [info.sex, info.birth && '생일 ' + info.birth, info.prev && '이전 ' + info.prev, info.guardian && '보호자 ' + info.guardian, info.phone].filter(Boolean);
  const card = studentSummary(no);
  const hb = ((S.stuNotes || {}).hb || {})[no] || '';
  const head = `<div class="stu-head"><div class="nm"><button type="button" class="btn small" data-stu-nav="-1" aria-label="이전 학생">‹</button><strong>${esc(stuName(no))}</strong><button type="button" class="btn small" data-stu-nav="1" aria-label="다음 학생">›</button></div>
    <span class="facts">${facts.map(esc).join(' · ') || '<span class="hint">명부에 생년월일·연락처를 넣으면 여기 보여요.</span>'}</span><span class="grow"></span><button type="button" class="btn small gas-only" id="stu-print">학생 카드 인쇄</button></div>
    <div class="stu-cards">
      <section class="sc"><h4>출결 <small>${card.sy}</small></h4>${card.attHtml}</section>
      <section class="sc"><h4>평가·제출 <small>명렬표</small></h4>${card.evalHtml}</section>
      <section class="sc"><h4>누가기록 <small>${all.length}건</small></h4><div class="tally">${CATS.filter(c => catT[c]).map(c => `<span class="pill" ${catStyle(c)}>${c} ${catT[c]}</span>`).join('') || '<span class="hint">아직 없어요.</span>'}</div>
        <p class="hint" style="margin:6px 0 0">학급일지에 "${esc(info.name || no + '번')} …"처럼 이름이나 번호를 넣어 적으면 자동으로 여기 모여요.</p></section>
    </div>
    ${(() => { const hbs = all.filter(e => e.cat === '행발').sort((a, b) => (a.date || '') < (b.date || '') ? -1 : 1); return `<section class="sc hblog"><h4>행발 누가기록 <small>${hbs.length}건 · 학급일지에 "행발 ${esc(info.name || no + '번')} …"처럼 적으면 모여요</small></h4>${hbs.length ? `<ul class="hbl">${hbs.map(e => `<li><span class="mono">${e.date ? mdShort(e.date) : ''}</span><span>${esc(e.text)}</span></li>`).join('')}</ul><button type="button" class="btn small" id="hb-draft">아래 종합의견 초안에 모두 붙이기</button>` : '<p class="hint" style="margin:0">아직 행발 기록이 없어요.</p>'}</section>`; })()}
    <section class="sc hbbox"><h4>행동특성 및 종합의견 <small id="stu-hb-n">${hb.length}자</small></h4>
      <textarea id="stu-hb" rows="4" placeholder="아래 누가기록을 보며 행발 초안을 적어 두세요. 나만 볼 수 있어요." aria-label="행동특성 및 종합의견">${esc(hb)}</textarea></section>`;
  if (keepHb){ /* 쓰는 중에는 위쪽을 다시 그리지 않아요 */ $('#stu-tl').innerHTML = tlHtml(); return; }
  function tlHtml(){ return `<div class="seg stu-cats" role="group" aria-label="분류">${[['all', `전체 ${all.length}`]].concat(CATS.filter(c => catT[c]).map(c => [c, `${c} ${catT[c]}`])).map(([v, n]) => `<button type="button" data-stu-cat="${v}" aria-pressed="${cat === v}">${n}</button>`).join('')}</div>
    <div class="list">${list.length ? list.map(e => entryRow(e, true)).join('') : '<p class="empty">아직 이 학생 기록이 없어요.</p>'}</div>`; }
  $('#stu-detail').innerHTML = head + `<h3 class="stu-sub">누가기록</h3><div id="stu-tl">${tlHtml()}</div>`;
}
function relinkCandidates(){
  return S.journal.map(e => {
    const found = namesIn(' ' + (e.text || '') + ' ').filter(n => !(e.students || []).includes(n));
    const lead = (e.text || '').match(/^(출결|상담|생활|행발|행동발달|학부모|수업|메모)\s*[:·]?\s+/);
    if (!found.length && !(lead && e.cat === '메모')) return null;
    if (!found.length && !(e.students || []).length) return null;
    return {e, found, lead};
  }).filter(Boolean);
}
async function relinkNames(){
  const list = relinkCandidates(); if (!list.length) return;
  const col = S.db.doc(PROFILE()).collection('journal'); let n = 0;
  for (const {e, found, lead} of list){
    const students = (e.students || []).concat(found);
    const upd = {students};
    if (lead && (e.cat === '메모' || !e.cat)){ upd.cat = lead[1] === '행동발달' ? '행발' : lead[1]; upd.text = e.text.slice(lead[0].length); }
    const cat = upd.cat || e.cat;
    if (cat === '출결' && !e.att){ upd.cat = '출결'; upd.att = inferAtt(upd.text || e.text, true); }
    try { await col.doc(e.id).update(upd); n++; } catch (er){ wErr(er, false); break; }
  }
  toast(`${n}개 기록을 학생 카드에 이어 붙였어요.`);
}
function studentSummary(no){
  const sy = schoolYearOf(today());
  const ix = attIndex(), tot = ATT_COLS.map(() => 0), days = [];
  Object.keys(ix).forEach(k => { const [n, d] = k.split('|'); if (+n !== no || d < sy.from || d > sy.to) return; const a = ix[k]; const ci = ATT_COLS.findIndex(c => c[0] === a.kind && (c[1] === null || c[1] === a.reason)); if (ci >= 0) tot[ci]++; days.push([d, a]); });
  days.sort((a, b) => a[0] < b[0] ? 1 : -1);
  const attHtml = `<div class="atot">${ATT_COLS.map((c, i) => `<span class="${tot[i] ? 'has' : ''}"><b>${tot[i]}</b>${c[2]}</span>`).join('')}</div>` +
    (days.length ? `<ul class="mini">${days.slice(0, 6).map(([d, a]) => `<li><span class="mono">${mdShort(d)}</span> ${esc(attLabel(a))}${a.e.text ? ' · ' + esc(a.e.text) : ''}</li>`).join('')}${days.length > 6 ? `<li class="hint">외 ${days.length - 6}일 (출결 탭에서 모두 보기)</li>` : ''}</ul>` : '<p class="hint" style="margin:4px 0 0">개근 중이에요.</p>');
  const items = (S.sheet && S.sheet.items) || [], vals = (S.sheet && S.sheet.values) || {};
  const rows = items.map(it => {
    const v = (vals[it.id] || {})[no];
    let out = '', cls = '';
    if (it.type === 'check'){ out = v === true ? '제출' : '미제출' + (typeof v === 'string' && v ? ` (${esc(v)})` : ''); cls = v === true ? '' : 'miss'; }
    else if (it.type === 'score'){ const ns = Object.values(vals[it.id] || {}).map(Number).filter(n => !isNaN(n)); const avg = ns.length ? Math.round(ns.reduce((a, b) => a + b, 0) / ns.length * 10) / 10 : null; out = v !== undefined && v !== '' ? `<b>${esc(v)}</b>${avg !== null ? ` <small>반 평균 ${avg}</small>` : ''}` : '—'; }
    else out = v ? `<b>${esc(v)}</b>` : '—';
    return `<li class="${cls}"><span>${esc(it.name)}</span><span>${out}</span></li>`;
  }).join('');
  const ga = groupAverages(no).filter(x => x.avg !== null);
  const groupsOrder = [...new Set(items.map(it => it.group || ''))];
  const rowsArr = items.map((it, i) => ({it, html:rows.split('</li>')[i] + '</li>'}));
  const grouped = groupsOrder.map(g => { const rs = rowsArr.filter(x => (x.it.group || '') === g).map(x => x.html).join(''); const av = ga.find(x => x.g === g); return (g ? `<li class="gh"><span>${esc(g)}</span>${av ? `<span>평균 <b>${av.avg}</b></span>` : '<span></span>'}</li>` : '') + rs; }).join('');
  const evalHtml = items.length ? `<ul class="evl">${grouped}</ul>` : '<p class="hint">명렬표에 평가·수합 항목을 만들면 이 학생 결과가 여기 모여요.</p>';
  return {sy:sy.label, attHtml, evalHtml, tot};
}
const STUNOTES = () => `data/users/${S.uid}/stunotes`;
let hbTimer;
document.addEventListener('input', e => {
  if (e.target.id !== 'stu-hb' || !S.uid || S.selStu === null) return;
  const no = S.selStu, v = e.target.value;
  $('#stu-hb-n').textContent = v.length + '자';
  S.stuNotes = S.stuNotes || {hb:{}}; S.stuNotes.hb = Object.assign({}, S.stuNotes.hb, {[no]:v});
  clearTimeout(hbTimer); hbTimer = setTimeout(() => queueSet(STUNOTES(), () => ({hb:S.stuNotes.hb, updatedAt:Date.now()}), false), 700);
});
async function printStudent(no){
  if (no === null) return;
  const info = (S.profile.roster || []).find(r => r.no === no) || {}, c = studentSummary(no);
  const all = S.journal.filter(e => (e.students || []).includes(no)).sort((a, b) => a.date < b.date ? -1 : 1);
  const hb = ((S.stuNotes || {}).hb || {})[no] || '';
  printDoc(`<div class="pdoc"><h1 style="font-size:18pt;letter-spacing:.1em">학생 기록 카드</h1>
    <div class="meta"><span>${esc(classLabel())} ${esc(stuName(no))}</span><span>${esc([info.sex, info.birth].filter(Boolean).join(' · '))}</span><span>${c.sy}</span></div>
    <table><tr>${ATT_COLS.map(x => `<th>${x[2]}</th>`).join('')}</tr><tr>${c.tot.map(n => `<td>${n}</td>`).join('')}</tr></table>
    <h3 style="font-size:12pt;margin:6mm 0 2mm">평가·제출</h3><div style="font-size:10pt">${c.evalHtml}</div>
    <h3 style="font-size:12pt;margin:6mm 0 2mm">행동특성 및 종합의견</h3><div class="box">${esc(hb).replace(/\n/g, '<br>')}</div>
    <h3 style="font-size:12pt;margin:6mm 0 2mm">누가기록 (${all.length}건)</h3>
    <table><thead><tr><th style="width:16%">날짜</th><th style="width:10%">분류</th><th>내용</th></tr></thead><tbody>${all.map(e => `<tr><td>${e.date ? mdShort(e.date) : ''}${e.end ? '~' + mdShort(e.end) : ''}</td><td>${e.cat}</td><td style="text-align:left">${esc(e.text || '')}</td></tr>`).join('') || '<tr><td colspan="3">기록 없음</td></tr>'}</tbody></table></div>`);
}
function renderSheet(){
  renderPlanBox();
  $('#sh-groups').innerHTML = [...new Set((S.sheet.items || []).map(it => it.group).filter(Boolean))].map(g => `<option value="${esc(g)}">`).join('');
  const roster = S.profile.roster || [], items = S.sheet.items || [], vals = S.sheet.values || {};
  $('#sh-missing').checked = S.onlyMissing;
  if (!roster.length){ $('#sheet').innerHTML = '<p class="empty">명렬표를 쓰려면 먼저 "명부"를 넣어 주세요.</p>'; return; }
  if (!items.length){ $('#sheet').innerHTML = '<p class="empty">위에서 항목을 추가하면 우리 반 명단으로 표가 만들어져요.</p>'; return; }
  const has = (it, no) => { const v = (vals[it.id] || {})[no]; return it.type === 'check' ? v === true : (v !== undefined && v !== null && v !== '' && v !== false); };
  let rows = roster;
  if (S.onlyMissing) rows = roster.filter(r => items.some(it => !has(it, r.no)));
  const head = items.map(it => {
    const got = roster.filter(r => has(it, r.no));
    let stat = `${roster.length - got.length}명 남음`;
    if (it.type === 'check') stat = `제출 ${got.length} · 미제출 ${roster.length - got.length}`;
    if (it.type === 'level'){ const c = {}; got.forEach(r => { const v = vals[it.id][r.no]; c[v] = (c[v] || 0) + 1; }); stat = (it.levels || []).map(l => `${l} ${c[l] || 0}`).join(' · ') + (got.length < roster.length ? ` · 남음 ${roster.length - got.length}` : ''); }
    if (it.type === 'score' && got.length){
      const nums = got.map(r => Number(vals[it.id][r.no])).filter(n => !isNaN(n));
      if (nums.length) stat = `평균 ${Math.round(nums.reduce((a, b) => a + b, 0) / nums.length * 10) / 10} · 최고 ${Math.max(...nums)} · 최저 ${Math.min(...nums)}`;
    }
    const armed = S.armed === 'item:' + it.id;
    return `<th>${esc(it.name)}<button type="button" class="xbtn" data-act="item-del" data-id="${it.id}" aria-label="${esc(it.name)} 항목 지우기" style="${armed ? 'color:var(--danger);font-weight:700' : ''}">${armed ? '지우기?' : '×'}</button>
      <span class="stat">${{check:'제출', score:'점수', level:'단계', text:'글'}[it.type] || ''} · ${stat}</span></th>`;
  }).join('');
  const body = rows.map(r => `<tr><td class="mono">${r.no}</td><td class="name">${esc(r.name || '')}</td>${items.map(it => {
    const v = (vals[it.id] || {})[r.no];
    if (it.type === 'check') return `<td class="subm"><div class="row"><button type="button" class="tick" data-act="tick" data-item="${it.id}" data-no="${r.no}" aria-label="${r.no}번 ${esc(it.name)} 제출">${v === true ? '✓' : ''}</button>${v === true ? '' : `<input type="text" class="why" id="why-${it.id}-${r.no}" data-item="${it.id}" data-no="${r.no}" data-why="1" value="${esc(typeof v === 'string' ? v : '')}" placeholder="미제출 사유" aria-label="${r.no}번 미제출 사유">`}</div></td>`;
    if (it.type === 'level') return `<td><select class="lv" id="lv-${it.id}-${r.no}" data-item="${it.id}" data-no="${r.no}" aria-label="${r.no}번 ${esc(it.name)}"><option value=""></option>${(it.levels || []).map(l => `<option ${v === l ? 'selected' : ''}>${esc(l)}</option>`).join('')}</select></td>`;
    return `<td><input class="${it.type === 'text' ? 'txt' : ''}" ${it.type === 'score' ? 'type="number" inputmode="decimal"' : 'type="text"'} data-item="${it.id}" data-no="${r.no}" value="${esc(v ?? '')}" aria-label="${r.no}번 ${esc(it.name)}"></td>`;
  }).join('')}</tr>`).join('');
  const grs = [...new Set(items.filter(it => it.type === 'score' && it.group).map(it => it.group))];
  const avgHead = grs.map(g => { const al = roster.map(r => groupAverages(r.no).find(x => x.g === g)).filter(x => x && x.avg !== null).map(x => x.avg); return `<th class="avg">${esc(g)} 평균<span class="stat">반 ${al.length ? Math.round(al.reduce((a, b) => a + b, 0) / al.length * 10) / 10 : '—'}</span></th>`; }).join('');
  const body2 = grs.length ? rows.map((r, ri) => body.split('</tr>')[ri] + grs.map(g => { const x = groupAverages(r.no).find(y => y.g === g); return `<td class="avg">${x && x.avg !== null ? x.avg : ''}</td>`; }).join('') + '</tr>').join('') : body;
  $('#sheet').innerHTML = `<div class="tablewrap"><table class="sheet"><thead><tr><th>번호</th><th>이름</th>${head}${avgHead}</tr></thead><tbody>${body2 || `<tr><td colspan="${items.length + 2}" class="hint">모두 냈어요.</td></tr>`}</tbody></table></div>`;
}
function renderRoster(){
  if (ROS.m) ROS.m.render();
  renderRosterQuick();
}
function renderRosterQuick(){
  if (document.activeElement && document.activeElement.closest('#p-roster .quick')) return;
  $('#r-class').innerHTML = classOptions(S.profile.myClass, false);
  $('#r-text').value = (S.profile.roster || []).map(r => [r.no, r.name, r.sex].filter(Boolean).join(' ')).join('\n');
}
function renderMe(){
  renderHeader();
  $('#me-off').hidden = S.privateOk || !S.privateOffMsg;
  $('#me-on').hidden = !S.privateOk && !!S.privateOffMsg;
  if (S.privateOffMsg) $('#me-off-text').textContent = S.privateOffMsg;
  $$('#me-tabs button').forEach(b => { b.setAttribute('aria-selected', b.dataset.tab === S.meTab); const m = MPAGES.find(x => x[2] === b.dataset.tab); if (m){ if (!b.dataset.def) b.dataset.def = b.textContent; b.textContent = (S.profile.pageNames || {})[m[0]] || b.dataset.def; } });
  ['day', 'plan', 'todo', 'stu', 'cns', 'att', 'sheet', 'tt', 'budget', 'roster', 'mops', 'jday', 'jtt', 'jles', 'jprog', 'jcls', 'eval'].forEach(t => { $('#p-' + t).hidden = S.meTab !== t; });
  placeStuCol();
  $('#me-top').hidden = S.meTab !== 'day';
  renderToday(); renderNotes(); renderCats(); renderJPreview(); renderStage('j'); renderStage('cns'); renderStage('stu');
  ({day:renderDayBoard, plan:renderPlanPage, todo:renderTodo, stu:renderStu, cns:renderCns, att:renderAtt, sheet:renderSheet, tt:renderTT, budget:() => BUD.m && BUD.m.render(), roster:renderRoster, mops:() => renderOps(OPM), jday:renderJDay, jtt:renderJTT, jles:renderJLes, jprog:renderJProg, jcls:renderJCls, eval:renderEval})[S.meTab]();
}
function renderAll(){ renderGrade(); if (S.space === 'me') renderMe(); }

/* ---------- data ---------- */
const docs = snap => snap.docs.map(d => Object.assign({id:d.id}, d.data()));
function listen(ref, key, onData){
  S.pending.add(key);
  S.reg = S.reg || {}; S.liveSnap = S.liveSnap || {};
  S.reg[key] = onData;
  return ref.onSnapshot(snap => {
    if (!snap.metadata.fromCache){ S.pending.delete(key); if (!S.pending.size) banner(''); }
    S.liveSnap[key] = snap;
    if (S.arc && ARC_KEYS[key]) return;
    onData(snap);
  }, e => {
    S.pending.delete(key);
    if (e && e.code === 'revoked') banner('접근 권한이 바뀌어 더 이상 불러올 수 없어요.');
    else banner('일부 기록을 불러오지 못했어요. 페이지를 다시 열어 주세요.');
  });
}
const PROFILE = () => `data/users/${S.uid}/profile`;
const SHEET = () => `data/users/${S.uid}/sheet`;
const NOTES = () => `data/users/${S.uid}/notes`;
function listenDay(){
  if (!S.db || !S.uid) return;
  if (S.unsubDay) S.unsubDay();
  const k = S.jDate; S.day = {};
  S.unsubDay = S.db.doc(DAYPATH(k)).onSnapshot(snap => {
    if (k !== S.jDate || busy(DAYPATH(k))) return;
    S.day = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {};
    if (S.space === 'me' && S.meTab === 'day') renderDayBoard();
    if (S.space === 'me' && S.meTab === 'plan') renderPlanPage();
    if (S.space === 'me' && S.meTab === 'jday') renderJDay();
    if (S.space === 'me' && S.meTab === 'jles') renderJLes(true);
  }, () => {});
}
function listenDaily(){
  if (S.unsubDaily) S.unsubDaily();
  S.daily = null; S.dailyDirty = false; S.dailyImgs = []; S.dailyDrops = [];
  const k = S.selDate;
  S.unsubDaily = S.db.doc('daily/' + k).onSnapshot(snap => {
    if (k !== S.selDate) return;
    S.daily = snap.exists ? snap.data() : null;
    if (busy('daily/' + k)) return;
    renderDay(); resolveNames();
  }, () => {});
}
function startListening(){
  const db = S.db;
  listen(db.doc('grade/settings'), 'settings', snap => { if (snap.exists) S.settings = Object.assign({gradeName:'3학년', classCount:4, lunchAfter:3}, snap.data()); renderHeader(); renderPageHead(); renderMeal(); if (S.space === 'me') renderMe(); else if (S.page === 'budget') BUD.g.render(); else if (S.page === 'roster') ROS.g.render(); });
  listen(db.collection('events'), 'events', snap => { S.events = docs(snap); renderGradeToday(); renderCal(); renderDay(); renderTasks(); if (S.space === 'me') renderToday(); gcalSoon(); });
  listen(db.collection('tasks'), 'tasks', snap => { S.tasks = docs(snap); gcalSoon(); renderGradeToday(); renderCal(); renderDay(); renderTasks(); if (S.space === 'me'){ renderToday(); if (S.meTab === 'todo') renderTodo(); } });
  db.doc('daily/' + ymd(today())).onSnapshot(snap => { S.dailyToday = snap.exists ? snap.data() : null; renderGradeToday(); resolveNames(); }, () => {});
  listen(db.collection('notices'), 'notices', snap => { S.notices = docs(snap); renderNotices(); resolveNames(); });
  listen(db.collection('links'), 'links', snap => { S.links = docs(snap); renderLinks(); });
  listen(db.collection('lessons'), 'lessons', snap => { S.lessons = docs(snap); renderLessons(); renderCal(); if (S.space === 'me') renderToday(); });
  listen(db.doc('grade/jdtt'), 'jdtt', snap => { LS.jd = snap.exists ? ((snap.data() || {}).map || {}) : {}; renderLessons(); });
  listen(db.collection('ops'), 'ops', snap => { S.ops = docs(snap); if (S.page === 'ops') renderOps(); });
  listen(db.collection('phrases'), 'phrases', snap => { S.phG = docs(snap); if (S.page === 'ops') renderPhrases(); });
  listen(db.doc('grade/units'), 'gunits', snap => { if (busy('grade/units')) return; S.gunits = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {}; renderLinks(); });
  listen(db.doc('grade/memo'), 'gmemo', snap => { S.gmemo = snap.exists ? snap.data() : {}; renderGMemo(); });
  listen(db.collection('budget'), 'budget', snap => { S.budG = docs(snap); if (S.page === 'budget' && S.space === 'grade') BUD.g.render(); });
  listen(db.collection('roster'), 'roster', snap => {
    const m = {}; docs(snap).forEach(d => { m[d.id] = d; });
    Object.keys(S.rosG || {}).forEach(k => { if (busy('roster/' + k)) m[k] = S.rosG[k]; });
    S.rosG = m;
    if (S.profileLoaded) rosterAutoSync('grade');
    if (S.page === 'roster' && S.space === 'grade') ROS.g.render();
    if (S.space === 'me' && S.meTab === 'roster') ROS.m.render();
  });
  listen(db.collection('tabs'), 'tabs', snap => { S.tabs = docs(snap); renderStrip(); renderTabList(); renderTabPage(); });
  if (S.page === 'tab') listenRows();
  listenDaily();
  startPrivate();
  setTimeout(() => { if (S.pending.size) banner('기록을 불러오는 데 시간이 걸리고 있어요. 인터넷 연결을 확인해 주세요.'); }, 10000);
}
/* 나의 공간 기록 받기 (계정을 늦게 알게 돼도 다시 부를 수 있어요) */
function startPrivate(){
  if (!S.uid || S.privStarted) return;
  S.privStarted = true;
  const db = S.db;
    listen(db.doc(PROFILE()), 'profile', snap => {
      if (busy(PROFILE())) return;
      const wasJD = isJD();
      S.profile = Object.assign({myClass:'', roster:[]}, snap.exists ? snap.data() : {});
      if (S.pendRoute){ const pr = S.pendRoute; S.pendRoute = null; S.pendDone = true; try { history.replaceState(null, '', '#' + pr); } catch (e){} applyRoute(pr); }
      else if (wasJD !== isJD() && S.space === 'me'){ applyRoute(S.route); }
      if (!snap.metadata.fromCache){ S.profileLoaded = true; setTimeout(maybeShowNews, 600); }
      renderHeader(); renderTasks(); if (S.space === 'me') renderMe();
    });
    listen(db.doc(ROUTINE()), 'routine', snap => {
      if (busy(ROUTINE())) return;
      S.routine = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {items:[], done:{}};
      if (!Array.isArray(S.routine.items)) S.routine.items = []; if (!S.routine.done) S.routine.done = {}; if (!S.routine.extra) S.routine.extra = {};
      renderRoutine();
    });
    if (GAS) listen(db.doc(GCALP()), 'gcal', snap => {
      if (busy(GCALP())) return;
      const first = !S.gcal;
      S.gcal = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {target:'app', show:false, sent:{}};
      if (!S.gcal.sent) S.gcal.sent = {};
      if (first){ loadGEvents(); gcalSoon(); }
    });
    listen(db.doc(STUNOTES()), 'stunotes', snap => {
      if (busy(STUNOTES())) return;
      S.stuNotes = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {hb:{}};
      if (!S.stuNotes.hb) S.stuNotes.hb = {};
      if (S.space === 'me' && S.meTab === 'stu' && !(document.activeElement && document.activeElement.id === 'stu-hb')) renderStu();
    });
    listen(db.doc(EVP()), 'evalplan', snap => {
      if (busy(EVP())) return;
      S.ev = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {imgs:[]}; if (!Array.isArray(S.ev.imgs)) S.ev.imgs = []; if (!Array.isArray(S.ev.items)) S.ev.items = [];
      if (S.space === 'me' && S.meTab === 'eval' && !(document.activeElement && document.activeElement.closest('#ev-form'))) renderEval();
    });
    listen(db.doc(JDP()), 'jd', snap => {
      if (busy(JDP())) return;
      S.jd = jdNorm(snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {});
      renderHeader();
      if (S.space === 'me' && S.meTab === 'jtt' && !(document.activeElement && document.activeElement.closest('#p-jtt'))) renderJTT();
      if (S.space === 'me' && S.meTab === 'jday') renderJDay();
    });
    listen(db.doc(JLP()), 'jdles', snap => {
      if (busy(JLP())) return;
      S.jl = jlNorm(snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {});
      const ae = document.activeElement;
      if (S.space === 'me' && S.meTab === 'jles' && !(ae && ae.closest('#jl-add'))) renderJProg();
      if (S.space === 'me' && S.meTab === 'jles' && !(ae && ae.closest('#jl-rows'))) renderJLes(true);
      if (S.space === 'me' && S.meTab === 'jprog') renderJProg();
      if (S.space === 'me' && S.meTab === 'jday') renderJDay();
    });
    listen(db.doc(JCP()), 'jdcls', snap => {
      if (busy(JCP())) return;
      S.jc = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {};
      if (!S.jc.c) S.jc.c = {};
      if (S.space === 'me' && S.meTab === 'jcls' && !(document.activeElement && document.activeElement.closest('#jc-main'))) renderJCls();
    });
    listen(db.doc(PROFILE()).collection('phrases'), 'mphrases', snap => { S.phM = docs(snap); if (S.page === 'ops') renderPhrases(); });
    listen(db.doc(PROFILE()).collection('ops'), 'mops', snap => { S.mops = docs(snap); if (S.space === 'me' && S.meTab === 'mops') renderOps(OPM); });
    listen(db.doc(PROFILE()).collection('budget'), 'mbudget', snap => { S.budM = docs(snap); if (S.space === 'me' && S.meTab === 'budget') BUD.m.render(); });
    listen(db.doc(PROFILE()).collection('journal'), 'journal', snap => { S.journal = docs(snap); if (S.space === 'me') renderMe(); gcalSoon(); });
    listen(db.doc(NOTES()), 'notes', snap => {
      if (busy(NOTES())) return;
      S.notes = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {items:[]};
      if (!Array.isArray(S.notes.items)) S.notes.items = [];
      if (!Array.isArray(S.notes.done)) S.notes.done = [];
      if (S.space === 'me') renderNotes();
    });
    listenDay();
    listen(db.doc(TTPLAN()), 'ttplan', snap => {
      if (busy(TTPLAN())) return;
      S.ttplan = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {terms:[]};
      if (!Array.isArray(S.ttplan.terms)) S.ttplan.terms = [];
      buildTtIdx(); renderPageHead();
      if (S.space === 'me' && !(document.activeElement && document.activeElement.closest('#p-tt'))) renderMe();
    });
    listen(db.doc(SHEET()), 'sheet', snap => {
      if (busy(SHEET())) return;
      S.sheet = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {items:[], values:{}};
      if (!S.sheet.items) S.sheet.items = []; if (!S.sheet.values) S.sheet.values = {};
      if (S.space === 'me' && S.meTab === 'sheet' && !(document.activeElement && document.activeElement.closest('#sheet'))) renderSheet();
    });
}
async function boot(){
  if (window.__GAS_MODE) document.body.classList.add('gas');
  renderAll();
  const C = window.claude;
  if (!C || !C.use){ banner(window.__GAS_PREVIEW ? '미리보기 화면이라 기록이 비어 있어요. 구글 Apps Script에 설치한 뒤 웹 앱 주소로 열면 기록이 보여요.' : '이 페이지는 claude.ai에서 열어야 기록을 불러오고 저장할 수 있어요.'); return; }
  const [db, user, dl] = await Promise.all([C.use('db'), C.use('user'), C.use('downloads')]);
  S.db = db; S.user = user; S.dl = dl;
  try { S.assets = await C.use('assets'); } catch (e){ S.assets = null; }
  if (!db){
    banner('로그인한 상태로 열어야 기록을 불러오고 저장할 수 있어요.');
    S.canWrite = false; document.body.classList.add('ro');
    S.privateOffMsg = '로그인한 상태로 열면 나만 보는 학급일지를 쓸 수 있어요.'; renderAll(); return;
  }
  if (user){
    S.uid = await user.id();
    S.isOwner = await user.isOwner();
    const cw = await user.can('data.write');
    if (cw === false){ S.canWrite = false; document.body.classList.add('ro'); renderStrip(); if (window.__gasNoGrade) gradePickSoon(); else banner('학년 공간은 읽기만 할 수 있어요. 함께 고치려면 만든 선생님께 편집자로 초대해 달라고 해 주세요.'); }
  }
  if (S.uid) S.privateOk = true;
  else S.privateOffMsg = '이 화면에서는 나의 공간을 쓸 수 없어요. 초대받은 계정으로 로그인해서 열어 주세요.';
  startListening(); renderAll();
  if (!S.uid) setTimeout(maybeShowNews, 1200);
  setTimeout(() => { if (!newsChecked){ S.profileLoaded = true; maybeShowNews(); } }, 12000);
}

/* ---------- actions ---------- */
async function addEvent(p){
  try { const ref = await S.db.collection('events').add({date:p.date || S.selDate, time:p.time || null, title:p.text, who:p.who || '전체', kind:S.gaKind && S.gaKind !== 'auto' ? S.gaKind : guessKind(p.text), createdBy:S.uid, createdAt:Date.now()}); if (ref && ref.id) setTimeout(() => addAfter('ev:' + ref.id, '#cal-also-g'), 300); }
  catch (e){ wErr(e, true); return false; }
  return true;
}
async function addTask(p){
  const kind = p.kind || guessKind(p.text);
  try { await S.db.collection('tasks').add({title:p.text, due:p.date, who:p.who || '전체', repeat:p.repeat, every:p.every || null, eom:!!p.eom, prio:p.prio || '보통', kind, done:false, note:'', createdBy:S.uid, createdAt:Date.now()}); }
  catch (e){ wErr(e, true); return false; }
  return true;
}
function arm(key){
  if (S.armed === key) return true;
  S.armed = key; renderAll(); renderTabPage();
  clearTimeout(arm.t); arm.t = setTimeout(() => { S.armed = null; renderAll(); renderTabPage(); }, 4000);
  return false;
}
function saveProfile(){ queueSet(PROFILE(), () => ({motto:S.profile.motto || '', myClass:S.profile.myClass || '', roster:S.profile.roster || [], rosterExtra:S.profile.rosterExtra || [], rosterSync:!!S.profile.rosterSync, tabPrefs:S.profile.tabPrefs || {}, seenVersion:S.profile.seenVersion || '', timetable:S.profile.timetable || {}, pageNames:S.profile.pageNames || {}, role:S.profile.role || '', updatedAt:Date.now()}), false); }
function saveNotes(){ queueSet(NOTES(), () => ({items:S.notes.items, done:S.notes.done || []}), false); }
function saveSheet(){ queueSet(SHEET(), () => S.sheet, false); }
function openDlg(id){ $(id).hidden = false; const f = $(id).querySelector('input,select,textarea'); if (f) f.focus(); }
function closeDlgs(){ $$('.overlay').forEach(o => { o.hidden = true; }); S.armed = null; }

document.addEventListener('click', async ev => {
  if (ev.target.closest('#lightbox')){ $('#lightbox').hidden = true; return; }
  const timg = ev.target.closest('.thumb img'); if (timg && !timg.closest('.gm-imgs')){ openLightbox(timg.getAttribute('src')); return; }
  const rmb = ev.target.closest('[data-rmimg]'); if (rmb){ await removeImg(rmb.dataset.rmimg, +rmb.dataset.i); return; }
  const pk = ev.target.closest('[data-pick]'); if (pk){ pickImages(pk.dataset.pick); return; }
  const ic = ev.target.closest('.imgcell'); if (ic && S.canWrite){ pickImages(`cell:${ic.dataset.row}:${ic.dataset.col}`); return; }
  const sw = ev.target.closest('.switch button'); if (sw){ go(sw.dataset.space === 'me' ? 'me' : 'grade'); return; }
  const tpl = ev.target.closest('[data-tpl]'); if (tpl){ S.newTpl = tpl.dataset.tpl; renderTplPicker(); return; }
  const colx = ev.target.closest('[data-colx]'); if (colx){ syncEditCols(); const c = S.editCols[+colx.dataset.colx]; c.hidden = !c.hidden; renderEditCols(); return; }
  const cell = ev.target.closest('.cell'); if (cell){ S.selDate = cell.dataset.date; renderCal(); listenDaily(); renderDay(); renderGaPreview(); return; }
  if (ev.target.closest('[data-close]')){ closeDlgs(); return; }
  const hl = ev.target.closest('[data-hold-link]'); if (hl){ S.taskFilter = 'hold'; $$('#task-filter button').forEach(b => b.setAttribute('aria-pressed', b.dataset.f === 'hold')); setTimeout(renderTasks, 0); }
  const tf = ev.target.closest('#task-filter button'); if (tf){ S.taskFilter = tf.dataset.f; $$('#task-filter button').forEach(b => b.setAttribute('aria-pressed', b === tf)); renderTasks(); return; }
  const tab = ev.target.closest('#me-tabs button'); if (tab){ go(MPAGES.find(x => x[2] === tab.dataset.tab)[0]); return; }
  const cat = ev.target.closest('#j-cats button'); if (cat){ S.jForced = S.jForced === cat.dataset.cat ? null : cat.dataset.cat; renderCats(); renderJPreview(); $('#j-input').focus(); return; }
  const stu = ev.target.closest('#stu-grid button'); if (stu){ S.selStu = +stu.dataset.stu; S.stuCat = 'all'; renderStu(); return; }
  const cb = ev.target.closest('[data-cal]'); if (cb){ cb.disabled = true; gcalToggle(cb.dataset.cal).finally(() => { cb.disabled = false; }); return; }
  const os = ev.target.closest('[data-open-stu]'); if (os){ S.selStu = +os.dataset.openStu; S.stuCat = 'all'; if (S.route === 'me-stu') renderStu(); else go('me-stu'); window.scrollTo(0, 0); return; }
  const sc = ev.target.closest('[data-stu-cat]'); if (sc){ S.stuCat = sc.dataset.stuCat; renderStu(); return; }
  const sn = ev.target.closest('[data-stu-nav]'); if (sn){ const ro = S.profile.roster || []; const i = ro.findIndex(r => r.no === S.selStu); const nx = ro[(i + (+sn.dataset.stuNav) + ro.length) % ro.length]; if (nx){ S.selStu = nx.no; renderStu(); } return; }
  if (ev.target.closest('#stu-print')){ printStudent(S.selStu); return; }
  if (ev.target.closest('#hb-draft')){
    const no = S.selStu; const ta = $('#stu-hb'); if (!ta) return;
    const add = S.journal.filter(e => e.cat === '행발' && (e.students || []).includes(no)).sort((a, b) => (a.date || '') < (b.date || '') ? -1 : 1).map(e => e.text.trim()).filter(t => t && !ta.value.includes(t));
    if (!add.length){ toast('새로 붙일 행발 기록이 없어요.'); return; }
    ta.value = (ta.value.trim() ? ta.value.trim() + '\n' : '') + add.join('\n'); ta.dispatchEvent(new Event('input', {bubbles:true})); ta.focus(); toast(`${add.length}개를 초안에 붙였어요. 다듬어 주세요.`); return;
  }
  if (ev.target.closest('#relink-go')){ relinkNames(); return; }
  const ttt = ev.target.closest('[data-ttterm]'); if (ttt){ S.ttTerm = ttt.dataset.ttterm; renderTTOverview(); return; }
  const tds = ev.target.closest('#td-src button'); if (tds){ S.tdSrc = tds.dataset.src; renderTodo(); return; }
  const cf = ev.target.closest('#cns-filter button'); if (cf){ S.cnsF = cf.dataset.c; renderCns(); return; }
  const tt = ev.target.closest('#tool-tabs button'); if (tt){ showTool(tt.dataset.tool); return; }
  const pm = ev.target.closest('[data-min]'); if (pm){ timerSet(+pm.dataset.min * 60); return; }
  const a = ev.target.closest('[data-act]'); if (!a) return;
  const id = a.dataset.id, act = a.dataset.act;
  if (act === 'task-toggle'){
    const t = S.tasks.find(x => x.id === id); if (!t) return;
    try { await S.db.doc('tasks/' + id).update({done:!t.done, doneAt:!t.done ? Date.now() : null}); if (!t.done) spawnNext('task', t); } catch (e){ wErr(e, true); }
  } else if (act === 'event-done'){
    const e = S.events.find(x => x.id === id); if (!e) return;
    try { await S.db.doc('events/' + id).update({done:!e.done, doneAt:!e.done ? Date.now() : null}); toast(e.done ? '다시 남은 제출로 돌렸어요.' : '제출 끝! 달력에도 줄이 그어져요.'); } catch (er){ wErr(er, true); }
  } else if (act === 'task-hold'){
    const t = S.tasks.find(x => x.id === id); if (!t) return;
    try { await S.db.doc('tasks/' + id).update({hold:!t.hold, holdAt:!t.hold ? Date.now() : null}); toast(t.hold ? '다시 할 일로 돌렸어요.' : '보류로 빼 두었어요. 할 일 → "보류"에서 다시 꺼낼 수 있어요.'); } catch (e){ wErr(e, true); }
  } else if (act === 'me-hold'){
    const e0 = S.journal.find(x => x.id === id); if (!e0) return;
    try { await S.db.doc(PROFILE()).collection('journal').doc(id).update({hold:!e0.hold}); toast(e0.hold ? '다시 할 일로 돌렸어요.' : '보류로 빼 두었어요.'); } catch (er){ wErr(er, false); }
  } else if (act === 'task-defer'){
    const t = S.tasks.find(x => x.id === id); if (!t) return;
    const base = t.due && t.due >= ymd(today()) ? fromYmd(t.due) : today();
    const nd = ymd(addDays(base, 7));
    try { await S.db.doc('tasks/' + id).update({due:nd, deferred:(t.deferred || 0) + 1}); toast(`${fmtMD(nd)}로 미뤘어요.`); } catch (e){ wErr(e, true); }
  } else if (act === 'task-edit'){
    const t = S.tasks.find(x => x.id === id); if (!t) return;
    S.editTask = id; S.armed = null;
    $('#t-title').value = t.title || ''; $('#t-due').value = t.due || ''; $('#t-who').innerHTML = classOptions(t.who || '전체');
    $('#t-repeat').checked = !!t.repeat; $('#t-note').value = t.note || ''; $('#t-every').value = t.every === 'm' && t.eom ? 'me' : (t.every || '');
    $('#t-del').textContent = '삭제'; $('#t-del').classList.remove('armed');
    $$('#t-form input,#t-form select,#t-form textarea').forEach(el => { el.disabled = !S.canWrite; });
    openDlg('#dlg-task');
  } else if (act === 'event-del'){
    if (arm('event:' + id)){ S.armed = null; try { await S.db.doc('events/' + id).delete(); toast('일정을 지웠어요.'); } catch (e){ wErr(e, true); } }
  } else if (act === 'notice-del'){
    if (arm('notice:' + id)){ S.armed = null; const n = S.notices.find(x => x.id === id); try { await S.db.doc('notices/' + id).delete(); toast('공지를 지웠어요.'); (n && n.imgs || []).forEach(dropImage); } catch (e){ wErr(e, true); } }
  } else if (act === 'notice-pin'){
    const n = S.notices.find(x => x.id === id); if (!n) return;
    try { await S.db.doc('notices/' + id).update({pinned:!n.pinned}); } catch (e){ wErr(e, true); }
  } else if (act === 'link-del'){
    if (arm('link:' + id)){ S.armed = null; try { await S.db.doc('links/' + id).delete(); } catch (e){ wErr(e, true); } }
  } else if (act === 'entry-toggle'){
    const e = S.journal.find(x => x.id === id); if (!e) return;
    try { await S.db.doc(PROFILE()).collection('journal').doc(id).update({done:!e.done}); if (!e.done) spawnNext('entry', e); } catch (er){ wErr(er, false); }
  } else if (act === 'entry-edit'){
    const e = S.journal.find(x => x.id === id); if (!e) return;
    S.editEntry = id; S.armed = null;
    $('#e-date').value = e.date || ''; $('#e-time').value = e.time || ''; $('#e-end').value = e.end || '';
    $('#e-cat').innerHTML = CATS.map(c => `<option ${c === e.cat ? 'selected' : ''}>${c}</option>`).join('');
    $('#e-stu').value = (e.students || []).join(', '); $('#e-text').value = e.text || '';
    S.editImgs = (e.imgs || []).slice(); S.editDrops = []; renderEditThumbs();
    $('#e-del').textContent = '삭제'; $('#e-del').classList.remove('armed');
    openDlg('#dlg-entry');
  } else if (act === 'tick'){
    const it = a.dataset.item, no = a.dataset.no;
    S.sheet.values[it] = S.sheet.values[it] || {};
    if (S.sheet.values[it][no] === true) delete S.sheet.values[it][no]; else S.sheet.values[it][no] = true;
    renderSheet(); saveSheet();
  } else if (act === 'tt-make'){
    if (!S.uid) return; ensureWeek(S.ttMon); saveTtplan(); renderTTWeek(); renderTTOverview();
  } else if (act === 'mcal-prev' || act === 'mcal-next'){
    S.ttCal = new Date(S.ttCal.getFullYear(), S.ttCal.getMonth() + (act === 'mcal-next' ? 1 : -1), 1); renderTTNav();
  } else if (act === 'mcal-day'){
    const m0 = S.ttCal; goTTWeek(mondayOf(a.dataset.date)); S.ttCal = m0; renderTTNav();
  } else if (act === 'tt-goweek'){
    goTTWeek(a.dataset.mon);
    $('#tt-week-label').scrollIntoView({block:'start', behavior:'smooth'});
  } else if (act === 'tt-off'){
    const w = weekAt(S.ttMon); if (!w || !S.uid) return;
    const d = w.days[+a.dataset.i];
    if (d.off){ delete d.off; d.s = d.s && d.s.length ? d.s : ['', '', '', '', '', '']; }
    else d.off = HOLIDAYS[ymd(addDays(fromYmd(S.ttMon), +a.dataset.i))] || '휴업일';
    saveTtplan(); renderTTWeek(); renderTTOverview();
  } else if (act === 'acct'){
    closeDlgs(); openAcct();
  } else if (act === 'grade-pick'){
    openGradePick();
  } else if (act === 'late-today' || act === 'late-done'){
    if (act === 'late-done' && !twoStep(a, '정말 모두 끝냄?')) return;
    bulkLate(act === 'late-today' ? 'today' : 'done');
  } else if (act === 'board-me'){
    openBoard(S.jDate || ymd(today()));
  } else if (act === 'board-grade'){
    openBoard(S.page === 'daily' || S.page === 'calendar' ? S.selDate : ymd(today()));
  } else if (act === 'extract'){
    EX.to = a.dataset.to || 'event'; EX.items = []; renderExtract(); $('#ex-info').textContent = ''; openDlg('#dlg-extract');
  } else if (act === 'att-cell'){
    if (!S.uid){ toast('로그인한 상태로 열어야 적을 수 있어요.'); return; }
    openAttCell(+a.dataset.no, a.dataset.date);
  } else if (act === 'led-csv'){
    const m = attMonthStart(), all = $('#led-all').checked;
    save(`${a.dataset.led === 'abs' ? '결석계관리대장' : '교외체험학습대장'}_${all ? schoolYearOf(m).label : m.getFullYear() + '-' + pad(m.getMonth() + 1)}.csv`, csv(ledgerCsv(a.dataset.led)));
  } else if (act === 'led-print'){
    printLedger(a.dataset.led);
  } else if (act === 'led-form'){
    printAbsenceForm(a.dataset.id, +a.dataset.no);
  } else if (act === 'newtab'){
    openNewTab();
  } else if (act === 'tabarrange'){
    $('#dlg-tabs').hidden = false; renderTabArrange();
  } else if (act === 'cell-tick'){
    const r = S.rows.find(x => x.id === a.dataset.row); if (!r) return;
    const cur = (r.cells || {})[a.dataset.col];
    try { await S.db.doc(`tabs/${S.tabId}/rows/${a.dataset.row}`).update({cells:{[a.dataset.col]:!cur}}); } catch (er){ wErr(er, true); }
  } else if (act === 'row-del'){
    if (arm('row:' + id)){ S.armed = null; const r = S.rows.find(x => x.id === id); try { await S.db.doc(`tabs/${S.tabId}/rows/${id}`).delete(); Object.values((r && r.cells) || {}).forEach(v => { if (Array.isArray(v)) v.forEach(dropImage); }); } catch (er){ wErr(er, true); } }
    else renderTabPage();
  } else if (act === 'todo-toggle'){
    if (a.dataset.src === 'me'){ try { await S.db.doc(PROFILE()).collection('journal').doc(id).update({done:true}); toast('끝냈어요.'); spawnNext('entry', S.journal.find(x => x.id === id)); } catch (er){ wErr(er, false); } }
    else { try { await S.db.doc('tasks/' + id).update({done:true, doneAt:Date.now()}); toast('학년 할 일을 끝냈어요.'); spawnNext('task', S.tasks.find(x => x.id === id)); } catch (er){ wErr(er, true); } }
  } else if (act === 'todo-today'){
    try { await S.db.doc(PROFILE()).collection('journal').doc(id).update({date:ymd(today())}); } catch (er){ wErr(er, false); }
  } else if (act === 'att-fill'){
    const inp = $('#j-input'); const pre = a.dataset.no + '번 ';
    if (!inp.value.startsWith(pre)) inp.value = pre + inp.value.replace(/^\d{1,2}번\s*/, '');
    if (S.jDate !== ymd(today()) && !/\d{1,2}\s*[\/.]\s*\d{1,2}/.test(inp.value)) inp.value += `${fromYmd(S.jDate).getMonth()+1}/${fromYmd(S.jDate).getDate()} `;
    inp.focus(); inp.setSelectionRange(inp.value.length, inp.value.length); renderJPreview();
    inp.scrollIntoView({block:'center', behavior:'smooth'});
  } else if (act === 'day-check'){
    S.day.checks = Object.assign({}, S.day.checks);
    if (S.day.checks[a.dataset.no]) delete S.day.checks[a.dataset.no]; else S.day.checks[a.dataset.no] = true;
    renderDayBoard(); saveDay();
  } else if (act === 'note-del'){
    const gone = S.notes.items.find(n => n.id === id);
    S.notes.items = S.notes.items.filter(n => n.id !== id);
    if (gone){ S.notes.done = [Object.assign({}, gone, {doneAt:Date.now()})].concat(S.notes.done || []).slice(0, 300); }
    renderNotes(true); saveNotes(); toast('해결한 메모로 옮겼어요. 메모 칸 위 "해결한 메모"에서 볼 수 있어요.');
  } else if (act === 'note-back'){
    const n = (S.notes.done || []).find(x => x.id === id); if (!n) return;
    S.notes.done = S.notes.done.filter(x => x.id !== id);
    const b = Object.assign({}, n); delete b.doneAt; S.notes.items = [b].concat(S.notes.items || []);
    renderNotes(true); saveNotes(); toast('메모를 다시 붙였어요.');
  } else if (act === 'note-purge'){
    if (!arm('notedone:' + id)){ renderNotesDone(); return; }
    S.armed = null;
    const n = (S.notes.done || []).find(x => x.id === id);
    S.notes.done = (S.notes.done || []).filter(x => x.id !== id); renderNotesDone(); saveNotes(); toast('메모를 완전히 지웠어요.');
    (n && n.imgs || []).forEach(dropImage);
  } else if (act === 'item-del'){
    if (arm('item:' + id)){ S.armed = null; S.sheet.items = S.sheet.items.filter(x => x.id !== id); delete S.sheet.values[id]; renderSheet(); saveSheet(); }
    else renderSheet();
  }
});

$('#ga-event').onclick = () => { S.gaType = 'event'; setTimeout(renderKindPick, 0); $('#ga-event').setAttribute('aria-pressed', 'true'); $('#ga-task').setAttribute('aria-pressed', 'false'); $('#ga-input').placeholder = '예: 11/20 8:40 3학년 현장체험학습'; renderGaPreview(); $('#ga-input').focus(); };
$('#ga-task').onclick = () => { S.gaType = 'task'; setTimeout(renderKindPick, 0); $('#ga-task').setAttribute('aria-pressed', 'true'); $('#ga-event').setAttribute('aria-pressed', 'false'); $('#ga-input').placeholder = '예: 다음 주 금요일까지 동의서 수합 @2반 #매년'; renderGaPreview(); $('#ga-input').focus(); };
$('#ga-input').addEventListener('input', renderGaPreview);
$('#ga-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const v = $('#ga-input').value.trim(); if (!v || !S.db) return;
  const p = parseLine(v);
  if (!p.text){ toast('내용을 함께 적어 주세요.'); return; }
  const ok = S.gaType === 'event' ? await addEvent(p) : await addTask(Object.assign(p, S.gaKind && S.gaKind !== 'auto' ? {kind:S.gaKind} : {}));
  if (ok){
    $('#ga-input').value = ''; renderGaPreview();
    const d = p.date || (S.gaType === 'event' ? S.selDate : null);
    toast(S.gaType === 'event' ? `${fmtMD(d)} 일정에 넣었어요.` : '할 일에 넣었어요.');
    if (d){ const dd = fromYmd(d); if (dd.getMonth() !== S.month.getMonth() || dd.getFullYear() !== S.month.getFullYear()){ S.month = new Date(dd.getFullYear(), dd.getMonth(), 1); renderCal(); } }
  }
});
function renderTkPreview(){
  const v = $('#tk-input').value.trim();
  if (!v){ $('#tk-preview').textContent = '날짜를 적으면 마감일, "@2반"은 담당 반, "!높음"은 중요 표시로 들어가요.'; return; }
  const p = parseLine(v);
  $('#tk-preview').textContent = `마감 ${p.date ? fmtMD(p.date) : '없음'} · ${kindName(guessKind(p.text))} · 담당 ${p.who || '전체'}${p.prio === '높음' ? ' · 중요' : ''}${p.repeat ? ' · 매년 반복' : ''} · ${p.text || '(내용을 적어 주세요)'}`;
}
$('#tk-input').addEventListener('input', renderTkPreview);
$('#th-wk-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const v = $('#th-wk-input').value.trim(); if (!v || !S.db) return;
  if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  const p = parseLine(v); if (!p.text){ toast('할 일 내용을 적어 주세요.'); return; }
  if (!p.date) p.date = weekFri();
  if (await addTask(p)){ $('#th-wk-input').value = ''; toast(`${fmtMD(p.date)}까지 할 일로 넣었어요.`); }
});
$('#tk-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const v = $('#tk-input').value.trim(); if (!v || !S.db) return;
  if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  const p = parseLine(v);
  if (!p.text){ toast('할 일 내용을 적어 주세요.'); return; }
  if (await addTask(p)){ $('#tk-input').value = ''; renderTkPreview(); toast(p.date ? `${fmtMD(p.date)}까지 할 일로 넣었어요.` : '할 일에 넣었어요.'); }
});
renderTkPreview();
function calWeekShift(n){ const d = addDays(fromYmd(S.selDate), n); S.selDate = ymd(d); S.month = new Date(d.getFullYear(), d.getMonth(), 1); renderCal(); if (S.db) listenDaily(); renderDay(); }
$('#cal-prev').onclick = () => { if (S.calView === 'week') return calWeekShift(-7); S.month = new Date(S.month.getFullYear(), S.month.getMonth()-1, 1); renderCal(); };
$('#cal-next').onclick = () => { if (S.calView === 'week') return calWeekShift(7); S.month = new Date(S.month.getFullYear(), S.month.getMonth()+1, 1); renderCal(); };
document.addEventListener('change', async e => { const s0 = e.target.closest('[data-tk-kind]'); if (!s0) return; try { await S.db.doc('tasks/' + s0.dataset.tkKind).update({kind:s0.value}); } catch (er){ wErr(er, true); } });
$('#day-items').addEventListener('change', async e => { const s0 = e.target.closest('[data-ev-kind]'); if (!s0) return; try { await S.db.doc('events/' + s0.dataset.evKind).update({kind:s0.value}); } catch (er){ wErr(er, true); } });
$('#cal-view').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (!b) return; S.calView = b.dataset.v; try { localStorage.setItem('calView', S.calView); } catch (er){} renderCal(); });
try { S.calView = localStorage.getItem('calView') || 'month'; } catch (e){ S.calView = 'month'; }
$('#ga-kind').addEventListener('click', e => { const b = e.target.closest('[data-kind]'); if (!b) return; S.gaKind = b.dataset.kind; renderKindPick(); renderGaPreview(); });
$('#cal-today').onclick = () => { const d = today(); S.month = new Date(d.getFullYear(), d.getMonth(), 1); S.selDate = ymd(d); renderCal(); if (S.db) listenDaily(); renderDay(); };

['#d-plan', '#d-notice'].forEach(s => $(s).addEventListener('input', () => { if (!S.dailyDirty){ S.dailyDirty = true; $('#d-meta').textContent = '저장하지 않은 내용이 있어요'; } }));
$('#d-save').onclick = () => {
  if (!S.db) return;
  const k = S.selDate, plan = $('#d-plan').value, notice = $('#d-notice').value;
  S.dailyDirty = false;
  const imgs = S.dailyImgs.slice(), drops = S.dailyDrops.splice(0);
  queueSet('daily/' + k, () => ({date:k, plan, notice, imgs, updatedBy:S.uid, updatedAt:Date.now()}), true);
  drops.forEach(dropImage);
  toast(`${fmtMD(k)} 일일계획·알림장을 저장했어요.`);
};
$('#d-big').onclick = async () => {
  $('#big-title').textContent = `${fmtLong(S.selDate)} 알림장`;
  $('#big-body').textContent = $('#d-notice').value || (S.dailyImgs.length ? '' : '아직 알림장이 비어 있어요.');
  $('#big-imgs').innerHTML = S.dailyImgs.map(r => `<img data-img="${esc(imgKey(r))}" ${imgUrl(r) ? `src="${esc(imgUrl(r))}"` : ''} alt="알림장 사진">`).join('');
  $('#big').hidden = false;
  S.bigMode = ''; $('#big-hint').textContent = '글을 눌러 고쳐 쓸 수 있어요 · 여기서 고친 내용은 저장되지 않아요';
};
$('#big-close').onclick = async () => { $('#big').hidden = true; try { if (document.fullscreenElement) await document.exitFullscreen(); } catch (e) {} };

$('#n-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const title = $('#n-title').value.trim(), body = $('#n-body').value.trim();
  if (!title){ toast('제목을 적어 주세요.'); return; }
  const poll = mkPoll($('#n-poll').value, $('#n-multi').checked);
  if ($('#n-poll').value.trim() && !poll){ toast('투표는 고를 것을 두 줄 이상 적어 주세요.'); return; }
  const kind = $('#n-kind').value === 'auto' ? guessNk(title + ' ' + body) : $('#n-kind').value;
  try { await S.db.collection('notices').add(Object.assign({title, body, kind, imgs:S.stage.notice.slice(), pinned:$('#n-pin').checked, createdBy:S.uid, createdAt:Date.now()}, poll ? {poll} : {})); }
  catch (e){ wErr(e, true); return; }
  $('#n-poll').value = ''; $('#n-multi').checked = false; $('#n-pollbox').open = false;
  S.stage.notice = []; renderStage('notice');
  $('#n-title').value = ''; $('#n-body').value = ''; $('#n-pin').checked = false; $('#n-details').open = false; toast('공지를 올렸어요.');
});
$('#l-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  let url = $('#l-url').value.trim(); const title = $('#l-title').value.trim();
  if (url && !/^https?:\/\//i.test(url)) url = 'https://' + url;
  if (!url){ toast('주소를 적어 주세요.'); return; }
  const subj = $('#l-subj').value || guessSubj(title + ' ' + url);
  try { await S.db.collection('links').add({title:title || url, url, subj, createdBy:S.uid, createdAt:Date.now()}); }
  catch (e){ wErr(e, true); return; }
  $('#l-url').value = ''; $('#l-title').value = ''; toast('링크를 넣었어요.');
});

$('#t-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const id = S.editTask; if (!id || !S.canWrite) return;
  const title = $('#t-title').value.trim(); if (!title){ toast('할 일을 적어 주세요.'); return; }
  try { await S.db.doc('tasks/' + id).update({title, due:$('#t-due').value || null, who:$('#t-who').value, repeat:$('#t-repeat').checked, every:({w:'w', m:'m', me:'m'})[$('#t-every').value] || null, eom:$('#t-every').value === 'me', note:$('#t-note').value.trim()}); closeDlgs(); toast('저장했어요.'); }
  catch (e){ wErr(e, true); }
});
$('#t-del').onclick = async () => {
  const b = $('#t-del');
  if (!b.classList.contains('armed')){ b.classList.add('armed'); b.textContent = '한 번 더 누르면 삭제'; return; }
  try { await S.db.doc('tasks/' + S.editTask).delete(); closeDlgs(); toast('할 일을 지웠어요.'); } catch (e){ wErr(e, true); }
};

$('#j-input').addEventListener('input', renderJPreview);
$('#j-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  if (!S.db || !S.uid){ toast('로그인한 상태로 열어야 기록할 수 있어요.'); return; }
  const v = $('#j-input').value.trim(); if (!v && !S.stage.j.length) return;
  const p = parseLine(v, {students:true});
  const cat = inferCat(p.text, p.tags, S.jForced, p.students.length > 0);
  const entry = {date:p.date || (cat === '할일' ? null : S.jDate), end:p.end || null, time:p.time || null, cat, text:p.text, students:p.students,
    att:cat === '출결' ? inferAtt(p.text, p.students.length > 0) : null, prio:p.prio || '보통', area:areaOf(p), imgs:S.stage.j.slice(), every:cat === '할일' ? p.every || null : null, eom:!!p.eom, done:false, createdAt:Date.now()};
  try { await S.db.doc(PROFILE()).collection('journal').add(entry); }
  catch (e){ wErr(e, false); return; }
  $('#j-input').value = ''; S.jForced = null; S.stage.j = []; renderStage('j'); renderCats(); renderJPreview();
  if (cat === '할일') toast(entry.date ? `${fmtMD(entry.date)} 할 일로 적었어요.` : '언젠가 할 일로 적었어요.');
  else if (entry.date !== S.jDate) toast(`${fmtMD(entry.date)}에 적었어요.`); else toast('적었어요.');
});
const setJDate = k => { blurIn('#p-day'); S.jDate = k; listenDay(); renderDayBoard(); renderJPreview(); };
$('#j-prev').onclick = () => setJDate(ymd(addDays(fromYmd(S.jDate), -1)));
$('#j-next').onclick = () => setJDate(ymd(addDays(fromYmd(S.jDate), 1)));
$('#j-today').onclick = () => setJDate(ymd(today()));
$('#j-date').addEventListener('change', e => { if (e.target.value) setJDate(e.target.value); });
$('#j-export').onclick = () => {
  const rows = [['날짜','시각','분류','번호','이름','출결','내용','중요도','끝냄']];
  S.journal.slice().sort((a, b) => (a.date || '9') < (b.date || '9') ? -1 : (a.date || '9') > (b.date || '9') ? 1 : byTime(a, b)).forEach(e => {
    const nos = e.students && e.students.length ? e.students : [null];
    nos.forEach(n => { const r = n === null ? null : (S.profile.roster || []).find(x => x.no === n);
      rows.push([e.date || '언젠가', e.time || '', e.cat, n ?? '', r ? r.name || '' : '', attLabel(e.att), e.text, e.prio || '', e.cat === '할일' ? (e.done ? 'O' : '') : '']); });
  });
  save(`학급일지_${ymd(today())}.csv`, csv(rows));
};

$('#e-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const id = S.editEntry; if (!id) return;
  const text = $('#e-text').value.trim(), cat = $('#e-cat').value;
  const students = $('#e-stu').value.split(/[,\s]+/).map(x => parseInt(x, 10)).filter(n => !isNaN(n));
  const orig = S.journal.find(x => x.id === id) || {};
  const d0 = $('#e-date').value || (cat === '할일' ? null : S.jDate), e0 = $('#e-end').value || null;
  const upd = {date:d0, end:e0 && d0 && e0 > d0 ? e0 : null, time:$('#e-time').value || null, cat, text, students, att:cat === '출결' ? (inferAtt(text, students.length > 0) || orig.att || null) : null};
  upd.imgs = S.editImgs.slice();
  try { await S.db.doc(PROFILE()).collection('journal').doc(id).update(upd); S.editDrops.splice(0).forEach(dropImage); closeDlgs(); toast('고쳤어요.'); } catch (e){ wErr(e, false); }
});
$('#e-del').onclick = async () => {
  const b = $('#e-del');
  if (!b.classList.contains('armed')){ b.classList.add('armed'); b.textContent = '한 번 더 누르면 삭제'; return; }
  const en = S.journal.find(x => x.id === S.editEntry);
  try { await S.db.doc(PROFILE()).collection('journal').doc(S.editEntry).delete(); closeDlgs(); toast('기록을 지웠어요.'); [...((en && en.imgs) || []), ...S.editDrops.splice(0)].forEach(dropImage); } catch (e){ wErr(e, false); }
};

async function addEntryFrom(stageName, inputSel, opts){
  if (!S.db || !S.uid){ toast('로그인한 상태로 열어야 기록할 수 있어요.'); return; }
  const v = $(inputSel).value.trim(); if (!v && !S.stage[stageName].length) return;
  const p = parseLine(v, {students:true});
  const students = p.students.slice(); if (opts.student != null && !students.includes(opts.student)) students.unshift(opts.student);
  const cat = opts.cat || inferCat(p.text, p.tags, null, students.length > 0);
  const entry = {date:p.date || ymd(today()), end:p.end || null, time:p.time || null, cat, text:p.text, students,
    att:cat === '출결' ? inferAtt(p.text, students.length > 0) : null, prio:p.prio || '보통', area:areaOf(p), imgs:S.stage[stageName].slice(), every:cat === '할일' ? p.every || null : null, eom:!!p.eom, done:false, createdAt:Date.now()};
  try { const ref = await S.db.doc(PROFILE()).collection('journal').add(entry); if (ref && ref.id && inputSel === '#j-input' && entry.date) setTimeout(() => addAfter('j:' + ref.id, '#cal-also-j'), 300); } catch (e){ wErr(e, false); return; }
  $(inputSel).value = ''; S.stage[stageName] = []; renderStage(stageName); toast(`${fmtMD(entry.date)} ${cat} 기록으로 적었어요.`);
}
$('#cns-form').addEventListener('submit', ev => { ev.preventDefault(); addEntryFrom('cns', '#cns-input', {cat:$('#cns-cat').value}); });
$('#stu-form').addEventListener('submit', ev => { ev.preventDefault(); if (S.selStu === null) return; addEntryFrom('stu', '#stu-input', {student:S.selStu}); });

$('#sh-form').addEventListener('submit', ev => {
  ev.preventDefault();
  const name = $('#sh-name').value.trim(); if (!name){ toast('항목 이름을 적어 주세요.'); return; }
  if (!S.uid){ toast('로그인한 상태로 열어야 쓸 수 있어요.'); return; }
  const type = $('#sh-type').value;
  const item = {id:'i' + Date.now().toString(36), name, type, createdAt:Date.now()};
  const grp = $('#sh-group').value.trim(); if (grp) item.group = grp;
  if (type === 'level'){ item.levels = $('#sh-levels').value.split(/[,·\/]/).map(x => x.trim()).filter(Boolean).slice(0, 8); if (item.levels.length < 2){ toast('단계를 두 개 이상 쉼표로 적어 주세요. 예: 상, 중, 하'); return; } }
  S.sheet.items.push(item);
  $('#sh-name').value = ''; renderSheet(); saveSheet();
});
$('#sh-missing').addEventListener('change', e => { S.onlyMissing = e.target.checked; renderSheet(); });
$('#sh-type').addEventListener('change', e => { $('#sh-levels').hidden = e.target.value !== 'level'; });
$('#sheet').addEventListener('change', e => {
  const inp = e.target.closest('input[data-item], select[data-item]'); if (!inp) return;
  const it = inp.dataset.item, no = inp.dataset.no, v = inp.value.trim();
  S.sheet.values[it] = S.sheet.values[it] || {};
  if (v === '') delete S.sheet.values[it][no];
  else S.sheet.values[it][no] = inp.type === 'number' ? Number(v) : v;
  saveSheet();
  if (!(e.relatedTarget)) setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#sheet'))) renderSheet(); }, 0);
});

function parseRosterLines(lines){
  return lines.map(l => {
    let sex = null;
    l = l.replace(/[(\[]?\s*(여|남)(자)?\s*[)\]]?\s*$/, (_, x) => { sex = x; return ''; }).trim();
    const m = l.match(/^(\d{1,3})\s*(?:번)?[\s.)\]\-:]*(.*)$/);
    return m ? {no:+m[1], name:m[2].trim(), sex} : {no:null, name:l, sex};
  });
}
$('#r-renum').onclick = () => {
  const lines = $('#r-text').value.split('\n').map(l => l.trim()).filter(Boolean);
  if (!lines.length){ toast('먼저 명단을 적어 주세요.'); return; }
  const rs = parseRosterLines(lines);
  if (!rs.some(r => r.sex)){ toast('이름 뒤에 "여" 또는 "남"을 붙여 주세요. 예: 김민지 여'); return; }
  let f = parseInt($('#r-fstart').value, 10) || 1, m = parseInt($('#r-mstart').value, 10) || 41;
  const fs = rs.filter(r => r.sex === '여'), ms = rs.filter(r => r.sex === '남'), etc = rs.filter(r => !r.sex);
  fs.forEach(r => { r.no = f++; }); etc.forEach(r => { r.no = f++; }); ms.forEach(r => { r.no = m++; });
  $('#r-text').value = [...fs, ...etc, ...ms].map(r => [r.no, r.name, r.sex].filter(Boolean).join(' ')).join('\n');
  toast('번호를 다시 매겼어요. 확인하고 "명단 저장"을 눌러 주세요.');
};
$('#r-numbers').onclick = () => {
  const n = Math.max(1, Math.min(60, parseInt($('#r-count').value, 10) || 0));
  if (!parseInt($('#r-count').value, 10)){ toast('인원을 적어 주세요.'); return; }
  $('#r-text').value = Array.from({length:n}, (_, i) => String(i + 1)).join('\n');
};
$('#r-save').onclick = () => {
  if (!S.uid){ toast('로그인한 상태로 열어야 저장할 수 있어요.'); return; }
  const lines = $('#r-text').value.split('\n').map(l => l.trim()).filter(Boolean);
  const roster = []; let next = 1; const seen = new Set();
  for (const r0 of parseRosterLines(lines)){
    let no = r0.no ?? next;
    while (seen.has(no)) no++;
    seen.add(no); next = no + 1;
    const old = S.profile.roster || [];
    const prev = old.find(o => o.no === no && (!r0.name || !o.name || o.name === r0.name)) || (r0.name && old.find(o => o.name === r0.name)) || {};
    roster.push(Object.assign({}, prev, {no, name:r0.name}, r0.sex ? {sex:r0.sex} : {}));
  }
  roster.sort((a, b) => a.no - b.no);
  S.profile.roster = roster; S.profile.myClass = $('#r-class').value;
  saveProfile(); renderHeader(); renderTasks(); if (ROS.m) ROS.m.render(); toast(`명단 ${roster.length}명을 저장했어요.`);
};
$('#r-class').addEventListener('change', () => { if (!S.uid) return; S.profile.myClass = $('#r-class').value; saveProfile(); renderHeader(); renderTasks(); renderToday(); });

$('#open-settings').onclick = async () => {
  if (window.__GAS_MODE && S.user && S.uid){ $('#st-myname-wrap').hidden = false; const ps = await S.user.profiles([S.uid]); $('#st-myname').value = (ps[S.uid] && ps[S.uid].name) || ''; }
  $('#st-role').value = isJD() ? 'jd' : ''; $('#st-role-wrap').hidden = !S.uid;
  $('#st-name').value = S.settings.gradeName || ''; $('#st-count').value = S.settings.classCount || 4; $('#st-cnames').value = clsNames().filter(Boolean).join(', '); $('#st-lunch').value = String(lunchAt());
  if (GAS){ const ne = S.settings.neis; $('#ne-cur').textContent = ne ? `지금 학교: ${ne.name}` : '아직 학교를 정하지 않았어요.'; NE.schools = null; $('#ne-res').innerHTML = '<option value="">학교를 찾아 골라 주세요</option>'; const g = S.gcal || {}; $('#gc-target').value = g.target || 'app'; $('#gc-show').checked = !!g.show; }
  $$('#st-form input, #st-form select, #st-form textarea').forEach(el => { el.disabled = !S.canWrite; });
  openDlg('#dlg-settings');
};
$('#st-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const gradeName = $('#st-name').value.trim() || '3학년';
  const classNames = $('#st-cnames').value.split(/[,，\n]+/).map(x => x.trim()).filter(Boolean).slice(0, 20);
  const classCount = classNames.length || Math.max(1, Math.min(20, parseInt($('#st-count').value, 10) || 4));
  const lunchAfter = parseInt($('#st-lunch').value, 10) || 3;
  if (window.__GAS_MODE && S.uid && $('#st-myname').value.trim()){ try { await S.db.doc('members/' + S.uid).set({name:$('#st-myname').value.trim()}); } catch (e){} }
  const extra = {};
  if (GAS && NE.schools && $('#ne-res').value !== ''){ const sc = NE.schools[+$('#ne-res').value]; if (sc) extra.neis = {office:sc.office, code:sc.code, name:sc.name}; }
  if (GAS && S.uid){ S.gcal = S.gcal || {sent:{}}; const t = $('#gc-target').value, sh = $('#gc-show').checked; if (t !== (S.gcal.target || 'app') || sh !== !!S.gcal.show){ if (t !== (S.gcal.target || 'app') && Object.keys(S.gcal.sent || {}).length) toast('이미 넣은 기록은 원래 캘린더에 남아 있어요. 새로 넣는 것부터 바뀐 캘린더로 가요.'); S.gcal.target = t; S.gcal.show = sh; saveGcal(); loadGEvents(); } }
  if (!S.canWrite && !Object.keys(extra).length){ closeDlgs(); return; }
  try { await S.db.doc('grade/settings').set(Object.assign({}, S.settings, {gradeName, classCount, classNames, lunchAfter}, extra)); NE.meal = {}; closeDlgs(); toast('설정을 바꿨어요.'); } catch (e){ wErr(e, true); }
});
$('#export-grade').onclick = () => {
  const rows = [['종류','날짜','시각','대상','내용','끝냄','매년','다음엔']];
  S.events.slice().sort((a, b) => a.date < b.date ? -1 : 1).forEach(e => rows.push(['일정', e.date, e.time || '', e.who || '전체', e.title, '', '', '']));
  S.tasks.forEach(t => rows.push(['할 일', t.due || '', '', t.who || '전체', t.title, t.done ? 'O' : '', t.repeat ? 'O' : '', t.note || '']));
  S.notices.forEach(n => rows.push(['공지', n.createdAt ? ymd(new Date(n.createdAt)) : '', '', '', n.title + (n.body ? ' — ' + n.body : ''), '', '', '']));
  save(`${S.settings.gradeName || '학년'}_학년기록_${ymd(today())}.csv`, csv(rows));
};
$('#export-repeat').onclick = () => {
  const rows = [['할 일','올해 마감','맡은 반','다음엔']];
  S.tasks.filter(t => t.repeat).sort((a, b) => (a.due || '9') < (b.due || '9') ? -1 : 1).forEach(t => rows.push([t.title, t.due || '', t.who || '전체', t.note || '']));
  save(`매년반복업무_${S.settings.gradeName || '학년'}_${today().getFullYear()}.csv`, csv(rows));
};

$('#plan').addEventListener('change', e => {
  const inp = e.target.closest('input[data-pl]'); if (!inp || !S.uid) return;
  const plan = [];
  const base = (subjFor(S.jDate).s || []).map(expand);
  const prev = (S.day && S.day.plan) || [];
  for (let i = 0; i < 6; i++) plan.push(Object.assign({}, prev[i] || {}, {s:(v => v === (base[i] || '') ? null : v)($('#pl-s-' + i).value.trim()), t:$('#pl-t-' + i).value.trim(), p:$('#pl-p-' + i).value.trim()}));
  S.day.plan = plan; saveDay();
});
$('#day-memo').addEventListener('change', e => { if (!S.uid) return; S.day.memo = e.target.value; saveDay(); });
$('#chk-name').addEventListener('change', e => { if (!S.uid) return; S.day.checkName = e.target.value.trim(); saveDay(); renderDayBoard(); });
$('#note-add').onclick = () => {
  if (!S.uid){ toast('로그인한 상태로 열어야 메모를 쓸 수 있어요.'); return; }
  const id = 'n' + Date.now().toString(36);
  S.notes.items.push({id, text:'', color:S.notes.items.length % 4, createdAt:Date.now()});
  renderNotes(); saveNotes();
  const t = document.getElementById('nt-' + id); if (t) t.focus();
};
$('#notes').addEventListener('change', e => {
  const t = e.target.closest('textarea[data-note]'); if (!t) return;
  const n = S.notes.items.find(x => x.id === t.dataset.note); if (!n) return;
  n.text = t.value; saveNotes();
});
$('#notes').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#notes'))) renderNotes(); }, 0));
$('#td-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  if (!S.db || !S.uid){ toast('로그인한 상태로 열어야 적을 수 있어요.'); return; }
  const v = $('#td-input').value.trim(); if (!v) return;
  const p = parseLine(v);
  if (!p.text){ toast('할 일을 함께 적어 주세요.'); return; }
  try { await S.db.doc(PROFILE()).collection('journal').add({date:p.date, time:p.time, cat:'할일', text:p.text, students:[], att:null, prio:p.prio || '보통', area:areaOf(p), every:p.every || null, eom:!!p.eom, done:false, createdAt:Date.now()}); }
  catch (e){ wErr(e, false); return; }
  $('#td-input').value = ''; toast(p.date ? `${fmtMD(p.date)} 할 일로 적었어요.` : '언젠가 할 일로 적었어요.');
});
$('#td-high').addEventListener('change', e => { S.tdHigh = e.target.checked; renderTodo(); });
$('#tt-upload').onclick = () => { const f = $('#tt-file'); f.value = ''; f.click(); };
$('#tt-file').addEventListener('change', e => { const f = e.target.files && e.target.files[0]; if (f) importHwp(f); });
const ttDrop = $('.tt-upload');
['dragenter', 'dragover'].forEach(t => ttDrop.addEventListener(t, e => { e.preventDefault(); ttDrop.classList.add('drag'); }));
['dragleave', 'drop'].forEach(t => ttDrop.addEventListener(t, e => { e.preventDefault(); ttDrop.classList.remove('drag'); }));
ttDrop.addEventListener('drop', e => { const f = e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0]; if (f) importHwp(f); });
const ttShift = n => goTTWeek(ymd(addDays(fromYmd(S.ttMon || mondayOf(ymd(today()))), n)));
$('#ttw-prev').onclick = () => ttShift(-7);
$('#ttw-next').onclick = () => ttShift(7);
$('#ttw-now').onclick = () => goTTWeek(mondayOf(ymd(today())));
$('#ttw-pick').addEventListener('change', e => { if (e.target.value) goTTWeek(e.target.value); });
$('#ttw-date').addEventListener('change', e => {
  const v = e.target.value; if (!v) return;
  goTTWeek(mondayOf(v));
  const sf = subjFor(v), wd = fromYmd(v).getDay();
  toast(wd === 0 || wd === 6 ? `${fmtMD(v)}은 주말이라 그 주 시간표를 보여 드려요.` : sf.off ? `${fmtMD(v)} · ${sf.off}` : `${fmtMD(v)} · ${(sf.s || []).filter(Boolean).map(expand).join(', ') || '시간표 없음'}`);
});
$('#ttw-caltoggle').onclick = () => { S.ttCalOpen = !S.ttCalOpen; if (S.ttCalOpen){ const d = fromYmd(S.ttMon); S.ttCal = new Date(d.getFullYear(), d.getMonth(), 1); } renderTTNav(); };
$('#tt-week').addEventListener('change', e => {
  if (!S.uid) return;
  const w = weekAt(S.ttMon); if (!w) return;
  const inp = e.target;
  if (inp.dataset.ttoff !== undefined){ const d = w.days[+inp.dataset.ttoff]; d.off = inp.value.trim() || '휴일'; }
  else if (inp.dataset.tti !== undefined){ const d = w.days[+inp.dataset.tti]; d.s = d.s || []; while (d.s.length < 6) d.s.push(''); d.s[+inp.dataset.ttp] = inp.value.trim(); inp.title = expand(inp.value); }
  else return;
  saveTtplan(); renderTTOverview();
});
$('#tt-week').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#tt-week'))) renderTTWeek(); }, 0));
$('#tt-note').addEventListener('change', e => {
  const w = weekAt(S.ttMon); if (!w || !S.uid) return;
  w.note = e.target.value; w.events = parseNoteEvents(w.note, w.mon); saveTtplan(); renderTTOverview(); toast('이 주 학교 행사를 저장했어요.');
});
$('#tt-save').onclick = () => {
  if (!S.uid){ toast('로그인한 상태로 열어야 저장할 수 있어요.'); return; }
  const tt = {};
  [1, 2, 3, 4, 5].forEach(w => { tt[w] = []; for (let i = 0; i < 6; i++) tt[w].push($(`#tt-${w}-${i}`).value.trim()); });
  S.profile.timetable = tt; saveProfile(); toast('시간표를 저장했어요.');
};
$('#th-big').onclick = async () => {
  $('#big-title').textContent = `${fmtLong(ymd(today()))} 알림장`;
  const dti = (S.dailyToday && S.dailyToday.imgs) || [];
  $('#big-body').textContent = (S.dailyToday && S.dailyToday.notice) || (dti.length ? '' : '아직 오늘 알림장이 비어 있어요.');
  $('#big-imgs').innerHTML = dti.map(r => `<img data-img="${esc(imgKey(r))}" ${imgUrl(r) ? `src="${esc(imgUrl(r))}"` : ''} alt="알림장 사진">`).join('');
  $('#big').hidden = false;
  S.bigMode = ''; $('#big-hint').textContent = '글을 눌러 고쳐 쓸 수 있어요 · 여기서 고친 내용은 저장되지 않아요';
};
$('#th-write').onclick = () => {
  const d = today(); S.selDate = ymd(d); S.month = new Date(d.getFullYear(), d.getMonth(), 1);
  renderCal(); if (S.db) listenDaily(); renderDay();
  $('#d-notice').scrollIntoView({block:'center', behavior:'smooth'}); setTimeout(() => $('#d-notice').focus(), 300);
};

$('#tab-table').addEventListener('change', async e => {
  const inp = e.target.closest('input[data-row]'); if (!inp || !S.canWrite) return;
  let v = inp.value.trim();
  if (inp.type === 'number') v = v === '' ? null : Number(v);
  if (v === '') v = null;
  try { await S.db.doc(`tabs/${S.tabId}/rows/${inp.dataset.row}`).update({cells:{[inp.dataset.col]:v}}); } catch (er){ wErr(er, true); }
});
$('#tab-table').addEventListener('keydown', e => {
  const inp = e.target.closest('input[data-row]'); if (!inp || e.key !== 'Enter') return;
  e.preventDefault();
  const all = $$(`#tab-table [data-col="${inp.dataset.col}"]`); const i = all.indexOf(inp);
  if (all[i + 1]) all[i + 1].focus(); else inp.blur();
});
$('#tab-table').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#tab-table'))) renderTabPage(); }, 0));
$('#row-add').onclick = async () => {
  if (!S.db || !S.tabId) return;
  const ref = S.db.collection(`tabs/${S.tabId}/rows`).doc();
  S.focusRow = ref.id;
  try { await ref.set({cells:{}, order:Date.now(), createdBy:S.uid}); } catch (er){ S.focusRow = null; wErr(er, true); }
};
$('#tab-export').onclick = () => {
  const t = S.tabs.find(x => x.id === S.tabId); if (!t) return;
  const cols = (t.cols || []).filter(c => !c.hidden);
  const rows = [cols.map(c => c.name)];
  S.rows.slice().sort((a, b) => (a.order || 0) - (b.order || 0)).forEach(r => rows.push(cols.map(c => { const v = cellVal(r, c); return c.type === 'check' ? (v ? 'O' : '') : c.type === 'image' ? (Array.isArray(v) && v.length ? `사진 ${v.length}장` : '') : v; })));
  save(`${t.name}_${ymd(today())}.csv`, csv(rows));
};
$('#nt-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const tpl = TEMPLATES.find(t => t.key === S.newTpl) || TEMPLATES[0];
  const name = $('#nt-name').value.trim() || (tpl.key === 'blank' ? '새 탭' : tpl.name);
  const ref = S.db.collection('tabs').doc();
  try { await ref.set({name, cols:tpl.cols.map(([n, t]) => ({id:cid(), name:n, type:t})), createdAt:Date.now(), createdBy:S.uid}); }
  catch (er){ wErr(er, true); return; }
  closeDlgs(); toast(`"${name}" 탭을 만들었어요.`); go('t-' + ref.id);
});
$('#tab-addimg').onclick = async () => {
  const tb = (S.tabs || []).find(x => x.id === S.tabId); if (!tb) return;
  const cols = (tb.cols || []).map(c => Object.assign({}, c));
  const old = cols.find(c => c.type === 'image');
  if (old) old.hidden = false; else cols.push({id:cid(), name:'사진', type:'image'});
  try { await S.db.doc('tabs/' + S.tabId).update({cols}); toast('사진 칸을 만들었어요. 칸을 누르거나 사진을 복사해 Ctrl+V로 붙여 넣어요.'); } catch (er){ wErr(er, true); }
};
$('#tab-edit').onclick = () => {
  const t = S.tabs.find(x => x.id === S.tabId); if (!t) return;
  S.editCols = JSON.parse(JSON.stringify(t.cols || []));
  $('#tb-name').value = t.name || ''; renderEditCols(); fillBudgetForm(t);
  $('#tb-del').textContent = '탭 지우기'; $('#tb-del').classList.remove('armed');
  openDlg('#dlg-tab');
};
$('#tb-addcol').onclick = () => { syncEditCols(); S.editCols.push({id:cid(), name:'새 열', type:'text'}); renderEditCols(); const n = $('#tbc-name-' + (S.editCols.length - 1)); if (n){ n.focus(); n.select(); } };
$('#tb-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  syncEditCols();
  const name = $('#tb-name').value.trim() || '이름 없는 탭';
  try { await S.db.doc('tabs/' + S.tabId).update({name, cols:S.editCols, budget:readBudgetForm()}); closeDlgs(); toast('탭을 고쳤어요.'); } catch (er){ wErr(er, true); }
});
async function deleteTab(id){
  if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  const t = S.tabs.find(x => x.id === id);
  try {
    const snap = await S.db.collection(`tabs/${id}/rows`).get();
    for (const d of snap.docs){ const cells = (d.data() || {}).cells || {}; Object.values(cells).forEach(v => { if (Array.isArray(v)) v.forEach(dropImage); }); await S.db.doc(`tabs/${id}/rows/${d.id}`).delete(); }
    await S.db.doc('tabs/' + id).delete();
    closeDlgs(); toast(`"${(t && t.name) || '탭'}" 탭을 지웠어요.`);
    if (S.route === 't-' + id) go('grade');
  } catch (er){ wErr(er, true); }
}
$('#tb-del').onclick = () => {
  const b = $('#tb-del');
  if (!b.classList.contains('armed')){ b.classList.add('armed'); b.textContent = '줄까지 모두 지워져요. 한 번 더 누르기'; return; }
  deleteTab(S.tabId);
};
$('#tab-del').onclick = () => { const b = $('#tab-del'); if (!twoStep(b, '모든 선생님 화면에서 지워져요. 한 번 더 누르기')) return; deleteTab(S.tabId); };
$('#tablist').addEventListener('click', e => { const b = e.target.closest('[data-tab-del]'); if (!b) return; if (!twoStep(b, '정말 지우기')) return; deleteTab(b.dataset.tabDel); });
const shiftDay = n => {
  const d = addDays(fromYmd(S.selDate), n); S.selDate = ymd(d);
  if (d.getMonth() !== S.month.getMonth() || d.getFullYear() !== S.month.getFullYear()) S.month = new Date(d.getFullYear(), d.getMonth(), 1);
  renderCal(); if (S.db) listenDaily(); renderDay();
};
$('#day-prev').onclick = () => shiftDay(-1);
$('#day-next').onclick = () => shiftDay(1);
$('#day-today').onclick = () => { S.selDate = ymd(addDays(today(), 0)); shiftDay(0); };

/* ---------- print (구글 버전에서만) ---------- */
function printDoc(html){
  const pa = $('#printarea'); pa.innerHTML = html; pa.hidden = false;
  document.body.classList.add('printing');
  const done = () => { document.body.classList.remove('printing'); pa.hidden = true; pa.innerHTML = ''; window.removeEventListener('afterprint', done); };
  window.addEventListener('afterprint', done);
  setTimeout(() => { try { window.print(); } catch (e){ toast('이 화면에서는 인쇄할 수 없어요.'); } setTimeout(done, 1500); }, 60);
}

/* ---------- 공문·메시지에서 일정 뽑기 ---------- */
const EX = {items:[], to:'event'};
function extractItems(text, to){
  const out = [], seen = new Set();
  text.replace(/\r/g, '').split('\n').forEach(line => {
    const raw = line.trim(); if (raw.length < 3) return;
    const clean = raw.replace(/^[\s\-–—•·○●◦▶▷►※*>□■◇◆☞✔✓]+/, '').replace(/^\(?\d{1,2}[).]\s+(?!\d)/, '').replace(/^[가-하][.)]\s+/, '');
    const p = parseLine(clean);
    if (!p.date) return;
    let t = (p.text || '').replace(/^\s*\(?\d{1,2}[).]\s+/, '').replace(/\(\s*[월화수목금토일]\s*\)/g, ' ').replace(/\s+/g, ' ').replace(/^[\s,.:·\-~]+|[\s,.:·\-~]+$/g, '').trim();
    if (!t) return;
    const key = p.date + '|' + t; if (seen.has(key)) return; seen.add(key);
    let kind = to === 'mine' ? 'mine' : /까지|제출|마감|회신|수합|입력|발송|신청|보고|완료/.test(raw) ? 'task' : 'event';
    if (kind !== 'mine' && !S.canWrite) kind = 'mine';
    out.push({on:true, date:p.date, end:p.end, time:p.time || '', text:t, kind, src:raw});
  });
  return out;
}
function renderExtract(){
  const it = EX.items;
  if (!it.length){ $('#ex-list').innerHTML = ''; $('#ex-count').textContent = ''; $('#ex-add').disabled = true; return; }
  const opts = k => (S.canWrite ? `<option value="event" ${k === 'event' ? 'selected' : ''}>학년 일정</option><option value="task" ${k === 'task' ? 'selected' : ''}>학년 할 일</option>` : '') + `<option value="mine" ${k === 'mine' ? 'selected' : ''}>내 할 일</option>`;
  $('#ex-list').innerHTML = `<div class="tablewrap"><table class="ex"><thead><tr><th></th><th>날짜</th><th>시각</th><th>내용</th><th>넣을 곳</th></tr></thead><tbody>${it.map((x, i) => `<tr class="${x.on ? '' : 'off'}">
    <td><input type="checkbox" id="ex-on-${i}" data-ex="${i}" data-f="on" ${x.on ? 'checked' : ''} aria-label="${i + 1}번째 넣기"></td>
    <td><input type="date" id="ex-d-${i}" data-ex="${i}" data-f="date" value="${x.date}">${x.end ? `<span class="src">~ ${fmtMD(x.end)}까지</span>` : ''}</td>
    <td><input type="time" id="ex-t-${i}" data-ex="${i}" data-f="time" value="${x.time}"></td>
    <td><input type="text" id="ex-x-${i}" data-ex="${i}" data-f="text" value="${esc(x.text)}"><span class="src">${esc(x.src)}</span></td>
    <td><select id="ex-k-${i}" data-ex="${i}" data-f="kind">${opts(x.kind)}</select></td></tr>`).join('')}</tbody></table></div>`;
  const n = it.filter(x => x.on).length;
  $('#ex-count').textContent = `${it.length}개 찾음 · ${n}개 고름`;
  $('#ex-add').disabled = !n; $('#ex-add').textContent = `고른 것 넣기 (${n})`;
}
$('#ex-run').onclick = () => {
  EX.items = extractItems($('#ex-text').value, EX.to);
  $('#ex-info').textContent = EX.items.length ? '날짜·시각·내용을 고치고, 넣지 않을 줄은 체크를 풀어 주세요.' : '날짜가 있는 줄을 찾지 못했어요. "11월 25일", "11.25" 같은 날짜가 들어 있는지 확인해 주세요.';
  renderExtract();
};
$('#ex-list').addEventListener('change', e => {
  const el = e.target.closest('[data-ex]'); if (!el) return;
  const x = EX.items[+el.dataset.ex], f = el.dataset.f;
  x[f] = f === 'on' ? el.checked : el.value;
  if (f === 'on') renderExtract();
});
$('#ex-add').onclick = async () => {
  if (!S.db){ toast('기록을 저장할 수 없는 화면이에요.'); return; }
  const pick = EX.items.filter(x => x.on && x.date && x.text.trim());
  let ok = 0;
  $('#ex-add').disabled = true;
  for (const x of pick){
    try {
      if (x.kind === 'event') await S.db.collection('events').add({date:x.date, time:x.time || null, title:x.text.trim() + (x.end ? ` (~${mdShort(x.end)})` : ''), who:'전체', kind:guessKind(x.text), createdBy:S.uid, createdAt:Date.now()});
      else if (x.kind === 'task') await S.db.collection('tasks').add({title:x.text.trim(), due:x.end || x.date, who:'전체', repeat:false, prio:'보통', done:false, note:'', createdBy:S.uid, createdAt:Date.now()});
      else { if (!S.uid) throw {code:'invalid_argument'}; await S.db.doc(PROFILE()).collection('journal').add({date:x.end || x.date, end:null, time:x.time || null, cat:'할일', text:x.text.trim(), students:[], att:null, prio:'보통', imgs:[], done:false, createdAt:Date.now()}); }
      ok++;
    } catch (e){ wErr(e, x.kind !== 'mine'); break; }
  }
  if (ok){ toast(`${ok}개를 넣었어요.`); closeDlgs(); $('#ex-text').value = ''; EX.items = []; renderExtract(); $('#ex-info').textContent = ''; }
  else $('#ex-add').disabled = false;
};

/* ---------- 출결 ---------- */
const ATT_MARK = {결석:'결', 지각:'지', 조퇴:'조', 결과:'과'};
const ATT_COLS = [['결석', '질병', '질결'], ['결석', '미인정', '미결'], ['결석', '기타', '기결'], ['결석', '출석인정', '인결'], ['지각', null, '지각'], ['조퇴', null, '조퇴'], ['결과', null, '결과']];
function isSchoolDay(k){ const d = fromYmd(k), w = d.getDay(); if (w === 0 || w === 6 || HOLIDAYS[k]) return false; return !subjFor(k).off; }
function daysBetween(a, b){ const out = []; for (let d = fromYmd(a); ymd(d) <= b; d = addDays(d, 1)) out.push(ymd(d)); return out; }
const schoolDaysBetween = (a, b) => daysBetween(a, b).filter(isSchoolDay);
function attEntries(){ return S.journal.filter(e => e.att && e.att.kind && e.date && (e.students || []).length); }
function attIndex(){
  const ix = {};
  attEntries().forEach(e => {
    const days = e.end ? schoolDaysBetween(e.date, e.end) : [e.date];
    e.students.forEach(no => days.forEach(k => { ix[no + '|' + k] = {kind:e.att.kind, reason:e.att.reason, e}; }));
  });
  return ix;
}
function attMonthStart(){ if (!S.attMonth){ const d = today(); S.attMonth = new Date(d.getFullYear(), d.getMonth(), 1); } return S.attMonth; }
function monthDays(){
  const m = attMonthStart(), last = new Date(m.getFullYear(), m.getMonth() + 1, 0);
  const all = daysBetween(ymd(m), ymd(last));
  const sch = all.filter(isSchoolDay);
  return {all, sch, first:ymd(m), last:ymd(last)};
}
function schoolYearOf(d){ const y = d.getMonth() >= 2 ? d.getFullYear() : d.getFullYear() - 1; return {from:`${y}-03-01`, to:`${y + 1}-02-${new Date(y + 1, 2, 0).getDate()}`, label:`${y}학년도`}; }
function renderAtt(){
  const m = attMonthStart(), {sch, first, last} = monthDays(), tk = ymd(today());
  $('#att-month').textContent = `${m.getFullYear()}년 ${m.getMonth() + 1}월 출석부`;
  $('#att-days').textContent = `수업일수 ${sch.length}일`;
  $('#att-legend').innerHTML = '<span><b>결</b> 결석 · <b>지</b> 지각 · <b>조</b> 조퇴 · <b>과</b> 결과</span><span><b class="mk-질병">파랑</b> 질병 · <b class="mk-미인정">빨강</b> 미인정 · <b class="mk-기타">주황</b> 기타 · <b class="mk-출석인정">초록</b> 출석인정</span>';
  const roster = S.profile.roster || [];
  if (!roster.length){ $('#att-grid').innerHTML = '<p class="empty">"명단" 탭에서 우리 반 명단을 넣으면 출석부가 만들어져요.</p>'; }
  else {
    const ix = attIndex();
    const dayCount = {};
    let h = `<div class="tablewrap"><table class="attg"><thead><tr><th>학생</th>${sch.map(k => { const d = fromYmd(k); return `<th class="${k === tk ? 'today' : ''}">${d.getDate()}<small>${WD[d.getDay()]}</small></th>`; }).join('')}${ATT_COLS.map(c => `<th>${c[2]}</th>`).join('')}</tr></thead><tbody>`;
    roster.forEach(r => {
      const tot = ATT_COLS.map(() => 0);
      h += `<tr><td class="nm"><span class="mono">${r.no}</span>${esc(r.name || '')}</td>`;
      sch.forEach(k => {
        const a = ix[r.no + '|' + k];
        if (a){ const ci = ATT_COLS.findIndex(c => c[0] === a.kind && (c[1] === null || c[1] === a.reason)); if (ci >= 0) tot[ci]++; if (a.kind === '결석') dayCount[k] = (dayCount[k] || 0) + 1; }
        h += `<td><button type="button" data-act="att-cell" data-no="${r.no}" data-date="${k}" class="${a ? 'mk-' + a.reason : ''}" title="${a ? esc(attLabel(a)) + (a.e.text ? ' · ' + esc(a.e.text) : '') : ''}" aria-label="${r.no}번 ${fromYmd(k).getDate()}일 ${a ? esc(attLabel(a)) : '출석'}">${a ? ATT_MARK[a.kind] || '·' : ''}</button></td>`;
      });
      h += tot.map(n => `<td class="tot ${n ? 'has' : ''}">${n || ''}</td>`).join('') + '</tr>';
    });
    h += `</tbody><tfoot><tr><td class="nm">결석 인원</td>${sch.map(k => `<td>${dayCount[k] || ''}</td>`).join('')}<td colspan="${ATT_COLS.length}"></td></tr></tfoot></table></div>`;
    $('#att-grid').innerHTML = h;
  }
  renderLedgers();
}
function prevSchoolDay(k){ let d = fromYmd(k); for (let i = 0; i < 20; i++){ d = addDays(d, -1); const x = ymd(d); const w = d.getDay(); if (w !== 0 && w !== 6 && !HOLIDAYS[x]) return x; } return ymd(addDays(fromYmd(k), -1)); }
function ledgerRows(type){
  const all = $('#led-all').checked;
  const {first, last} = monthDays();
  const sy = schoolYearOf(attMonthStart());
  const [lo, hi] = all ? [sy.from, sy.to] : [first, last];
  return attEntries().filter(e => e.att.kind === '결석' && (type === 'trip' ? e.att.reason === '출석인정' : e.att.reason !== '출석인정'))
    .filter(e => e.date <= hi && (e.end || e.date) >= lo)
    .flatMap(e => e.students.map(no => ({e, no})))
    .sort((a, b) => a.e.date < b.e.date ? -1 : a.e.date > b.e.date ? 1 : a.no - b.no);
}
const stuNm = no => { const r = (S.profile.roster || []).find(x => x.no === no); return r ? r.name || '' : ''; };
const entryDays = e => e.end ? schoolDaysBetween(e.date, e.end).length : 1;
function renderLedgers(){
  if (document.activeElement && document.activeElement.closest('.ledger')) return;
  const f = (e, k, ph) => `<input type="text" id="lf-${e.id}-${k}" data-led-e="${e.id}" data-led-f="${k}" value="${esc((e.doc || {})[k] ?? (k === 'reason' || k === 'title' ? e.text || '' : ''))}" placeholder="${ph}" aria-label="${ph}">`;
  const ck = (e, k = 'done', l = '서류 완결') => `<input type="checkbox" id="lf-${e.id}-${k}" data-led-e="${e.id}" data-led-f="${k}" ${(e.doc || {})[k] ? 'checked' : ''} aria-label="${l}">`;
  const abs = ledgerRows('abs');
  $('#led-abs').innerHTML = abs.length ? `<div class="tablewrap"><table class="led"><thead><tr><th>번호</th><th>이름</th><th>기간</th><th>일수</th><th>종류</th><th>사유(질병명)</th><th>증빙서류</th><th>완결</th><th>나이스</th><th class="gas-only">신고서</th></tr></thead><tbody>${abs.map(({e, no}) => `<tr>
    <td class="n">${no}</td><td>${esc(stuNm(no))}</td><td class="n">${mdShort(e.date)}${e.end ? '~' + mdShort(e.end) : ''}</td><td class="n">${entryDays(e)}</td><td>${esc(e.att.reason)}결석</td>
    <td>${f(e, 'reason', '사유')}</td><td>${f(e, 'proof', '진단서·처방전·학부모 의견서')}</td><td class="ck">${ck(e)}</td><td class="ck">${ck(e, 'neis', '나이스 입력')}</td>
    <td class="n gas-only"><button type="button" class="btn small" data-act="led-form" data-id="${e.id}" data-no="${no}">인쇄</button></td></tr>`).join('')}</tbody></table></div>`
    : '<p class="empty">이 기간에 질병·기타·미인정 결석이 없어요.</p>';
  const trip = ledgerRows('trip');
  $('#led-trip').innerHTML = trip.length ? `<div class="tablewrap"><table class="led"><thead><tr><th>번호</th><th>이름</th><th>시작일</th><th>종료일</th><th>일수</th><th title="체험 시작 하루 전까지 (주말·공휴일 빼고)">신청 기한</th><th>체험활동명</th><th>장소(기관)</th><th>활동내용</th><th>완결</th><th>나이스</th></tr></thead><tbody>${trip.map(({e, no}) => `<tr>
    <td class="n">${no}</td><td>${esc(stuNm(no))}</td><td class="n">${mdShort(e.date)}</td><td class="n">${mdShort(e.end || e.date)}</td><td class="n">${entryDays(e)}</td><td class="n">${(() => { const dl = prevSchoolDay(e.date); return `<span class="${dl < ymd(today()) && !(e.doc || {}).done ? 'neg' : ''}">${mdShort(dl)}(${WD[fromYmd(dl).getDay()]})</span>`; })()}</td>
    <td>${f(e, 'title', '예: 가족여행')}</td><td>${f(e, 'place', '장소')}</td><td>${f(e, 'content', '활동내용')}</td><td class="ck">${ck(e)}</td><td class="ck">${ck(e, 'neis', '나이스 입력')}</td></tr>`).join('')}</tbody></table></div>`
    : '<p class="empty">이 기간에 체험학습(출석인정 결석)이 없어요. 학급일지에 "3번 11/18~20 체험학습 가족여행"처럼 적으면 여기 모여요.</p>';
}
$('#p-att').addEventListener('change', async e => {
  const el = e.target.closest('[data-led-e]'); if (!el){ if (e.target.id === 'led-all') renderLedgers(); return; }
  const v = el.type === 'checkbox' ? el.checked : el.value.trim();
  try { await S.db.doc(PROFILE()).collection('journal').doc(el.dataset.ledE).update({doc:{[el.dataset.ledF]:v}}); } catch (er){ wErr(er, false); }
});
$('#p-att').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('.ledger'))) renderLedgers(); }, 0));
const attShift = n => { const m = attMonthStart(); S.attMonth = new Date(m.getFullYear(), m.getMonth() + n, 1); renderAtt(); };
$('#att-prev').onclick = () => attShift(-1);
$('#att-next').onclick = () => attShift(1);
$('#att-now').onclick = () => { S.attMonth = null; renderAtt(); };
$('#att-csv').onclick = () => {
  const {sch} = monthDays(), ix = attIndex(), m = attMonthStart();
  const rows = [['번호', '이름', ...sch.map(k => `${fromYmd(k).getMonth() + 1}/${fromYmd(k).getDate()}`), ...ATT_COLS.map(c => c[2])]];
  (S.profile.roster || []).forEach(r => {
    const tot = ATT_COLS.map(() => 0);
    const cells = sch.map(k => { const a = ix[r.no + '|' + k]; if (!a) return ''; const ci = ATT_COLS.findIndex(c => c[0] === a.kind && (c[1] === null || c[1] === a.reason)); if (ci >= 0) tot[ci]++; return attLabel(a); });
    rows.push([r.no, r.name || '', ...cells, ...tot.map(n => n || '')]);
  });
  save(`출석부_${m.getFullYear()}-${pad(m.getMonth() + 1)}.csv`, csv(rows));
};
function attSelHtml(no, k, ix){
  const a = ix[no + '|' + k], v = a ? `${a.kind}|${a.reason}` : '';
  const opts = $('#at-kind').innerHTML.replace('출석 (기록 지우기)', '출석').replace(' (체험학습 등)', '').replace(/ selected(="[^"]*")?/g, '').replace(`value="${v}"`, `value="${v}" selected`);
  return `<select class="att-sel ${v ? 'on' : ''}" data-attsel="${no}" aria-label="${no}번 출결">${opts}</select>`;
}
document.addEventListener('change', async e => {
  const sel = e.target.closest && e.target.closest('[data-attsel]'); if (!sel || !S.uid) return;
  const no = isNaN(+sel.dataset.attsel) ? sel.dataset.attsel : +sel.dataset.attsel, k = S.jDate;
  const rec = attIndex()[no + '|' + k], v = sel.value;
  sel.disabled = true;
  const ok = await attWrite(no, k, rec, v, rec ? rec.e.text || '' : '', rec && rec.e.end ? rec.e.end : '');
  sel.disabled = false;
  if (ok) toast(v ? `${stuName(no)} ${sel.options[sel.selectedIndex].text}으로 적었어요. 사유는 출결 탭에서 더 적을 수 있어요.` : `${stuName(no)} 출석으로 바꿨어요.`);
});
function openAttCell(no, k){
  const rec = attIndex()[no + '|' + k];
  S.attCell = {no, k, rec};
  $('#at-title').textContent = `${stuName(no)} · ${fmtLong(k)}`;
  $('#at-kind').value = rec ? `${rec.kind}|${rec.reason}` : '';
  $('#at-end').value = rec && rec.e.end ? rec.e.end : '';
  $('#at-text').value = rec ? rec.e.text || '' : '';
  const multi = rec && (rec.e.end || (rec.e.students || []).length > 1);
  $('#at-note').textContent = multi ? `이 칸은 ${rec.e.end ? `${mdShort(rec.e.date)}~${mdShort(rec.e.end)} 기간 기록` : '여러 학생이 함께 적힌 기록'}의 일부예요. 바꾸면 ${rec.e.end ? '기간 전체가' : '이 학생 것만'} 바뀌어요.` : '';
  openDlg('#dlg-att');
}
$('#at-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  if (!S.uid || !S.attCell) return;
  const {no, k, rec} = S.attCell;
  if (await attWrite(no, k, rec, $('#at-kind').value, $('#at-text').value.trim(), $('#at-end').value)){ closeDlgs(); toast($('#at-kind').value ? '출결을 적었어요.' : '출석으로 바꿨어요.'); }
});
async function attWrite(no, k, rec, v, text, endV){
  const start = rec && rec.e.end ? rec.e.date : k;
  const end = endV && endV > start ? endV : null;
  const col = S.db.doc(PROFILE()).collection('journal');
  try {
    if (rec){
      const others = (rec.e.students || []).filter(n => n !== no);
      if (!v){
        if (others.length) await col.doc(rec.e.id).update({students:others}); else await col.doc(rec.e.id).delete();
      } else {
        const [kind, reason] = v.split('|');
        if (others.length){
          await col.doc(rec.e.id).update({students:others});
          await col.add({date:start, end, time:null, cat:'출결', text, students:[no], att:{kind, reason}, prio:'보통', imgs:[], done:false, createdAt:Date.now()});
        } else await col.doc(rec.e.id).update({date:start, end, text, att:{kind, reason}, cat:'출결'});
      }
    } else if (v){
      const [kind, reason] = v.split('|');
      await col.add({date:k, end, time:null, cat:'출결', text, students:[no], att:{kind, reason}, prio:'보통', imgs:[], done:false, createdAt:Date.now()});
    }
    return true;
  } catch (e){ wErr(e, false); return false; }
}
function ledgerCsv(type){
  const rows = type === 'abs' ? [['번호', '이름', '시작일', '종료일', '결석일수', '종류', '사유(질병명)', '증빙서류', '서류완결', '나이스입력']] : [['번호', '이름', '시작일', '종료일', '교육과정일수', '체험활동명', '장소(기관)', '활동내용', '서류완결', '나이스입력']];
  ledgerRows(type).forEach(({e, no}) => {
    const d = e.doc || {};
    rows.push(type === 'abs'
      ? [no, stuNm(no), e.date, e.end || e.date, entryDays(e), e.att.reason + '결석', d.reason ?? e.text ?? '', d.proof || '', d.done ? 'O' : '', d.neis ? 'O' : '']
      : [no, stuNm(no), e.date, e.end || e.date, entryDays(e), d.title ?? e.text ?? '', d.place || '', d.content || '', d.done ? 'O' : '', d.neis ? 'O' : '']);
  });
  return rows;
}
function classLabel(){ return `${S.settings.gradeName || ''} ${S.profile.myClass || ''}`.trim(); }
async function teacherName(){ if (!S.user || !S.uid) return ''; try { const p = await S.user.profiles([S.uid]); return (p[S.uid] && p[S.uid].name) || ''; } catch (e){ return ''; } }
async function printLedger(type){
  const rows = ledgerCsv(type), sy = schoolYearOf(attMonthStart()), t = await teacherName();
  const title = type === 'abs' ? '결석계 관리대장' : '교외체험학습 대장';
  printDoc(`<div class="pdoc"><h1 style="font-size:18pt;letter-spacing:.1em">${title}</h1><div class="meta"><span>${sy.label} ${esc(classLabel())}</span><span>담임: ${esc(t)}</span></div>
    <table><thead><tr>${rows[0].map(h => `<th>${esc(h)}</th>`).join('')}</tr></thead><tbody>${rows.slice(1).map(r => `<tr>${r.map(c => `<td>${esc(c)}</td>`).join('')}</tr>`).join('') || `<tr><td colspan="${rows[0].length}">기록 없음</td></tr>`}</tbody></table>
    ${type === 'trip' ? '<p style="font-size:9.5pt;margin-top:4mm">비고: 기본 체험학습 일수 초과 시 교감 선생님 확인</p>' : ''}</div>`);
}
async function printAbsenceForm(id, no){
  const e = S.journal.find(x => x.id === id); if (!e) return;
  const d = e.doc || {}, t = await teacherName(), td = today();
  const range = `${fmtLong(e.date)}${e.end ? ' ~ ' + fmtLong(e.end) : ''} (${entryDays(e)}일간)`;
  printDoc(`<div class="pdoc"><h1>결석신고서</h1>
    <table><tr><th style="width:22%">학년 반 번호</th><td>${esc(classLabel())} ${no}번</td><th style="width:14%">이름</th><td>${esc(stuNm(no))}</td></tr>
    <tr><th>결석 기간</th><td colspan="3">${range}</td></tr>
    <tr><th>결석 종류</th><td colspan="3">${esc(e.att.reason)}결석</td></tr>
    <tr><th>결석 사유</th><td colspan="3">${esc(d.reason ?? e.text ?? '')}</td></tr>
    <tr><th>증빙 서류</th><td colspan="3">${esc(d.proof || '')}</td></tr></table>
    <p style="margin-top:8mm;font-size:12pt">위 학생은 위와 같은 사유로 결석하였음을 신고합니다.</p>
    <div class="sign">${td.getFullYear()}년 ${td.getMonth() + 1}월 ${td.getDate()}일<br>보호자: ________________ (서명)</div>
    <div class="box"><b>담임교사 확인</b><br>위 학생은 ( ${esc(d.reason ?? e.text ?? '')} )(으)로 인하여 결석하였음을 확인합니다.</div>
    <div class="sign">담임교사: ${esc(t) || '________________'} (서명)</div>
    <p style="font-size:9pt;margin-top:6mm">※ 학교 규정에 따라 일정 기간 이상 연속 질병결석 시 진단서 또는 소견서를 함께 제출합니다.</p></div>`);
}

/* ---------- 학년 탭 예산 요약 ---------- */
function renderBudget(t){
  const b = t.budget, el = $('#tab-budget');
  if (!b || !(Number(b.total) > 0)){ el.innerHTML = ''; return; }
  const amt = (t.cols || []).find(c => c.id === b.amountCol) || (t.cols || []).find(c => c.type === 'number');
  if (!amt){ el.innerHTML = ''; return; }
  const pur = (t.cols || []).find(c => c.id === b.purposeCol) || (t.cols || []).find(c => c.type === 'text');
  const num = r => Number((r.cells || {})[amt.id]) || 0;
  const total = Number(b.total), spent = S.rows.reduce((a, r) => a + num(r), 0), left = total - spent;
  const pct = Math.min(100, Math.round(spent / total * 100));
  const won = n => n.toLocaleString('ko-KR') + '원';
  const lim = (b.limits || []).map(l => {
    const used = S.rows.filter(r => pur && String((r.cells || {})[pur.id] || '').includes(l.name)).reduce((a, r) => a + num(r), 0);
    const cap = Math.round(total * l.pct / 100);
    return `<div class="limit ${used > cap ? 'over' : ''}"><div class="t"><span>${esc(l.name)} (${l.pct}%)</span><span>${won(used)} / ${won(cap)}</span></div><div class="bar ${used > cap ? 'over' : ''}"><i style="width:${Math.min(100, cap ? Math.round(used / cap * 100) : 0)}%"></i></div></div>`;
  }).join('');
  el.innerHTML = `<div class="budget-sum"><div class="nums"><span>총 예산<b>${won(total)}</b></span><span>쓴 돈<b>${won(spent)}</b></span><span style="color:${left < 0 ? 'var(--danger)' : 'inherit'}">남은 돈<b>${won(left)}</b></span></div>
    <div class="bar ${left < 0 ? 'over' : ''}"><i style="width:${pct}%"></i></div>${lim ? `<div class="limits">${lim}</div>` : ''}${left < 0 ? '<span class="hint" style="color:var(--danger)">총 예산을 넘었어요.</span>' : ''}</div>`;
}
function fillBudgetForm(t){
  const cols = t.cols || [], b = t.budget || {};
  const numCols = cols.filter(c => c.type === 'number' && !c.hidden), txtCols = cols.filter(c => c.type === 'text' && !c.hidden);
  $('#tb-budget').hidden = !numCols.length;
  $('#tb-total').value = b.total || '';
  $('#tb-amt').innerHTML = numCols.map(c => `<option value="${esc(c.id)}" ${c.id === b.amountCol ? 'selected' : ''}>${esc(c.name)}</option>`).join('');
  $('#tb-purpose').innerHTML = txtCols.map(c => `<option value="${esc(c.id)}" ${c.id === b.purposeCol ? 'selected' : ''}>${esc(c.name)}</option>`).join('');
  $('#tb-limits').value = (b.limits || []).map(l => `${l.name} ${l.pct}`).join('\n');
}
function readBudgetForm(){
  if ($('#tb-budget').hidden) return null;
  const total = Number($('#tb-total').value);
  if (!(total > 0)) return null;
  const limits = $('#tb-limits').value.split('\n').map(l => l.trim()).map(l => { const m = l.match(/^(.+?)\s*(\d{1,3})\s*%?$/); return m ? {name:m[1].trim(), pct:Math.min(100, +m[2])} : null; }).filter(Boolean);
  return {total, amountCol:$('#tb-amt').value || null, purposeCol:$('#tb-purpose').value || null, limits};
}

/* ---------- 붙여넣은 표 읽기 (스프레드시트·에듀파인) ---------- */
function pasteRows(text){
  const lines = String(text || '').replace(/\r/g, '').split('\n').filter(l => l.trim());
  const tab = lines.some(l => l.includes('\t'));
  return lines.map(l => (tab ? l.split('\t') : l.trim().split(/\s{2,}/)).map(c => c.replace(/^"|"$/g, '').trim()));
}
function headerMap(row, rules){
  const map = row.map(h => { const k = h.replace(/\s+/g, ' ').trim(); for (const [re, f, not] of rules){ if (re.test(k) && !(not && not.test(k))) return f; } return null; });
  return map.filter(Boolean).length >= 2 ? map : null;
}
const numIn = v => { const n = Number(String(v ?? '').replace(/[,\s원₩]/g, '')); return isFinite(n) ? n : 0; };
const wonS = n => (Math.round(n) || 0).toLocaleString('ko-KR');
const rid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
function twoStep(btn, label){
  if (btn.dataset.armed){ return true; }
  btn.dataset.armed = '1'; const old = btn.textContent; btn.textContent = label || '한 번 더'; btn.classList.add('armed');
  setTimeout(() => { if (btn.isConnected){ delete btn.dataset.armed; btn.textContent = old; btn.classList.remove('armed'); } }, 3000);
  return false;
}

/* ---------- 예산 ---------- */
function budCalc(l){
  const o = {base:numIn(l.amount), adj:0, req:0, spent:0};
  (l.logs || []).forEach(g => { const a = numIn(g.amt); if (g.kind === '증액') o.adj += a; else if (g.kind === '감액') o.adj -= a; else if (g.kind === '요구') o.req += a; else o.spent += a; });
  o.cur = o.base + o.adj; o.rest = o.cur - o.req - o.spent; return o;
}
const BUD_HDR = [[/구분|학년.?학급|사용처|사용\s*구분/, 'scope'], [/원가|비목/, 'stat'], [/세부\s*항목/, 'item'], [/세부\s*사업|단위\s*사업/, 'biz'], [/주요\s*활동|활동\s*명|사업\s*명/, 'act'], [/잔액/, 'rest'], [/현액|편성|배정|예산\s*액/, 'amount'], [/요구/, 'req'], [/집행|지출|사용\s*액/, 'spent'], [/^항목$/, 'item']];
const BUD_POS = ['act', 'biz', 'item', 'stat', 'amount', 'rest', 'req'];
const BUD_KIND_LABEL = {집행:'집행 (−)', 요구:'요구·품의 (−)', 증액:'증액 (+)', 감액:'감액 (−)'};
function makeBudget(key){
  const g = key === 'g';
  const st = {filter:'all', open:new Set()};
  const root = $('#bud-' + key);
  const list = () => ((g ? S.budG : S.budM) || []).slice().sort((a, b) => (a.order || a.createdAt || 0) - (b.order || b.createdAt || 0));
  const col = () => g ? S.db.collection('budget') : S.db.doc(PROFILE()).collection('budget');
  const can = () => !!S.db && (g ? S.canWrite : !!S.uid);
  const err = e => wErr(e, g);
  const nCls = () => Math.max(1, Math.min(20, +S.settings.classCount || 4));
  const sVal = l => l.scope === '학급' ? (g ? (l.cls || '학급') : '학급') : '학년';
  const match = l => { const f = st.filter; if (f === 'all') return true; if (f === '학년') return l.scope !== '학급'; if (f === '학급') return l.scope === '학급'; return l.scope === '학급' && l.cls === f; };
  const scopeOf = v => v === '학년' ? {scope:'학년', cls:null} : v === '학급' ? {scope:'학급', cls:null} : {scope:'학급', cls:v};
  root.innerHTML = `<div class="bud-sum"></div>
    <div class="bud-bar"><div class="seg bud-filter" role="group" aria-label="구분 고르기"></div><span class="grow"></span>
      <button type="button" class="btn small primary" data-b="add">+ 예산 줄 추가</button><button type="button" class="btn small" data-b="csv">CSV로 받기</button></div>
    <details class="bud-paste"><summary>에듀파인·스프레드시트에서 붙여넣기</summary>
      <p class="hint">제목 줄까지 함께 복사하면 구분·주요활동·세부사업·세부항목·원가통계비목·예산현액·예산잔액·요구금액 칸을 알아서 찾아요. 제목 없이 붙이면 "주요활동, 세부사업, 세부항목, 원가통계비목, 예산현액, 예산잔액, 요구금액" 순서로 읽어요. 구분 칸이 없으면 지금 고른 구분${g ? '(반)' : ''}으로 들어가요. 현액과 잔액의 차이는 "가져오기 전 집행액"으로 적어 둬요.</p>
      <textarea rows="5" id="bud-${key}-paste" aria-label="붙여넣을 예산 표" placeholder="여기에 Ctrl+V"></textarea>
      <div class="row"><span class="hint bud-info"></span><span class="grow"></span><button type="button" class="btn small primary" data-b="import">표로 넣기</button></div>
    </details>
    <div class="bud-table"></div>
    <details class="bud-wish" open><summary>사야 할 것 <span class="hint wish-n"></span></summary>
      <div class="wish-list"></div>
      <div class="wish-add"><input type="text" id="wi-${key}-n" placeholder="사야 할 것 (예: 이름 자석)" aria-label="사야 할 것"><input type="text" inputmode="numeric" class="amt" id="wi-${key}-p" placeholder="예상 금액" aria-label="예상 금액"><select id="wi-${key}-l" aria-label="쓸 예산 줄"></select><button type="button" class="btn small" data-b="wish-add">더하기</button></div>
      <p class="hint" style="margin:0">"샀어요"를 누르면 고른 예산 줄에 집행으로 들어가 잔액에서 빠져요. 금액은 그때 고칠 수 있어요.</p>
    </details>
    <p class="hint">줄 끝의 "내역"을 열고 쓴 돈(집행)·품의 올린 돈(요구)·증액·감액을 적으면 예산현액과 잔액이 저절로 더하고 빠져요. 품의한 돈을 실제로 쓰면 "집행으로"를 눌러 주세요.</p>`;
  function renderSum(){
    const all = list();
    const groups = [['all', '전체', all], ['학년', '학년 사용', all.filter(l => l.scope !== '학급')], ['학급', g ? '학급 사용 (모든 반)' : '학급 사용', all.filter(l => l.scope === '학급')]];
    if (g) for (let i = 1; i <= nCls(); i++){ const c = i + '반'; const ls = all.filter(l => l.scope === '학급' && l.cls === c); if (ls.length) groups.push([c, clsLabel(c), ls]); }
    $('.bud-filter', root).innerHTML = groups.map(([v, n, ls]) => `<button type="button" data-filter="${v}" aria-pressed="${st.filter === v}">${n.replace(' (모든 반)', '')} <small>${ls.length}</small></button>`).join('');
    $('.bud-sum', root).innerHTML = groups.slice(0, 3).map(([v, n, ls]) => {
      const t = ls.reduce((a, l) => { const c = budCalc(l); a.cur += c.cur; a.req += c.req; a.spent += c.spent; a.rest += c.rest; return a; }, {cur:0, req:0, spent:0, rest:0});
      const used = t.cur > 0 ? Math.min(100, Math.round((t.req + t.spent) / t.cur * 100)) : 0;
      return `<div class="bud-card ${st.filter === v ? 'on' : ''}"><h3><span>${n}</span><small>${ls.length}줄</small></h3>
        <dl><dt>예산현액</dt><dd>${wonS(t.cur)}</dd><dt>요구금액</dt><dd>${wonS(t.req)}</dd><dt>집행액</dt><dd>${wonS(t.spent)}</dd><dt>예산잔액</dt><dd class="rest ${t.rest < 0 ? 'neg' : ''}">${wonS(t.rest)}원</dd></dl>
        <div class="bar ${t.rest < 0 ? 'over' : ''}" title="쓴 비율 ${used}%"><i style="width:${used}%"></i></div></div>`;
    }).join('');
  }
  function scopeOpts(l){
    const v = sVal(l); let h = `<option value="학년" ${v === '학년' ? 'selected' : ''}>학년</option>`;
    if (g){ if (v === '학급') h += '<option value="학급" selected>학급</option>'; for (let i = 1; i <= nCls(); i++) h += `<option value="${i}반" ${v === i + '반' ? 'selected' : ''}>${esc(clsLabel(i + '반'))}</option>`; }
    else h += `<option value="학급" ${v === '학급' ? 'selected' : ''}>학급</option>`;
    return h;
  }
  function logsHTML(l, c){
    const logs = (l.logs || []).slice().sort((a, b) => (a.date || '') < (b.date || '') ? -1 : (a.date || '') > (b.date || '') ? 1 : (a.at || 0) - (b.at || 0));
    let bal = c.base;
    const dis = can() ? '' : 'disabled';
    const rows = logs.map(x => {
      const a = numIn(x.amt); bal += x.kind === '증액' ? a : -a;
      return `<tr><td class="n">${esc(x.date ? mdShort(x.date) : '')}</td><td><span class="kind k-${esc(x.kind)}">${esc(x.kind)}</span></td><td>${esc(x.text || '')}</td>
        <td class="n">${x.kind === '증액' ? '+' : '−'}${wonS(a)}</td><td class="n ${bal < 0 ? 'neg' : ''}">${wonS(bal)}</td>
        <td class="act">${x.kind === '요구' && can() ? `<button type="button" class="btn small" data-b="settle" data-id="${esc(l.id)}" data-log="${esc(x.id)}">집행으로</button>` : ''}${can() ? `<button type="button" class="x" data-b="log-del" data-id="${esc(l.id)}" data-log="${esc(x.id)}" aria-label="내역 지우기">×</button>` : ''}</td></tr>`;
    }).join('');
    return `<div class="logs"><table><thead><tr><th>날짜</th><th>종류</th><th>내용</th><th>금액</th><th>남은 돈</th><th></th></tr></thead>
      <tbody><tr class="start"><td></td><td><span class="kind">편성</span></td><td>처음 예산</td><td class="n">${wonS(c.base)}</td><td class="n">${wonS(c.base)}</td><td></td></tr>${rows}</tbody></table>
      ${can() ? `<div class="log-add">
        <input type="date" id="bl-${key}-${l.id}-d" value="${ymd(today())}" aria-label="날짜" ${dis}>
        <select id="bl-${key}-${l.id}-k" aria-label="종류">${Object.entries(BUD_KIND_LABEL).map(([k, n]) => `<option value="${k}">${n}</option>`).join('')}</select>
        <input type="text" id="bl-${key}-${l.id}-t" placeholder="내용 (예: 체험학습 버스 대절)" aria-label="내용">
        <input type="text" inputmode="numeric" id="bl-${key}-${l.id}-a" class="amt" placeholder="금액" aria-label="금액">
        <button type="button" class="btn small primary" data-b="log-add" data-id="${esc(l.id)}">넣기</button></div>` : ''}</div>`;
  }
  function renderTable(){
    const ae = document.activeElement;
    if (ae && $('.bud-table', root).contains(ae) && ae.matches('input, select, textarea')) return;
    const ls = list().filter(match);
    /* 비어 있는 에듀파인 칸(세부사업·원가통계비목)은 숨겨요 */
    const showBiz = st.showAll || list().some(l => l.biz), showStat = st.showAll || list().some(l => l.stat);
    const nCol = 9 + (showBiz ? 1 : 0) + (showStat ? 1 : 0);
    const dis = can() ? '' : 'disabled';
    if (!ls.length){ $('.bud-table', root).innerHTML = `<p class="empty">${list().length ? '이 구분에 들어간 예산이 없어요.' : '아직 예산 줄이 없어요. "+ 예산 줄 추가"를 누르거나 에듀파인 표를 붙여 넣어 주세요.'}</p>`; return; }
    const tot = {cur:0, rest:0, req:0, spent:0};
    const body = ls.map(l => {
      const c = budCalc(l); tot.cur += c.cur; tot.rest += c.rest; tot.req += c.req; tot.spent += c.spent;
      const t = f => `<td ${f === 'memo' ? 'class="memo"' : ''}><input type="text" id="bf-${key}-${l.id}-${f}" data-id="${esc(l.id)}" data-f="${f}" value="${esc(l[f] || '')}" aria-label="${{act:'주요활동', biz:'세부사업', item:'세부항목', stat:'원가통계비목', memo:'메모'}[f]}" ${f === 'memo' ? 'placeholder="메모"' : ''} ${dis}></td>`;
      const canSplit = g && can() && l.scope === '학급' && !l.cls;
      const open = st.open.has(l.id);
      return `<tr class="${open ? 'opened' : ''}"><td><select id="bf-${key}-${l.id}-scope" data-id="${esc(l.id)}" data-f="scope" aria-label="구분" ${dis}>${scopeOpts(l)}</select></td>${t('act')}${showBiz ? t('biz') : ''}${t('item')}${showStat ? t('stat') : ''}${t('memo')}
        <td class="n"><input type="text" inputmode="numeric" class="amt" id="bf-${key}-${l.id}-amount" data-id="${esc(l.id)}" data-f="amount" value="${wonS(c.base)}" aria-label="처음 예산" ${dis}>${c.adj ? `<small class="adj">${c.adj > 0 ? '+' : '−'}${wonS(Math.abs(c.adj))} → ${wonS(c.cur)}</small>` : ''}</td>
        <td class="n rest ${c.rest < 0 ? 'neg' : ''}">${wonS(c.rest)}</td><td class="n">${wonS(c.req)}</td><td class="n">${wonS(c.spent)}</td>
        <td class="act"><button type="button" class="btn small ${open ? 'on' : ''}" data-b="open" data-id="${esc(l.id)}" aria-expanded="${open}">내역 ${(l.logs || []).length}${l.calc ? ' · 산출' : ''}</button>${canSplit ? `<button type="button" class="btn small" data-b="split" data-id="${esc(l.id)}" title="반마다 같은 금액으로 한 줄씩 나눠요">반마다</button>` : ''}${can() ? `<button type="button" class="x" data-b="del" data-id="${esc(l.id)}" aria-label="이 줄 지우기">×</button>` : ''}</td></tr>
        ${open ? `<tr class="logrow"><td colspan="${nCol}"><label class="f bud-calc" for="bf-${key}-${l.id}-calc">산출내역 <span class="hint">예: 기본 강사비 130,000원 × 3회 × 1학급</span><textarea id="bf-${key}-${l.id}-calc" data-id="${esc(l.id)}" data-f="calc" rows="2" ${dis}>${esc(l.calc || '')}</textarea></label>${logsHTML(l, c)}</td></tr>` : ''}`;
    }).join('');
    $('.bud-table', root).innerHTML = `<div class="tablewrap"><table class="bud"><thead><tr><th>구분</th><th>주요활동</th>${showBiz ? '<th>세부사업</th>' : ''}<th>세부항목</th>${showStat ? '<th>원가통계비목</th>' : ''}<th>메모</th><th>예산현액</th><th>예산잔액</th><th>요구금액</th><th>집행액</th><th></th></tr></thead>
      <tbody>${body}</tbody><tfoot><tr><td colspan="${nCol - 5}">합계 (${ls.length}줄)${!st.showAll && (!showBiz || !showStat) ? ` <button type="button" class="btn small" data-b="showall" style="margin-left:6px">에듀파인 칸 보이기</button>` : ''}</td><td class="n">${wonS(tot.cur)}</td><td class="n rest ${tot.rest < 0 ? 'neg' : ''}">${wonS(tot.rest)}</td><td class="n">${wonS(tot.req)}</td><td class="n">${wonS(tot.spent)}</td><td></td></tr></tfoot></table></div>`;
  }
  const wpath = () => g ? 'budgetwish/list' : `data/users/${S.uid}/budgetwish`;
  function listenWish(){
    if (st.wl || !S.db || (!g && !S.uid)) return;
    st.wl = S.db.doc(wpath()).onSnapshot(snap => { if (busy(wpath())) return; st.wish = snap.exists ? (snap.data().items || []) : []; renderWish(); }, () => {});
  }
  const lineName = l => [l.item, l.act, l.biz].filter(Boolean)[0] || '(이름 없는 줄)';
  function renderWish(){
    const w = st.wish || [], ls = list();
    const ae = document.activeElement; if (ae && $('.bud-wish', root).contains(ae) && ae.matches('input, select') && ae.closest('.wish-list')) return;
    const todo = w.filter(x => !x.done), done = w.filter(x => x.done).slice(-8).reverse();
    $('.wish-n', root).textContent = todo.length ? `${todo.length}개 · 예상 ${wonS(todo.reduce((a, x) => a + numIn(x.price), 0))}원` : '';
    const opts = sel => `<option value="">예산 줄 고르기</option>` + ls.map(l => `<option value="${esc(l.id)}" ${sel === l.id ? 'selected' : ''}>${esc(sVal(l))} · ${esc(lineName(l))}</option>`).join('');
    const ls0 = $(`#wi-${key}-l`); if (ls0 && !(ae === ls0)) ls0.innerHTML = opts(ls0.value);
    $('.wish-list', root).innerHTML = (todo.length ? todo.map(x => `<div class="wish"><span class="nm">${esc(x.name)}</span>
      <input type="text" inputmode="numeric" class="amt" id="wp-${key}-${x.id}" data-wish="${x.id}" data-wf="price" value="${x.price ? wonS(numIn(x.price)) : ''}" placeholder="금액" aria-label="${esc(x.name)} 금액">
      <select id="wl-${key}-${x.id}" data-wish="${x.id}" data-wf="line" aria-label="${esc(x.name)} 예산 줄">${opts(x.line)}</select>
      <button type="button" class="btn small primary" data-b="wish-buy" data-id="${x.id}" ${can() ? '' : 'disabled'}>샀어요</button><button type="button" class="x" data-b="wish-del" data-id="${x.id}" aria-label="빼기">×</button></div>`).join('') : '<p class="hint" style="margin:0">살 것을 적어 두면 잊지 않아요.</p>')
      + (done.length ? `<div class="wish-done">${done.map(x => `<span>✓ ${esc(x.name)}${x.price ? ' ' + wonS(numIn(x.price)) + '원' : ''}</span>`).join('')}</div>` : '');
  }
  function putWish(items){ st.wish = items; renderWish(); queueSet(wpath(), () => ({items:(st.wish || []).slice(-200), updatedAt:Date.now()}), g); }
  root.addEventListener('change', e => {
    const el = e.target.closest('[data-wish]'); if (!el) return;
    const items = (st.wish || []).map(x => x.id === el.dataset.wish ? Object.assign({}, x, {[el.dataset.wf]:el.dataset.wf === 'price' ? numIn(el.value) : el.value}) : x);
    putWish(items);
  });
  function render(){ if (!root.isConnected) return; listenWish(); renderSum(); renderTable(); renderWish(); $$('[data-b="add"], [data-b="import"], [data-b="wish-add"]', root).forEach(b => { b.disabled = !can(); }); }
  const lineOf = id => ((g ? S.budG : S.budM) || []).find(l => l.id === id);
  async function upd(id, data){ try { await col().doc(id).update(data); } catch (e){ err(e); } }
  root.addEventListener('change', e => {
    const el = e.target.closest('[data-f]'); if (!el || !can()) return;
    const f = el.dataset.f, id = el.dataset.id;
    if (f === 'scope') upd(id, scopeOf(el.value));
    else if (f === 'amount'){ const n = numIn(el.value); el.value = wonS(n); upd(id, {amount:n}); }
    else upd(id, {[f]:el.value.trim()});
  });
  root.addEventListener('focusout', () => setTimeout(() => { const ae = document.activeElement; if (!(ae && $('.bud-table', root).contains(ae) && ae.matches('input, select'))) renderTable(); }, 0));
  root.addEventListener('keydown', e => { if (e.key === 'Enter' && e.target.closest('.log-add')){ e.preventDefault(); const b = $('[data-b="log-add"]', e.target.closest('.log-add')); if (b) b.click(); } });
  root.addEventListener('click', async e => {
    const fb = e.target.closest('[data-filter]'); if (fb){ st.filter = fb.dataset.filter; render(); return; }
    const b = e.target.closest('[data-b]'); if (!b) return;
    const act = b.dataset.b, id = b.dataset.id;
    if (act === 'open'){ st.open.has(id) ? st.open.delete(id) : st.open.add(id); renderTable(); return; }
    if (act === 'showall'){ st.showAll = true; renderTable(); return; }
    if (act === 'csv'){
      const rows = [['구분', '주요활동', '세부사업', '세부항목', '원가통계비목', '메모', '예산현액', '예산잔액', '요구금액', '집행액', '산출내역']];
      const ls = list().filter(match);
      ls.forEach(l => { const c = budCalc(l); rows.push([sVal(l), l.act || '', l.biz || '', l.item || '', l.stat || '', l.memo || '', c.cur, c.rest, c.req, c.spent, l.calc || '']); });
      rows.push([]); rows.push(['내역', '세부항목', '날짜', '종류', '내용', '금액']);
      ls.forEach(l => (l.logs || []).forEach(x => rows.push(['', l.item || l.act || '', x.date || '', x.kind, x.text || '', (x.kind === '증액' ? 1 : -1) * numIn(x.amt)])));
      save(`${g ? '학년' : '우리반'}_예산_${ymd(today())}.csv`, csv(rows)); return;
    }
    if (!can()){ toast(g ? '학년 공간을 고칠 권한이 없어요.' : '로그인한 상태로 열어야 적을 수 있어요.'); return; }
    if (act === 'wish-add'){
      const n = $(`#wi-${key}-n`).value.trim(); if (!n){ toast('살 것을 적어 주세요.'); return; }
      putWish((st.wish || []).concat([{id:rid(), name:n.slice(0, 60), price:numIn($(`#wi-${key}-p`).value), line:$(`#wi-${key}-l`).value, at:Date.now(), by:S.uid}]));
      $(`#wi-${key}-n`).value = ''; $(`#wi-${key}-p`).value = ''; return;
    }
    if (act === 'split'){
      const l = lineOf(id); if (!l) return;
      if (!twoStep(b, `${nCls()}개 반으로 나눌까요?`)) return;
      try {
        for (let i = 1; i <= nCls(); i++){ const c = Object.assign({}, l); delete c.id; c.cls = i + '반'; c.logs = []; c.order = (l.order || l.createdAt || 0) + i / 100; c.createdAt = Date.now() + i; await col().add(c); }
        await col().doc(id).delete(); toast(`${l.item || l.act || '이 줄'}을(를) ${nCls()}개 반으로 나눴어요. 반마다 쓴 돈을 따로 적을 수 있어요.`);
      } catch (er){ err(er); }
      return;
    }
    if (act === 'wish-del'){ if (!twoStep(b, '빼기?')) return; putWish((st.wish || []).filter(x => x.id !== id)); return; }
    if (act === 'wish-buy'){
      const x = (st.wish || []).find(w => w.id === id); if (!x) return;
      const price = numIn(($(`#wp-${key}-${id}`) || {}).value), lineId = ($(`#wl-${key}-${id}`) || {}).value || x.line;
      if (lineId && price > 0){
        const l = lineOf(lineId);
        if (l){ await upd(lineId, {logs:(l.logs || []).concat([{id:rid(), date:ymd(today()), kind:'집행', text:x.name, amt:price, at:Date.now(), by:S.uid}])}); }
      }
      putWish((st.wish || []).map(w => w.id === id ? Object.assign({}, w, {done:true, price, line:lineId, doneAt:Date.now()}) : w));
      toast(lineId && price > 0 ? `${x.name} ${wonS(price)}원을 집행으로 적었어요.` : `${x.name}을(를) 산 것으로 표시했어요. 금액과 예산 줄을 고르면 잔액에서도 빠져요.`);
      return;
    }
    if (act === 'add'){
      const sc = st.filter === 'all' || st.filter === '학년' ? {scope:'학년', cls:null} : scopeOf(st.filter);
      try { await col().add(Object.assign({act:'', biz:'', item:'', stat:'', amount:0, logs:[], createdAt:Date.now(), createdBy:S.uid}, sc)); } catch (er){ err(er); }
    } else if (act === 'del'){
      if (!twoStep(b, '지울까요?')) return;
      try { await col().doc(id).delete(); st.open.delete(id); toast('예산 줄을 지웠어요.'); } catch (er){ err(er); }
    } else if (act === 'log-add'){
      const l = lineOf(id); if (!l) return;
      const p = `#bl-${key}-${id}-`;
      const amt = numIn($(p + 'a').value), text = $(p + 't').value.trim(), kind = $(p + 'k').value, date = $(p + 'd').value || ymd(today());
      if (!(amt > 0)){ toast('금액을 적어 주세요.'); $(p + 'a').focus(); return; }
      const logs = (l.logs || []).concat([{id:rid(), date, kind, text, amt, at:Date.now(), by:S.uid}]);
      b.blur(); await upd(id, {logs});
      const c = budCalc(Object.assign({}, l, {logs}));
      toast(`${kind === '증액' ? '+' : '−'}${wonS(amt)}원 → 남은 돈 ${wonS(c.rest)}원`);
    } else if (act === 'log-del' || act === 'settle'){
      const l = lineOf(id); if (!l) return;
      if (act === 'log-del' && !twoStep(b, '지울까요?')) return;
      const logs = act === 'log-del' ? (l.logs || []).filter(x => x.id !== b.dataset.log) : (l.logs || []).map(x => x.id === b.dataset.log ? Object.assign({}, x, {kind:'집행', settledAt:Date.now()}) : x);
      b.blur(); await upd(id, {logs});
    } else if (act === 'import'){
      const rows = pasteRows($(`#bud-${key}-paste`).value);
      if (!rows.length){ toast('붙여 넣은 표가 없어요.'); return; }
      let map = headerMap(rows[0], BUD_HDR), data = rows;
      if (map) data = rows.slice(1);
      const def = st.filter === 'all' ? {scope:'학년', cls:null} : scopeOf(st.filter);
      const items = [];
      data.forEach(r => {
        if (r.some(c => /^(합\s*계|소\s*계|총\s*계|계)$/.test(c))) return;
        let m = map;
        if (!m){ const lead = /^(학년|학급|\d{1,2}\s*반)$/.test(r[0] || ''); m = (lead ? ['scope'] : []).concat(BUD_POS); }
        const o = {}; m.forEach((f, i) => { if (f && r[i] !== undefined && r[i] !== '') o[f] = r[i]; });
        if (!o.act && !o.biz && !o.item && !o.stat && !numIn(o.amount)) return;
        let sc = def;
        if (o.scope){ const cm = o.scope.match(/(\d{1,2})\s*반/); sc = cm ? (g ? {scope:'학급', cls:`${+cm[1]}반`} : {scope:'학급', cls:null}) : /학급|반/.test(o.scope) ? {scope:'학급', cls:null} : {scope:'학년', cls:null}; }
        const amount = numIn(o.amount), req = numIn(o.req), logs = [], d = ymd(today());
        if (req > 0) logs.push({id:rid(), date:d, kind:'요구', text:'가져온 요구금액', amt:req, at:Date.now()});
        if (o.spent !== undefined && numIn(o.spent) > 0) logs.push({id:rid(), date:d, kind:'집행', text:'가져온 집행액', amt:numIn(o.spent), at:Date.now()});
        else if (o.rest !== undefined){ const used = amount - numIn(o.rest) - req; if (used > 0) logs.push({id:rid(), date:d, kind:'집행', text:'가져오기 전 집행액', amt:used, at:Date.now()}); else if (used < 0) logs.push({id:rid(), date:d, kind:'증액', text:'가져온 잔액에 맞춤', amt:-used, at:Date.now()}); }
        items.push(Object.assign({act:o.act || '', biz:o.biz || '', item:o.item || '', stat:o.stat || '', amount, logs, createdBy:S.uid}, sc));
      });
      if (!items.length){ $('.bud-info', root).textContent = '읽을 수 있는 줄이 없어요. 스프레드시트에서 칸째로 복사해 주세요.'; return; }
      b.disabled = true; let ok = 0; const t0 = Date.now();
      for (const it of items){ try { await col().add(Object.assign(it, {createdAt:t0 + ok, order:t0 + ok})); ok++; } catch (er){ err(er); break; } }
      b.disabled = false;
      if (ok){ $(`#bud-${key}-paste`).value = ''; $('.bud-info', root).textContent = ''; toast(`예산 ${ok}줄을 넣었어요.`); $('.bud-paste', root).open = false; }
    }
  });
  return {render};
}

/* ---------- 명부 ---------- */
const ROS_F = [['no', '번호'], ['name', '이름'], ['sex', '성별'], ['birth', '생년월일'], ['prev', '이전 학년반'], ['guardian', '보호자'], ['phone', '보호자 연락처'], ['addr', '주소'], ['note', '비고']];
const ROS_HDR = [[/^(출석\s*)?번호$|^번$|^No\.?$/i, 'no'], [/연락처|전화|휴대폰|핸드폰|폰/, 'phone', /학생|본인/], [/보호자|학부모|부모|관계/, 'guardian', /연락|전화|폰/], [/성명|이름|학생명|^학생$/, 'name'], [/성별/, 'sex'], [/생년월일|생일|출생/, 'birth'], [/이전|작년|전\s*학년|원\s*소속|구\s*반/, 'prev'], [/^(현재\s*)?반$|현재\s*반|새\s*반|배정\s*반|^학반$|^학년\s*반$/, 'cls'], [/주소/, 'addr'], [/비고|메모|특이/, 'note']];
const ROS_MAX = 6;
function normBirth(s){
  s = String(s || '').trim(); if (!s) return '';
  const d = s.replace(/\D/g, ''); let y, m, dd;
  const p = s.match(/(\d{2,4})\s*[.\-\/년]\s*(\d{1,2})\s*[.\-\/월]\s*(\d{1,2})/);
  if (p){ y = p[1]; m = p[2]; dd = p[3]; }
  else if (d.length === 8){ y = d.slice(0, 4); m = d.slice(4, 6); dd = d.slice(6); }
  else if (d.length === 6){ y = d.slice(0, 2); m = d.slice(2, 4); dd = d.slice(4); }
  else return s;
  if (y.length === 2) y = (+y > 50 ? '19' : '20') + y;
  return `${y}.${pad(+m)}.${pad(+dd)}`;
}
function normPhone(s){ s = String(s || '').trim(); const d = s.replace(/\D/g, ''); if (/^0\d{9,10}$/.test(d)) return d.length === 11 ? `${d.slice(0, 3)}-${d.slice(3, 7)}-${d.slice(7)}` : d.startsWith('02') ? `02-${d.slice(2, 6)}-${d.slice(6)}` : `${d.slice(0, 3)}-${d.slice(3, 6)}-${d.slice(6)}`; return s; }
const normSex = s => /^(남|남자|M|male)$/i.test(String(s).trim()) ? '남' : /^(여|여자|F|female)$/i.test(String(s).trim()) ? '여' : String(s || '').trim();
const clsNo = s => { s = clsCanon(s) || String(s || ''); const m = s.match(/(\d{1,2})\s*반/) || s.match(/\d+\s*[-–.]\s*(\d{1,2})\s*$/) || s.match(/^\s*(\d{1,2})\s*$/); return m ? +m[1] : null; };
function guessCell(o, c){
  const v = c.trim(); if (!v) return;
  if (o.no == null && /^\d{1,2}$/.test(v)) o.no = +v;
  else if (!o.sex && /^(남|여|남자|여자)$/.test(v)) o.sex = normSex(v);
  else if (!o.phone && /^0\d{1,2}[-.\s]?\d{3,4}[-.\s]?\d{4}$/.test(v)) o.phone = normPhone(v);
  else if (!o.birth && (/^(\d{2}|\d{4})[.\-\/]\s*\d{1,2}[.\-\/]\s*\d{1,2}\.?$/.test(v) || /^\d{6}$|^(19|20)\d{6}$/.test(v) || /\d{4}년\s*\d{1,2}월/.test(v))) o.birth = normBirth(v);
  else if (!o.prev && (/^\d\s*[-–]\s*\d{1,2}$/.test(v) || /\d\s*학년\s*\d{1,2}\s*반/.test(v) || /^\d{1,2}\s*반$/.test(v) || (o.name && /^[가-힣A-Za-z0-9\s]{1,12}반$/.test(v)))) o.prev = v;
  else if (!o.name && /^[가-힣]{2,5}$|^[A-Za-z][A-Za-z .'-]{1,30}$/.test(v)) o.name = v;
  else if (!o.guardian && /^[가-힣]{2,5}\s*\((부|모|조부|조모|보호자|어머니|아버지)\)$|^(어머니|아버지|엄마|아빠|부|모)\s*[가-힣]{2,5}$/.test(v)) o.guardian = v;
  else if (!o.prev && o.name && /^[가-힣]{1,8}$/.test(v) && !o.guardian) o.prev = v;
  else o.note = o.note ? o.note + ' ' + v : v;
}
function parseRosterPaste(text){
  const rows = pasteRows(text); if (!rows.length) return {list:[], extra:[], hasCls:false};
  const map = headerMap(rows[0], ROS_HDR);
  const extra = [];
  if (map) rows[0].forEach((h, i) => { if (!map[i] && h.trim()) extra.push(h.trim()); });
  const list = (map ? rows.slice(1) : rows).map(r => {
    const o = {};
    if (map) r.forEach((c, i) => {
      const f = map[i], v = (c || '').trim(); if (!v) return;
      if (!f){ const h = rows[0][i].trim(); if (h){ o.x = o.x || {}; o.x[h] = v; } return; }
      if (f === 'no'){ const n = parseInt(v, 10); if (isFinite(n)) o.no = n; }
      else if (f === 'birth') o.birth = normBirth(v);
      else if (f === 'phone') o.phone = normPhone(v);
      else if (f === 'sex') o.sex = normSex(v);
      else if (f === 'cls') o.cls = clsNo(v);
      else o[f] = v;
    });
    else r.forEach(c => guessCell(o, c));
    return o;
  }).filter(o => o.name || o.no != null);
  return {list, extra, hasCls:!!(map && map.includes('cls'))};
}
function mergeStudents(cur, inc, replace){
  const out = replace ? [] : cur.map(s => Object.assign({}, s, s.x ? {x:Object.assign({}, s.x)} : {}));
  inc.forEach(s0 => {
    const s = Object.assign({}, s0); delete s.cls;
    const hit = (s.no != null && out.find(o => o.no === s.no && (!s.name || !o.name || o.name === s.name))) || (s.name && out.find(o => o.name === s.name));
    if (hit){ Object.keys(s).forEach(k => { if (k === 'x') hit.x = Object.assign({}, hit.x || {}, s.x); else if (s[k] !== '' && s[k] != null) hit[k] = s[k]; }); }
    else out.push(Object.assign({id:rid()}, s));
  });
  return sortStu(out);
}
const sortStu = a => a.slice().sort((p, q) => (p.no ?? 999) - (q.no ?? 999) || String(p.name || '').localeCompare(String(q.name || ''), 'ko'));
const ROS_SIG_F = ['no', 'name', 'sex', 'birth', 'prev', 'guardian', 'phone', 'addr', 'note'];
function rosterSig(list){ return JSON.stringify(sortStu(list || []).map(s => ROS_SIG_F.map(f => s[f] ?? '').concat([JSON.stringify(s.x || {})]))); }
function gradeClass(n){ const d = (S.rosG || {})['c' + n] || {}; return {students:d.students || [], extra:d.extra || []}; }
const stripId = l => (l || []).map(s => { const o = JSON.parse(JSON.stringify(s)); delete o.id; return o; });
function rosterGradeToMine(n){
  if (!n || !S.uid) return;
  const src = gradeClass(n), old = S.profile.roster || [];
  S.profile.roster = sortStu(stripId(src.students).map(s => { const o = old.find(x => x.no === s.no && (!s.name || !x.name || x.name === s.name)); return Object.assign({id:o && o.id || rid()}, s); }));
  S.profile.rosterExtra = [...new Set((S.profile.rosterExtra || []).concat(src.extra))];
  saveProfile(); renderHeader();
}
function rosterMineToGrade(n){
  if (!n || !S.canWrite || !S.db) return;
  const ex = [...new Set(gradeClass(n).extra.concat(S.profile.rosterExtra || []))];
  const list = sortStu(stripId(S.profile.roster || []).map(s => Object.assign({id:rid()}, s)));
  S.rosG = S.rosG || {}; S.rosG['c' + n] = {id:'c' + n, students:list, extra:ex, updatedAt:Date.now()};
  queueSet('roster/c' + n, () => ({students:S.rosG['c' + n].students, extra:S.rosG['c' + n].extra, cls:n, updatedAt:Date.now(), updatedBy:S.uid}), true);
}
let rosSyncT;
function rosterAutoSync(from){
  if (S.arc || !S.profile.rosterSync) return;
  const n = clsNo(S.profile.myClass); if (!n) return;
  clearTimeout(rosSyncT);
  rosSyncT = setTimeout(() => {
    if (rosterSig(S.profile.roster || []) === rosterSig(gradeClass(n).students)) return;
    if (from === 'mine') rosterMineToGrade(n); else rosterGradeToMine(n);
    if (ROS.g) ROS.g.render(); if (ROS.m) ROS.m.render();
  }, 800);
}
function makeRoster(key){
  const g = key === 'g';
  const st = {cls:null};
  const root = $('#ros-' + key);
  const nCls = () => Math.max(1, Math.min(ROS_MAX, +S.settings.classCount || 4));
  const curCls = () => { if (!st.cls){ const m = clsNo(S.profile.myClass); st.cls = m && m <= nCls() ? m : 1; } return Math.min(st.cls, nCls()); };
  const path = n => 'roster/c' + n;
  const get = n => {
    if (g){ const d = (S.rosG || {})['c' + (n || curCls())] || {}; const st0 = (d.students || []).map(s => Object.assign({}, s)); st0.forEach(s => { if (!s.id) s.id = 'k' + (s.no ?? '') + (s.name || ''); }); return {students:st0, extra:(d.extra || []).slice()}; }
    const r = S.profile.roster || []; r.forEach(s => { if (!s.id) s.id = rid(); });
    return {students:r, extra:S.profile.rosterExtra || []};
  };
  const can = () => !!S.db && (g ? S.canWrite : !!S.uid);
  function put(data, n){
    data.students = sortStu(data.students);
    if (g){
      n = n || curCls();
      S.rosG = S.rosG || {}; S.rosG['c' + n] = Object.assign({id:'c' + n}, data, {updatedAt:Date.now()});
      queueSet(path(n), () => ({students:S.rosG['c' + n].students, extra:S.rosG['c' + n].extra || [], cls:n, updatedAt:Date.now(), updatedBy:S.uid}), true);
      if (n === clsNo(S.profile.myClass)) rosterAutoSync('grade');
    } else {
      S.profile.roster = data.students; S.profile.rosterExtra = data.extra;
      saveProfile(); renderHeader();
      rosterAutoSync('mine');
    }
  }
  root.innerHTML = `${g ? `<div class="ros-cls seg" role="group" aria-label="반 고르기"></div>` : ''}
    <div class="ros-bar"><span class="ros-count hint"></span><span class="grow"></span>
      ${g ? '' : '<button type="button" class="btn small" data-b="from-grade">학년 명부에서 우리 반 가져오기</button>'}
      <button type="button" class="btn small primary" data-b="add">+ 학생 추가</button>
      <button type="button" class="btn small" data-b="csv">${g ? '이 반 CSV' : 'CSV로 받기'}</button>${g ? '<button type="button" class="btn small" data-b="csv-all">학년 전체 CSV</button>' : ''}</div>
    <details class="ros-paste"><summary>스프레드시트에서 붙여넣기</summary>
      <p class="hint">나이스·스프레드시트에서 제목 줄까지 칸째로 복사해 붙이면 번호·이름·성별·생년월일·이전 학년반·보호자·보호자 연락처·주소·비고 칸을 알아서 찾고, 처음 보는 제목은 새 열로 만들어요.${g ? ' <b>"반" 또는 "현재 반" 칸이 있으면 반별로 알아서 나눠 넣어요</b> (최대 6반). 없으면 지금 고른 반에 들어가요.' : ''} 제목 없이 붙여도 번호·이름·성별·날짜·전화번호 모양을 보고 칸을 맞춰요.</p>
      <textarea rows="6" id="ros-${key}-paste" aria-label="붙여넣을 명부" placeholder="여기에 Ctrl+V"></textarea>
      <div class="row"><label class="hint row" style="gap:4px"><input type="radio" name="ros-${key}-mode" value="merge" checked> 번호·이름이 같으면 고치고, 없으면 더하기</label>
        <label class="hint row" style="gap:4px"><input type="radio" name="ros-${key}-mode" value="replace"> ${g ? '들어가는 반의 명부를 새로 바꾸기' : '명부를 새로 바꾸기'}</label>
        <span class="grow"></span><button type="button" class="btn small primary" data-b="import">명부에 넣기</button></div>
      <p class="hint ros-info"></p>
    </details>
    <p class="hint ros-selinfo" style="margin:0;min-height:1em"></p>
    <div class="ros-table"></div>
    <p class="hint" style="margin:0">스프레드시트처럼 끌어서 여러 칸을 고르고 Ctrl+C로 복사, 칸에서 Ctrl+V로 여러 줄을 한 번에 붙여요. 제목 칸을 누르면 열 전체, 칸 안에서 Ctrl+A를 두 번 누르면 표 전체를 골라요.</p>
    <div class="row ros-extra-add"><input type="text" id="ros-${key}-newcol" placeholder="열 더하기 (예: 방과후, 알레르기)" style="max-width:240px" aria-label="새 열 이름"><button type="button" class="btn small" data-b="addcol">열 추가</button></div>
    <p class="privacy">${g ? '학년 명부는 학년 공간을 열 수 있는 선생님 모두가 보고 고칠 수 있어요. ' : '나만 보는 기록이에요. '}보호자 연락처·주소 같은 개인정보는 학교의 개인정보 보호 기준에 맞는지 먼저 확인하고 넣어 주세요. 필요 없는 칸은 비워 두면 돼요.</p>`;
  function render(){
    if (!root.isConnected) return;
    if (g){
      $('.ros-cls', root).innerHTML = Array.from({length:nCls()}, (_, i) => { const n = i + 1, c = (((S.rosG || {})['c' + n] || {}).students || []).length; return `<button type="button" data-cls="${n}" aria-pressed="${curCls() === n}">${esc(clsLabel(n + '반'))} <small>${c}명</small></button>`; }).join('');
    }
    const {students, extra} = get();
    const m = students.filter(s => s.sex === '남').length, f = students.filter(s => s.sex === '여').length;
    $('.ros-count', root).textContent = `${g ? clsLabel(curCls() + '반') + ' · ' : ''}${students.length}명${m || f ? ` (남 ${m} · 여 ${f})` : ''}`;
    $$('[data-b="add"], [data-b="import"], [data-b="addcol"], [data-b="from-grade"]', root).forEach(b => { b.disabled = !can(); });
    const wrong = students.filter(s => s.guardian && !s.prev && /반$|^\d\s*[-–]\s*\d{1,2}$/.test(String(s.guardian).trim()));
    let fixBar = $('.ros-fix', root);
    if (!fixBar){ fixBar = document.createElement('div'); fixBar.className = 'relink ros-fix'; $('.ros-table', root).before(fixBar); }
    fixBar.hidden = !(wrong.length && can());
    if (wrong.length) fixBar.innerHTML = `<span>보호자 칸에 반 이름처럼 보이는 값이 ${wrong.length}명 있어요 (예: ${esc(wrong[0].guardian)}).</span><button type="button" class="btn small primary" data-b="fix-prev">이전 학년반 칸으로 옮기기</button>`;
    const ae = document.activeElement;
    if (ae && $('.ros-table', root).contains(ae) && ae.matches('input')) return;
    const dis = can() ? '' : 'disabled';
    const head = ROS_F.map(([, n], c) => `<th data-col="${c}" title="눌러서 열 전체 고르기">${n}</th>`).join('') + extra.map((n, i) => `<th class="ex" data-col="${ROS_F.length + i}">${esc(n)}${can() ? `<button type="button" class="x" data-b="delcol" data-col="${i}" aria-label="${esc(n)} 열 지우기">×</button>` : ''}</th>`).join('');
    const cell = (s, f, v, cls, r, c) => `<td class="${cls || ''}" data-r="${r}" data-c="${c}"><input type="text" id="rf-${key}-${s.id}-${f}" data-id="${esc(s.id)}" data-f="${esc(f)}" data-r="${r}" data-c="${c}" value="${esc(v ?? '')}" aria-label="${esc(s.name || s.no || '')} ${esc(f)}" autocomplete="off" ${dis}></td>`;
    const body = students.map((s, r) => `<tr>${ROS_F.map(([f], c) => cell(s, f, s[f], 'f-' + f, r, c)).join('')}${extra.map((n, j) => cell(s, 'x:' + n, (s.x || {})[n], '', r, ROS_F.length + j)).join('')}<td class="act">${can() ? `<button type="button" class="x" data-b="del" data-id="${esc(s.id)}" aria-label="학생 지우기">×</button>` : ''}</td></tr>`).join('');
    st.rows = students.length; st.cols = ROS_F.length + extra.length;
    $('.ros-table', root).innerHTML = students.length ? `<div class="tablewrap"><table class="ros"><thead><tr>${head}<th></th></tr></thead><tbody>${body}</tbody></table></div>`
      : `<p class="empty">${g ? clsLabel(curCls() + '반') + ' 명부가 비어 있어요. ' : '아직 명부가 없어요. '}스프레드시트에서 복사해 "붙여넣기"에 넣거나 "+ 학생 추가"를 눌러 주세요.</p>`;
    paint(); renderSyncBar();
  }
  /* ---- 우리 반 명부 ↔ 학년 명부 ---- */
  function renderSyncBar(){
    let bar = $('.ros-sync', root);
    if (!bar){ bar = document.createElement('div'); bar.className = 'ros-sync'; $('.ros-bar', root).after(bar); }
    const my = clsNo(S.profile.myClass);
    if (g && curCls() !== my){ bar.hidden = true; return; }
    bar.hidden = false;
    if (!my){ bar.innerHTML = `<span class="hint">${g ? '' : '"내가 맡은 반"을 고르면 학년 명부의 우리 반과 이어져요.'}</span>`; bar.hidden = g; return; }
    const same = rosterSig(S.profile.roster || []) === rosterSig(gradeClass(my).students);
    const auto = !!S.profile.rosterSync;
    bar.innerHTML = `<span class="st ${same ? 'ok' : 'diff'}">${same ? `✓ 학년 명부 ${my}반과 같아요` : `학년 명부 ${my}반과 달라요`}</span>
      ${same ? '' : `<button type="button" class="btn small" data-b="sync-pull">${g ? '내 우리 반 명부 → 여기로' : '학년 명부 → 내 명부로'}</button><button type="button" class="btn small" data-b="sync-push">${g ? '여기 → 내 우리 반 명부로' : '내 명부 → 학년 명부로'}</button>`}
      <label class="hint row" style="gap:4px"><input type="checkbox" data-b="sync-auto" ${auto ? 'checked' : ''} ${S.uid ? '' : 'disabled'}> 한쪽을 고치면 다른 쪽도 저절로 맞추기</label>`;
  }
  root.addEventListener('change', e => {
    if (e.target.matches('[data-b="sync-auto"]')){ S.profile.rosterSync = e.target.checked; saveProfile(); if (e.target.checked) rosterAutoSync(g ? 'grade' : 'mine'); toast(e.target.checked ? '이제 한쪽을 고치면 다른 쪽도 맞춰져요.' : '자동 맞추기를 껐어요.'); ROS.g.render(); ROS.m.render(); return; }
    const el = e.target.closest('[data-f]'); if (!el || !can()) return;
    const data = get(); const s = data.students.find(x => x.id === el.dataset.id); if (!s) return;
    let f = el.dataset.f, v = el.value.trim();
    if (f.startsWith('x:')){ s.x = Object.assign({}, s.x || {}); if (v) s.x[f.slice(2)] = v; else delete s.x[f.slice(2)]; }
    else {
      if (f === 'no'){ const n = parseInt(v, 10); v = isFinite(n) ? n : null; if (!g && v != null && data.students.some(x => x !== s && x.no === v)){ toast(`${v}번이 이미 있어요.`); el.value = s.no ?? ''; return; } }
      if (f === 'birth') v = normBirth(v); if (f === 'phone') v = normPhone(v); if (f === 'sex') v = normSex(v);
      if (v === '' || v == null) delete s[f]; else s[f] = v;
      if (typeof v === 'string') el.value = v;
    }
    put(data);
  });
  root.addEventListener('focusout', () => setTimeout(() => { const ae = document.activeElement; if (!(ae && $('.ros-table', root).contains(ae) && ae.matches('input'))) render(); }, 0));
  root.addEventListener('click', async e => {
    const cb = e.target.closest('[data-cls]'); if (cb){ st.cls = +cb.dataset.cls; render(); return; }
    const b = e.target.closest('[data-b]'); if (!b) return;
    const act = b.dataset.b;
    const fields = extra => [...ROS_F.map(([f, n]) => [f, n]), ...extra.map(n => ['x:' + n, n])];
    const rowOf = (s, extra) => fields(extra).map(([f]) => f.startsWith('x:') ? (s.x || {})[f.slice(2)] || '' : s[f] ?? '');
    if (act === 'csv'){ const d = get(); save(`${g ? (S.settings.gradeName || '') + ' ' + clsLabel(curCls() + '반') : '우리반'}_명부.csv`, csv([fields(d.extra).map(x => x[1]), ...d.students.map(s => rowOf(s, d.extra))])); return; }
    if (act === 'csv-all'){
      const ex = [...new Set(Array.from({length:nCls()}, (_, i) => get(i + 1).extra).flat())];
      const rows = [['반', ...fields(ex).map(x => x[1])]];
      for (let n = 1; n <= nCls(); n++) get(n).students.forEach(s => rows.push([clsLabel(n + '반'), ...rowOf(s, ex)]));
      save(`${S.settings.gradeName || ''}_학년명부.csv`, csv(rows)); return;
    }
    if (!can()){ toast(g ? '학년 공간을 고칠 권한이 없어요.' : '로그인한 상태로 열어야 적을 수 있어요.'); return; }
    if (act === 'add'){
      const d = get(); const no = d.students.reduce((a, s) => Math.max(a, +s.no || 0), 0) + 1;
      const s = {id:rid(), no}; d.students.push(s); put(d); render();
      setTimeout(() => { const el = $(`#rf-${key}-${s.id}-name`); if (el) el.focus(); }, 30);
    } else if (act === 'del'){
      if (!twoStep(b, '지울까요?')) return;
      const d = get(); d.students = d.students.filter(s => s.id !== b.dataset.id); put(d); render();
    } else if (act === 'addcol'){
      const inp = $(`#ros-${key}-newcol`), n = inp.value.trim();
      if (!n){ toast('열 이름을 적어 주세요.'); inp.focus(); return; }
      const d = get(); if (d.extra.includes(n) || ROS_F.some(x => x[1] === n)){ toast('이미 있는 열이에요.'); return; }
      d.extra = d.extra.concat([n]); inp.value = ''; put(d); render();
    } else if (act === 'delcol'){
      if (!twoStep(b, '지울까요?')) return;
      const d = get(); const n = d.extra[+b.dataset.col]; d.extra = d.extra.filter((_, i) => i !== +b.dataset.col);
      d.students.forEach(s => { if (s.x) { s.x = Object.assign({}, s.x); delete s.x[n]; } }); put(d); render();
    } else if (act === 'sync-pull' || act === 'sync-push'){
      const toMine = g ? act === 'sync-push' : act === 'sync-pull';
      const my = clsNo(S.profile.myClass);
      if (toMine) rosterGradeToMine(my); else if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; } else rosterMineToGrade(my);
      toast(toMine ? '학년 명부 내용으로 내 우리 반 명부를 맞췄어요.' : `내 명부 내용으로 학년 명부 ${my}반을 맞췄어요.`);
      ROS.g.render(); ROS.m.render(); renderRosterQuick();
    } else if (act === 'fix-prev'){
      const d = get(); let n = 0;
      d.students.forEach(s => { if (s.guardian && !s.prev && /반$|^\d\s*[-–]\s*\d{1,2}$/.test(String(s.guardian).trim())){ s.prev = s.guardian; delete s.guardian; n++; } });
      put(d); render(); toast(`${n}명의 이전 학년반을 옮겼어요.`);
    } else if (act === 'from-grade'){
      const n = clsNo(S.profile.myClass);
      if (!n){ toast('먼저 "내가 맡은 반"을 골라 주세요.'); return; }
      const src = (((S.rosG || {})['c' + n] || {}).students) || [];
      if (!src.length){ toast(`학년 명부에 ${n}반 명단이 아직 없어요.`); return; }
      const d = get(); const gx = ((S.rosG || {})['c' + n] || {}).extra || [];
      d.students = mergeStudents(d.students, src.map(s => { const o = Object.assign({}, s); delete o.id; return o; }), false);
      d.extra = [...new Set(d.extra.concat(gx))]; put(d); render(); renderRosterQuick();
      toast(`학년 명부의 ${n}반 ${src.length}명을 가져왔어요.`);
    } else if (act === 'import'){
      const {list, extra, hasCls} = parseRosterPaste($(`#ros-${key}-paste`).value);
      if (!list.length){ $('.ros-info', root).textContent = '학생을 찾지 못했어요. 이름이나 번호가 있는 칸을 복사해 주세요.'; return; }
      const replace = $(`input[name="ros-${key}-mode"]:checked`, root).value === 'replace';
      const groups = {}; let skipped = 0;
      list.forEach(s => {
        let n = g ? (hasCls && s.cls ? s.cls : curCls()) : 0;
        if (g && (n < 1 || n > nCls())){ skipped++; return; }
        (groups[n] = groups[n] || []).push(s);
      });
      const done = [];
      Object.keys(groups).forEach(k => {
        const n = +k || undefined, d = get(n);
        d.students = mergeStudents(d.students, groups[k], replace); d.extra = [...new Set(d.extra.concat(extra))];
        put(d, n); done.push(g ? `${k}반 ${groups[k].length}명` : `${groups[k].length}명`);
      });
      $(`#ros-${key}-paste`).value = '';
      $('.ros-info', root).textContent = `${done.join(', ')}을 넣었어요.${skipped ? ` 반을 알 수 없거나 ${nCls()}반을 넘는 ${skipped}명은 뺐어요.` : ''}`;
      toast('명부에 넣었어요.'); render(); if (!g) renderRosterQuick();
    }
  });
  /* ---- 표처럼 여러 칸 고르기 · 복사 · 붙여넣기 ---- */
  st.sel = null; st.anchor = null; st.drag = false;
  const fieldAt = c => { const ex = get().extra; return c < ROS_F.length ? ROS_F[c][0] : 'x:' + ex[c - ROS_F.length]; };
  const rect = () => { const s0 = st.sel; return s0 ? {r0:Math.min(s0.r0, s0.r1), r1:Math.max(s0.r0, s0.r1), c0:Math.min(s0.c0, s0.c1), c1:Math.max(s0.c0, s0.c1)} : null; };
  const multi = () => { const q = rect(); return q && (q.r0 !== q.r1 || q.c0 !== q.c1); };
  function paint(){
    const q = rect(), m = multi();
    $$('.ros-table td[data-r]', root).forEach(td => { const r = +td.dataset.r, c = +td.dataset.c; td.classList.toggle('sel', !!(m && q && r >= q.r0 && r <= q.r1 && c >= q.c0 && c <= q.c1)); });
    const t = $('.ros-table table', root); if (t) t.classList.toggle('multi', !!m);
    const info = $('.ros-selinfo', root);
    if (info) info.textContent = m ? `${q.r1 - q.r0 + 1}줄 × ${q.c1 - q.c0 + 1}칸 골랐어요 · Ctrl+C 복사 · Delete 지우기 · Esc 풀기` : '';
  }
  const cellOf = el => { const td = el && el.closest && el.closest('td[data-r]'); return td && $('.ros-table', root).contains(td) ? {r:+td.dataset.r, c:+td.dataset.c} : null; };
  const focusCell = (r, c) => { const i = $(`.ros-table input[data-r="${r}"][data-c="${c}"]`, root); if (i){ i.focus(); i.select(); } };
  function setSel(r0, c0, r1, c1){ st.sel = {r0, c0, r1, c1}; paint(); }
  function selText(){
    const q = rect(), d = get(), out = [];
    for (let r = q.r0; r <= q.r1; r++){ const s0 = d.students[r]; if (!s0) continue; const row = []; for (let c = q.c0; c <= q.c1; c++){ const f = fieldAt(c); row.push(String((f.startsWith('x:') ? (s0.x || {})[f.slice(2)] : s0[f]) ?? '')); } out.push(row.join('\t')); }
    return out.join('\n');
  }
  function setVal(s0, f, v){
    v = String(v ?? '').trim();
    if (f.startsWith('x:')){ s0.x = Object.assign({}, s0.x || {}); if (v) s0.x[f.slice(2)] = v; else delete s0.x[f.slice(2)]; return; }
    if (f === 'no'){ const n = parseInt(v, 10); v = isFinite(n) ? n : ''; }
    else if (f === 'birth') v = normBirth(v); else if (f === 'phone') v = normPhone(v); else if (f === 'sex') v = normSex(v);
    if (v === '' || v == null) delete s0[f]; else s0[f] = v;
  }
  const tbl = () => $('.ros-table', root);
  root.addEventListener('mousedown', e => {
    const th = e.target.closest('.ros-table th[data-col]');
    if (th && !e.target.closest('button')){ const c = +th.dataset.col; if (e.shiftKey && st.sel) setSel(0, st.sel.c0, st.rows - 1, c); else setSel(0, c, st.rows - 1, c); st.anchor = {r:0, c}; e.preventDefault(); return; }
    const p = cellOf(e.target); if (!p || e.button !== 0) return;
    if (e.shiftKey && st.anchor){ setSel(st.anchor.r, st.anchor.c, p.r, p.c); e.preventDefault(); return; }
    st.anchor = p; st.drag = true; setSel(p.r, p.c, p.r, p.c);
  });
  root.addEventListener('mouseover', e => {
    if (!st.drag) return; const p = cellOf(e.target); if (!p) return;
    if (p.r !== st.anchor.r || p.c !== st.anchor.c){ setSel(st.anchor.r, st.anchor.c, p.r, p.c); if (document.activeElement && document.activeElement.blur && tbl().contains(document.activeElement)) { st.hold = document.activeElement; } window.getSelection && window.getSelection().removeAllRanges(); }
  });
  /* 끌어서 고를 때 화면 위·아래 끝에 가까이 가면 저절로 스크롤해요 */
  let asPos = null, asRaf = 0;
  const asStep = () => {
    asRaf = 0; if (!st.drag || !asPos) return;
    const box = tbl(), inner = box && box.scrollHeight > box.clientHeight + 4 ? box : null;
    const top = inner ? inner.getBoundingClientRect().top : 0, bot = inner ? inner.getBoundingClientRect().bottom : window.innerHeight;
    const zone = 60; let dy = 0;
    if (asPos.y < top + zone) dy = -Math.ceil((top + zone - asPos.y) / 3);
    else if (asPos.y > bot - zone) dy = Math.ceil((asPos.y - (bot - zone)) / 3);
    if (!dy) return;
    dy = Math.max(-40, Math.min(40, dy));
    if (inner) inner.scrollTop += dy; else window.scrollBy(0, dy);
    const p = cellOf(document.elementFromPoint(asPos.x, Math.max(top + 2, Math.min(bot - 2, asPos.y))));
    if (p && (p.r !== (st.sel || {}).r1 || p.c !== (st.sel || {}).c1)) setSel(st.anchor.r, st.anchor.c, p.r, p.c);
    asRaf = requestAnimationFrame(asStep);
  };
  document.addEventListener('mousemove', e => { if (!st.drag) return; asPos = {x:e.clientX, y:e.clientY}; if (!asRaf) asRaf = requestAnimationFrame(asStep); });
  document.addEventListener('mouseup', () => { asPos = null; if (asRaf){ cancelAnimationFrame(asRaf); asRaf = 0; } if (st.drag){ st.drag = false; if (multi() && st.hold){ st.hold.focus({preventScroll:true}); try { st.hold.setSelectionRange(0, 0); } catch (x){} } st.hold = null; } });
  root.addEventListener('keydown', e => {
    const p = cellOf(e.target); if (!p) return;
    const inp = e.target, len = (inp.value || '').length;
    const atStart = inp.selectionStart === 0 && inp.selectionEnd === 0, atEnd = inp.selectionStart === len;
    const mv = {ArrowUp:[-1, 0], ArrowDown:[1, 0], Enter:[1, 0]}[e.key] || (e.key === 'ArrowLeft' && (atStart || multi() || e.shiftKey) ? [0, -1] : e.key === 'ArrowRight' && (atEnd || multi() || e.shiftKey) ? [0, 1] : null);
    if (e.key === 'Escape' && multi()){ setSel(p.r, p.c, p.r, p.c); return; }
    if ((e.ctrlKey || e.metaKey) && (e.key === 'a' || e.key === 'A') && (!len || inp.selectionEnd - inp.selectionStart >= len)){ e.preventDefault(); st.anchor = {r:0, c:0}; setSel(0, 0, st.rows - 1, st.cols - 1); return; }
    if ((e.key === 'Delete' || e.key === 'Backspace') && multi()){
      e.preventDefault(); if (!can()) return;
      const q = rect(), d = get();
      for (let r = q.r0; r <= q.r1; r++){ const s0 = d.students[r]; if (!s0) continue; for (let c = q.c0; c <= q.c1; c++) if (fieldAt(c) !== 'no') setVal(s0, fieldAt(c), ''); }
      put(d); document.activeElement.blur(); render(); toast('고른 칸을 비웠어요. 번호 칸은 그대로 둬요.'); return;
    }
    if (!mv) return;
    e.preventDefault();
    const cur = e.shiftKey && st.sel ? {r:st.sel.r1, c:st.sel.c1} : p;
    const nr = Math.max(0, Math.min(st.rows - 1, cur.r + mv[0])), nc = Math.max(0, Math.min(st.cols - 1, cur.c + mv[1]));
    if (e.shiftKey && e.key !== 'Enter'){ if (!st.sel) st.anchor = p; setSel(st.anchor ? st.anchor.r : p.r, st.anchor ? st.anchor.c : p.c, nr, nc); return; }
    st.anchor = {r:nr, c:nc}; setSel(nr, nc, nr, nc); focusCell(nr, nc);
  });
  document.addEventListener('copy', e => {
    if (!multi() || !tbl().contains(document.activeElement || document.body) && !$('.ros-table table.multi', root)) return;
    if (!root.isConnected || root.closest('[hidden]')) return;
    e.preventDefault(); e.clipboardData.setData('text/plain', selText()); toast('고른 칸을 복사했어요. 스프레드시트에 바로 붙여 넣을 수 있어요.');
  });
  root.addEventListener('paste', e => {
    const p = cellOf(e.target); if (!p || !can()) return;
    const text = (e.clipboardData || window.clipboardData).getData('text');
    if (!/[\t\n]/.test(text.replace(/\n$/, ''))) return;
    e.preventDefault();
    const rows = pasteRows(text);
    const q = multi() ? rect() : {r0:p.r, c0:p.c};
    const d = get(); let added = 0;
    rows.forEach((cells, i) => {
      const r = q.r0 + i;
      let s0 = d.students[r];
      if (!s0){ s0 = {id:rid(), no:d.students.reduce((m, x) => Math.max(m, +x.no || 0), 0) + 1}; d.students.push(s0); added++; }
      cells.forEach((v, j) => { const c = q.c0 + j; if (c < st.cols) setVal(s0, fieldAt(c), v); });
      if (s0.no == null && !s0.name) { /* 빈 줄 */ }
    });
    d.students = d.students.filter(s0 => s0.no != null || s0.name || Object.keys(s0).length > 1);
    put(d); document.activeElement.blur(); render();
    setSel(q.r0, q.c0, q.r0 + rows.length - 1, q.c0 + Math.max(...rows.map(r => r.length)) - 1);
    toast(`${rows.length}줄을 붙여 넣었어요.${added ? ` 새 학생 ${added}명이 생겼어요.` : ''}`);
  });
  return {render};
}

/* ================= 평가 계획 · 묶음 평균 ================= */
const PLAN_HDR = [[/과목|교과/, 'subj'], [/영역|단원/, 'area'], [/성취\s*기준/, 'std'], [/평가\s*(내용|요소|과제|문항)|^내용$/, 'content'], [/방법|유형/, 'method'], [/시기|일자|날짜|평가일|^월$|일정/, 'when']];
const PLAN = {rows:[]};
function syStart(){ const d = today(); return d.getMonth() >= 2 ? d.getFullYear() : d.getFullYear() - 1; }
function whenToDate(t){
  t = String(t || '');
  let m = t.match(/(\d{4})\s*[.\-\/년]\s*(\d{1,2})\s*[.\-\/월]\s*(\d{1,2})/);
  if (m) return `${m[1]}-${pad(+m[2])}-${pad(+m[3])}`;
  m = t.match(/(\d{1,2})\s*[.\/월]\s*(\d{1,2})\s*일?/);
  if (m && +m[1] >= 1 && +m[1] <= 12 && +m[2] <= 31){ const mo = +m[1], y = mo >= 3 ? syStart() : syStart() + 1; return `${y}-${pad(mo)}-${pad(+m[2])}`; }
  return '';
}
function parsePlan(text){
  const rows = pasteRows(text); if (!rows.length) return [];
  const map = headerMap(rows[0], PLAN_HDR);
  const data = map ? rows.slice(1) : rows;
  const m = map || ['subj', 'area', 'content', 'when'];
  let last = {};
  return data.map(r => {
    const o = {}; m.forEach((f, i) => { if (f && r[i]) o[f] = (o[f] ? o[f] + ' ' : '') + r[i].trim(); });
    ['subj', 'area'].forEach(f => { if (!o[f] && last[f]) o[f] = last[f]; });
    if (o.subj) last.subj = o.subj; if (o.area) last.area = o.area;
    const content = o.content || o.std || '';
    if (!content && !o.area) return null;
    return {on:true, subj:o.subj || '', area:o.area || '', content, method:o.method || '', when:o.when || '', date:whenToDate(o.when)};
  }).filter(Boolean);
}
function renderPlanPreview(){
  const r = PLAN.rows;
  $('#pl-count').textContent = r.length ? `${r.length}개 찾음 · ${r.filter(x => x.on).length}개 고름` : '';
  $('#pl-add').disabled = !r.some(x => x.on);
  $('#pl-list').innerHTML = r.length ? `<div class="tablewrap"><table class="ex"><thead><tr><th></th><th>과목</th><th>영역</th><th>평가 내용</th><th>평가일</th></tr></thead><tbody>${r.map((x, i) => `<tr class="${x.on ? '' : 'off'}">
    <td><input type="checkbox" id="pp-on-${i}" data-pp="${i}" data-f="on" ${x.on ? 'checked' : ''} aria-label="${i + 1}번째 넣기"></td>
    <td><input type="text" id="pp-s-${i}" data-pp="${i}" data-f="subj" value="${esc(x.subj)}" style="min-width:60px"></td>
    <td><input type="text" id="pp-a-${i}" data-pp="${i}" data-f="area" value="${esc(x.area)}"></td>
    <td><input type="text" id="pp-c-${i}" data-pp="${i}" data-f="content" value="${esc(x.content)}"></td>
    <td><input type="date" id="pp-d-${i}" data-pp="${i}" data-f="date" value="${x.date}">${x.when && !x.date ? `<span class="src">${esc(x.when)}</span>` : ''}</td></tr>`).join('')}</tbody></table></div>` : '';
}
$('#pl-run').onclick = () => { PLAN.rows = parsePlan($('#pl-text').value); $('#pl-info').textContent = PLAN.rows.length ? '과목·내용·평가일을 고치고, 넣지 않을 줄은 체크를 풀어 주세요. 평가일은 시기에 날짜가 있을 때만 채워져요.' : '평가 내용을 찾지 못했어요. 평가 계획표의 제목 줄(과목·영역·평가 내용·시기)까지 함께 복사해 주세요.'; renderPlanPreview(); };
$('#pl-list').addEventListener('change', e => { const el = e.target.closest('[data-pp]'); if (!el) return; const x = PLAN.rows[+el.dataset.pp]; x[el.dataset.f] = el.dataset.f === 'on' ? el.checked : el.value.trim(); if (el.dataset.f === 'on') renderPlanPreview(); });
$('#pl-add').onclick = () => {
  if (!S.uid){ toast('로그인한 상태로 열어야 쓸 수 있어요.'); return; }
  const type = $('#pl-type').value;
  const levels = $('#pl-levels').value.split(/[,·\/]/).map(x => x.trim()).filter(Boolean).slice(0, 8);
  if (type === 'level' && levels.length < 2){ toast('단계를 두 개 이상 적어 주세요.'); return; }
  const t0 = Date.now(); let n = 0;
  PLAN.rows.filter(x => x.on).forEach(x => {
    const nm = (`${x.subj} ${x.content || x.area}`).trim().slice(0, 40);
    const it = {id:'i' + (t0 + n).toString(36) + n, name:nm, type, createdAt:t0 + n, group:x.subj || '', plan:true, subj:x.subj, area:x.area, content:x.content, date:x.date || ''};
    if (type === 'level') it.levels = levels;
    S.sheet.items.push(it); n++;
  });
  saveSheet(); renderSheet(); closeDlgs(); PLAN.rows = []; $('#pl-text').value = ''; renderPlanPreview();
  toast(`평가 항목 ${n}개를 명렬표에 넣었어요.`);
};
function renderPlanBox(){
  const items = (S.sheet.items || []).filter(it => it.plan || it.date || it.subj);
  const roster = S.profile.roster || [], vals = S.sheet.values || {};
  const box = $('#plan-box');
  if (!items.length){ box.hidden = true; return; }
  box.hidden = false;
  if (document.activeElement && box.contains(document.activeElement)) return;
  const tk = ymd(today());
  const filled = (it, no) => { const v = (vals[it.id] || {})[no]; return it.type === 'check' ? v === true : v !== undefined && v !== null && v !== '' && v !== false; };
  const sorted = items.slice().sort((a, b) => (a.date || '9999') < (b.date || '9999') ? -1 : (a.date || '9999') > (b.date || '9999') ? 1 : (a.createdAt || 0) - (b.createdAt || 0));
  const doneN = sorted.filter(it => roster.length && roster.every(r => filled(it, r.no))).length;
  $('#plan-sum').textContent = `${items.length}개 중 ${doneN}개 완료`;
  $('#plan-table').innerHTML = `<div class="tablewrap"><table class="led plan-t"><thead><tr><th>과목</th><th>영역</th><th>평가 내용</th><th>평가일</th><th>완료</th><th>미실시 학생</th></tr></thead><tbody>${sorted.map(it => {
    const miss = roster.filter(r => !filled(it, r.no));
    const done = roster.length && !miss.length;
    const late = it.date && it.date < tk && !done;
    return `<tr class="${done ? 'done' : late ? 'late' : ''}"><td>${esc(it.subj || it.group || '')}</td><td>${esc(it.area || '')}</td><td>${esc(it.content || it.name)}</td>
      <td class="n"><input type="date" id="pd-${it.id}" data-plan-date="${it.id}" value="${esc(it.date || '')}" aria-label="${esc(it.name)} 평가일"></td>
      <td class="n">${done ? '<b class="ok">완료</b>' : `${roster.length - miss.length}/${roster.length}`}</td>
      <td class="miss">${done ? '' : miss.length > 10 ? `${miss.length}명` : miss.map(r => esc(r.name || r.no + '번')).join(', ')}</td></tr>`;
  }).join('')}</tbody></table></div>`;
}
$('#plan-box').addEventListener('change', e => { const el = e.target.closest('[data-plan-date]'); if (!el) return; const it = (S.sheet.items || []).find(x => x.id === el.dataset.planDate); if (!it) return; it.date = el.value; saveSheet(); });
$('#plan-box').addEventListener('focusout', () => setTimeout(() => { if (!($('#plan-box').contains(document.activeElement))) renderPlanBox(); }, 0));
$('#open-plan').onclick = () => { PLAN.rows = []; renderPlanPreview(); $('#pl-info').textContent = ''; openDlg('#dlg-plan'); };
$('#pl-type').addEventListener('change', e => { $('#pl-levels').hidden = e.target.value !== 'level'; });
function planOn(k){ return (S.sheet.items || []).filter(it => it.date === k); }
function groupAverages(no){
  const vals = S.sheet.values || {}, out = [];
  const groups = {};
  (S.sheet.items || []).filter(it => it.type === 'score' && it.group).forEach(it => { (groups[it.group] = groups[it.group] || []).push(it); });
  Object.entries(groups).forEach(([g, its]) => {
    const ns = its.map(it => Number((vals[it.id] || {})[no])).filter((n, i) => { const v = (vals[its[i].id] || {})[no]; return v !== undefined && v !== '' && !isNaN(n); });
    out.push({g, its, avg:ns.length ? Math.round(ns.reduce((a, b) => a + b, 0) / ns.length * 10) / 10 : null, n:ns.length});
  });
  return out;
}

/* ================= 통합 검색 ================= */
const SR = {daily:null};
function openSearch(){ openDlg('#dlg-search'); const i = $('#sr-input'); i.focus(); i.select(); runSearch(); }
async function loadDailyAll(){
  if (!S.db || SR.loading) return; SR.loading = true;
  try { const snap = await S.db.collection('daily').get(); SR.daily = docs(snap); runSearch(); } catch (e){ SR.daily = SR.daily || []; } finally { SR.loading = false; }
}
function runSearch(){
  const q = $('#sr-input').value.trim();
  const box = $('#sr-results');
  if (q.length < 1){ box.innerHTML = '<p class="hint">학급일지·상담·출결 사유·할 일·메모·공지·일정·명부·행발·명렬표·예산을 한 번에 찾아요.</p>'; return; }
  const terms = q.toLowerCase().split(/\s+/).filter(Boolean);
  const hit = s => { s = String(s || '').toLowerCase(); return terms.every(t => s.includes(t)); };
  const mark = s => { let h = esc(String(s || '')); terms.forEach(t => { const re = new RegExp(t.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'gi'); h = h.replace(re, m => `<mark>${m}</mark>`); }); return h; };
  const cut = (s, n = 90) => { s = String(s || '').replace(/\s+/g, ' '); const t = terms[0], i = s.toLowerCase().indexOf(t); if (s.length <= n) return s; const st = Math.max(0, i - 30); return (st ? '…' : '') + s.slice(st, st + n) + (st + n < s.length ? '…' : ''); };
  const R = [];
  const add = (group, date, title, body, go) => R.push({group, date, title, body, go});
  S.journal.forEach(e => { const nm = (e.students || []).map(stuName).join(', '); const d = e.doc ? Object.values(e.doc).join(' ') : ''; if (hit(`${e.text} ${nm} ${e.cat} ${e.att ? attLabel(e.att) : ''} ${d}`)) add(e.cat === '할일' ? '내 할 일' : e.cat === '상담' || e.cat === '학부모' ? '상담' : e.cat === '출결' ? '출결' : '학급일지', e.date, `${e.cat}${nm ? ' · ' + nm : ''}`, e.text + (d ? ' · ' + d : ''), {t:'j', e}); });
  ((S.notes && S.notes.items) || []).forEach(n => { if (hit(n.text)) add('메모장', n.createdAt ? ymd(new Date(n.createdAt)) : '', '메모', n.text, {t:'me'}); });
  Object.entries((S.stuNotes && S.stuNotes.hb) || {}).forEach(([no, t]) => { if (t && hit(t + ' ' + stuName(+no))) add('행발', '', stuName(+no), t, {t:'stu', no:+no}); });
  (S.profile.roster || []).forEach(r => { const s = [r.no + '번', r.name, r.birth, r.prev, r.guardian, r.phone, r.addr, r.note, ...Object.values(r.x || {})].join(' '); if (hit(s)) add('우리 반 명부', '', stuName(r.no), [r.birth, r.prev, r.phone, r.note].filter(Boolean).join(' · '), {t:'stu', no:r.no}); });
  Object.entries(S.rosG || {}).forEach(([c, d]) => (d.students || []).forEach(r => { const s = [r.name, r.birth, r.prev, r.guardian, r.phone, r.note, ...Object.values(r.x || {})].join(' '); if (hit(s)) add('학년 명부', '', `${c.slice(1)}반 ${r.no ?? ''}번 ${r.name || ''}`, [r.prev, r.phone, r.note].filter(Boolean).join(' · '), {t:'ros', c:+c.slice(1)}); }));
  const items = S.sheet.items || [], vals = S.sheet.values || {};
  items.forEach(it => { if (hit(it.name + ' ' + (it.content || ''))) add('명렬표', it.date || '', it.name, [it.subj, it.area, it.content].filter(Boolean).join(' · '), {t:'sheet'}); Object.entries(vals[it.id] || {}).forEach(([no, v]) => { if (typeof v === 'string' && v && hit(`${v} ${it.name} ${stuName(+no)}`)) add('명렬표', '', `${it.name} · ${stuName(+no)}`, v, {t:'sheet'}); }); });
  S.events.forEach(e => { if (hit(e.title + ' ' + (e.who || ''))) add('학년 일정', e.date, e.title, e.who && e.who !== '전체' ? e.who : '', {t:'gday', k:e.date}); });
  S.tasks.forEach(t => { if (hit(t.title + ' ' + (t.note || ''))) add('학년 할 일', t.due || '', t.title, t.note || '', {t:'tasks'}); });
  S.notices.forEach(n => { if (hit(n.title + ' ' + (n.body || ''))) add('협의·공지', n.date || (n.createdAt ? ymd(new Date(n.createdAt)) : ''), n.title, n.body, {t:'notices'}); });
  S.links.forEach(l => { if (hit(l.title + ' ' + l.url)) add('수업자료', '', l.title, l.url, {t:'links'}); });
  (S.ops || []).forEach(o => { const fn = (o.files || []).map(f => f.name).join(' '); if (hit(`${o.title} ${o.cat} ${o.body || ''} ${o.url || ''} ${fn}`)) add('운영자료', '', `${o.cat ? o.cat + ' · ' : ''}${o.title}`, o.body || fn, {t:'ops'}); });
  [['학년 문구', S.phG], ['내 문구', S.phM]].forEach(([g, l]) => (l || []).forEach(p => { if (hit(p.title + ' ' + p.text)) add(g, '', p.title, p.text, {t:'ops'}); }));
  [['학년 예산', S.budG, 'budget'], ['내 예산', S.budM, 'me-budget']].forEach(([g, ls, r]) => (ls || []).forEach(l => { const s = [l.act, l.biz, l.item, l.stat, ...(l.logs || []).map(x => x.text)].join(' '); if (hit(s)) add(g, '', [l.item, l.act].filter(Boolean).join(' · '), (l.logs || []).filter(x => hit(x.text)).map(x => `${x.text} ${wonS(numIn(x.amt))}원`).join(', '), {t:'route', r}); }));
  SR.list = R;
  if (!R.length){ box.innerHTML = `<p class="empty">"${esc(q)}"(이)가 들어간 기록이 없어요.${SR.loading ? '' : ''}</p>`; return; }
  R.sort((a, b) => (b.date || '') < (a.date || '') ? -1 : (b.date || '') > (a.date || '') ? 1 : 0);
  const order = ['학급일지', '상담', '출결', '내 할 일', '행발', '우리 반 명부', '명렬표', '메모장', '학년 일정', '학년 할 일', '일일계획·알림장', '협의·공지', '학년 명부', '학년 예산', '내 예산', '수업자료', '운영자료', '학년 문구', '내 문구'];
  const by = {}; R.forEach((r, i) => { r.i = i; (by[r.group] = by[r.group] || []).push(r); });
  box.innerHTML = `<p class="hint" style="margin:0 0 6px">${R.length}건</p>` + order.filter(g => by[g]).map(g => `<div class="sr-g"><h4>${g} <span>${by[g].length}</span></h4>${by[g].slice(0, 30).map(r => `<button type="button" class="sr-item" data-sr="${r.i}"><span class="d mono">${r.date ? mdShort(r.date) : ''}</span><span class="t"><b>${mark(r.title)}</b>${r.body ? `<span>${mark(cut(r.body))}</span>` : ''}</span></button>`).join('')}${by[g].length > 30 ? `<p class="hint">외 ${by[g].length - 30}건 · 검색어를 더 적어 주세요</p>` : ''}</div>`).join('');
}
$('#sr-input').addEventListener('input', () => { clearTimeout(SR.t); SR.t = setTimeout(runSearch, 120); });
$('#sr-input').addEventListener('keydown', e => { if (e.key === 'Enter'){ const b = $('#sr-results .sr-item'); if (b) b.click(); } });
$('#sr-results').addEventListener('click', e => {
  const b = e.target.closest('[data-sr]'); if (!b) return;
  const r = SR.list[+b.dataset.sr]; if (!r) return; const g = r.go;
  closeDlgs();
  if (g.t === 'j'){ if (g.e.cat === '할일') go('me-todo'); else { go('me'); if (g.e.date) setJDate(g.e.date); } }
  else if (g.t === 'stu'){ S.selStu = g.no; S.stuCat = 'all'; go('me-stu'); renderStu(); }
  else if (g.t === 'me') go('me');
  else if (g.t === 'sheet') go('me-sheet');
  else if (g.t === 'ros'){ go('roster'); setTimeout(() => { const c = $(`#ros-g [data-cls="${g.c}"]`); if (c) c.click(); }, 0); }
  else if (g.t === 'gday'){ go('calendar'); S.selDate = g.k; S.month = new Date(fromYmd(g.k).getFullYear(), fromYmd(g.k).getMonth(), 1); if (S.db) listenDaily(); renderCal(); renderDay(); }
  else if (g.t === 'route') go(g.r);
  else go(g.t);
  window.scrollTo(0, 0);
});
$('#open-search').onclick = openSearch;
document.addEventListener('keydown', e => {
  if ((e.ctrlKey || e.metaKey) && (e.key === 'k' || e.key === 'K')){ e.preventDefault(); openSearch(); }
  else if (e.key === '/' && !e.target.closest('input, textarea, select, [contenteditable]') && $('#dlg-search').hidden){ e.preventDefault(); openSearch(); }
});

/* ================= 주간 수업일지 ================= */
const WK = {mode:'day', cache:{}};
function setJView(m){ WK.mode = m; setTimeout(placeStuCol, 0); $$('#j-view button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === m)); $('#j-dayview').hidden = m !== 'day'; $('#j-week').hidden = m !== 'week'; if (m === 'week') renderWeek(); }
$('#j-view').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (b) setJView(b.dataset.v); });
async function renderWeek(){
  const mon = mondayOf(S.jDate), days = [0, 1, 2, 3, 4].map(i => ymd(addDays(fromYmd(mon), i))), tk = ymd(today());
  const fri = fromYmd(days[4]);
  const w = weekAt(mon);
  $('#wk-label').textContent = `${w && w.no ? w.no + '주 · ' : ''}${fromYmd(mon).getMonth() + 1}.${fromYmd(mon).getDate()} ~ ${fri.getMonth() + 1}.${fri.getDate()}`;
  const draw = () => {
    const L = lunchAt();
    let h = `<div class="tablewrap"><table class="wk"><thead><tr><th></th>${days.map(k => { const d = fromYmd(k); return `<th class="${k === tk ? 'today' : ''}"><button type="button" class="linkbtn" data-wk-day="${k}">${d.getMonth() + 1}/${d.getDate()} (${WD[d.getDay()]})</button>${HOLIDAYS[k] ? `<small class="hol">${esc(HOLIDAYS[k])}</small>` : ''}</th>`; }).join('')}</tr></thead><tbody>`;
    const info = days.map(k => ({k, sf:subjFor(k), d:(WK.cache['d|' + k] || {}), g:(WK.cache['g|' + k] || null)}));
    for (let i = 0; i < 6; i++){
      if (i === L) h += `<tr class="lunch"><td colspan="6">점심</td></tr>`;
      h += `<tr><th class="p">${i + 1}교시</th>${info.map(x => {
        if (x.sf.off) return i === 0 ? `<td rowspan="6" class="off">${esc(x.sf.off)}</td>` : '';
        const p = (x.d.plan || [])[i] || {};
        const subj = p.s !== undefined && p.s !== null && p.s !== '' ? p.s : expand((x.sf.s || [])[i]);
        return `<td><b>${esc(subj || '')}</b>${p.t ? `<span class="topic">${esc(p.t)}</span>` : ''}${p.p ? `<span class="memo">${esc(p.p)}</span>` : ''}</td>`;
      }).join('')}</tr>`;
    }
    h += `<tr class="rowj"><th class="p">학급 기록</th>${info.map(x => { const js = S.journal.filter(e => covers(e, x.k) && e.cat !== '할일'); const att = js.filter(e => e.att); return `<td>${att.map(e => `<span class="chip red">${esc((e.students || []).map(n => n + '번').join(','))} ${attLabel(e.att)}</span>`).join('')}${js.length - att.length ? `<span class="hint">기록 ${js.length - att.length}개</span>` : ''}${planOn(x.k).map(it => `<span class="chip">평가 · ${esc(it.name)}</span>`).join('')}</td>`; }).join('')}</tr>`;
    h += `<tr class="rowm"><th class="p">메모</th>${info.map(x => `<td>${x.d.memo ? `<div class="pre">${esc(x.d.memo)}</div>` : ''}</td>`).join('')}</tr>`;
    $('#wk-table').innerHTML = h + '</tbody></table></div>';
  };
  draw();
  if (!S.db) return;
  const need = [];
  days.forEach(k => { if (S.uid) need.push(['d|' + k, DAYPATH(k)]); need.push(['g|' + k, 'daily/' + k]); });
  await Promise.all(need.map(async ([key, path]) => { try { const s = await S.db.doc(path).get(); WK.cache[key] = s.exists ? s.data() : null; } catch (e){} }));
  if (WK.mode === 'week' && mondayOf(S.jDate) === mon) draw();
}
$('#wk-prev').onclick = () => { setJDate(ymd(addDays(fromYmd(mondayOf(S.jDate)), -7))); renderWeek(); };
$('#wk-next').onclick = () => { setJDate(ymd(addDays(fromYmd(mondayOf(S.jDate)), 7))); renderWeek(); };
$('#wk-now').onclick = () => { setJDate(ymd(today())); renderWeek(); };
$('#j-week').addEventListener('click', e => { const b = e.target.closest('[data-wk-day]'); if (b){ setJDate(b.dataset.wkDay); setJView('day'); } });

/* ================= 아침 안내 (교실 도구) ================= */
const ROUTINE = () => `data/users/${S.uid}/routine`;
const MO = {size:1, day:null, dayKey:null};
function rt(){ S.routine = S.routine || {items:[], done:{}, extra:{}}; if (!S.routine.extra) S.routine.extra = {}; if (!S.routine.done) S.routine.done = {}; return S.routine; }
function saveRoutine(){
  const r = rt(); const keep = ymd(addDays(today(), -120));
  ['done', 'extra'].forEach(f => Object.keys(r[f]).forEach(d => { if (d < keep) delete r[f][d]; }));
  queueSet(ROUTINE(), () => ({items:S.routine.items, done:S.routine.done, extra:S.routine.extra, updatedAt:Date.now()}), false);
}
function renderRoutine(){ if (!$('#tool-morn').hidden && !$('#tools').hidden) renderMorning(false); }
async function renderMorning(fetchDay){
  const k = ymd(today()), d = today();
  $('#mo-date').textContent = `${d.getMonth() + 1}월 ${d.getDate()}일 ${WD[d.getDay()]}요일`;
  $('#mo-hello').textContent = HOLIDAYS[k] ? HOLIDAYS[k] : '좋은 아침이에요!';
  if (!S.uid){ $('#mo-list').innerHTML = '<li class="hint">로그인한 상태로 열어야 쓸 수 있어요.</li>'; return; }
  const r = rt(), dn = r.done[k] || {}, ex = r.extra[k] || [];
  const all = r.items.map(x => Object.assign({daily:true}, x)).concat(ex);
  const n = all.filter(x => dn[x.id]).length;
  $('#mo-count').textContent = all.length ? `${n}/${all.length}` : '';
  const ae = document.activeElement;
  if (!(MO.editing && $('#mo-list .mo-edf'))) $('#mo-list').innerHTML = all.length ? all.map(x => (x.imgs && x.imgs.length) ? `<li class="mo-img ${dn[x.id] ? 'on' : ''}"><div class="mo-imgs">${thumbsHtml(x.imgs, '')}</div><div class="mo-imgbar"><button type="button" class="mo-chk" data-mo="${esc(x.id)}" aria-pressed="${!!dn[x.id]}"><span class="box">${dn[x.id] ? '✓' : ''}</span><span class="t">${esc(x.name || '사진')}</span></button><button type="button" class="mo-ed" data-mo-edit="${esc(x.id)}" aria-label="설명 고치기" title="설명 고치기">✎</button><button type="button" class="x" data-mo-del="${esc(x.id)}" aria-label="사진 빼기">×</button></div></li>` : `<li class="${dn[x.id] ? 'on' : ''}"><button type="button" class="mo-chk" data-mo="${esc(x.id)}" aria-pressed="${!!dn[x.id]}"><span class="box">${dn[x.id] ? '✓' : ''}</span><span class="t">${esc(x.name)}</span>${x.daily ? '' : '<span class="tag">오늘만</span>'}</button><button type="button" class="mo-ed" data-mo-edit="${esc(x.id)}" data-daily="${x.daily ? 1 : ''}" aria-label="${esc(x.name)} 고치기" title="고치기">✎</button>${x.daily ? '' : `<button type="button" class="x" data-mo-del="${esc(x.id)}" aria-label="${esc(x.name)} 빼기">×</button>`}</li>`).join('')
    : '<li class="hint">아래 "매일 할 일 고치기"에서 아침 독서, 숙제 내기처럼 날마다 하는 일을 넣어 주세요.</li>';
  hydrateImgs();
  if (ae !== $('#mo-daily-new')) $('#mo-daily').innerHTML = r.items.length ? r.items.map(x => `<li><span>${esc(x.name)}</span><button type="button" class="x" data-mo-ddel="${esc(x.id)}" aria-label="${esc(x.name)} 빼기">×</button></li>`).join('') : '<li class="hint">아직 없어요.</li>';
  const live = kk => r.items.filter(x => !x.at || ymd(new Date(x.at)) <= kk);
  const days = []; for (let i = 0; i < 14; i++){ const kk = ymd(addDays(today(), -i)); if ((isSchoolDay(kk) && live(kk).length) || (r.done[kk] && Object.keys(r.done[kk]).length) || (r.extra[kk] || []).length) days.push(kk); }
  $('#mo-log').innerHTML = `<div class="tablewrap"><table class="led"><thead><tr><th>날짜</th><th>한 일</th><th>못 한 일</th></tr></thead><tbody>${days.map(kk => {
    const dd = r.done[kk] || {}, list = live(kk).concat(r.extra[kk] || []);
    const did = list.filter(x => dd[x.id]), not = list.filter(x => !dd[x.id]);
    return `<tr><td class="n">${mdShort(kk)} (${WD[fromYmd(kk).getDay()]})</td><td>${did.map(x => esc(x.name)).join(', ') || '<span class="hint">—</span>'}</td><td style="color:var(--danger)">${kk === k ? '' : not.map(x => esc(x.name)).join(', ')}</td></tr>`;
  }).join('') || '<tr><td colspan="3" class="hint">아직 기록이 없어요.</td></tr>'}</tbody></table></div><p class="hint" style="margin:4px 0 0">매일 할 일은 넣은 날부터 기록에 잡혀요. 뺀 일은 지난 기록에서도 빠져요.</p>`;
  // 시간표
  if (fetchDay || MO.dayKey !== k){
    MO.dayKey = k; MO.day = null;
    if (S.db) try { const sn = await S.db.doc(DAYPATH(k)).get(); MO.day = sn.exists ? sn.data() : null; } catch (e){}
  }
  const sf = subjFor(k), plan = (MO.day && MO.day.plan) || [];
  if (sf.off) $('#mo-tt').innerHTML = `<li class="off">${esc(sf.off)}</li>`;
  else { const L = lunchAt(); let h = ''; for (let i = 0; i < 6; i++){ if (i === L) h += '<li class="lunch"><span class="p"></span><b>점심</b></li>'; const p = plan[i] || {}; const sj = p.s !== undefined && p.s !== null && p.s !== '' ? p.s : expand((sf.s || [])[i]); if (sj) h += `<li><span class="p">${i + 1}</span><b>${esc(sj)}</b><span class="mo-pw">${p.p ? `<small class="prep" title="준비물">${esc(p.p)}</small>` : ''}<button type="button" class="mo-pe ${p.m ? 'has' : ''}" data-mo-prep="${i}" title="과목 옆에 짧게 적기">${p.m ? esc(p.m) : '+ 메모'}</button></span></li>`; } $('#mo-tt').innerHTML = h || '<li class="off">시간표가 비어 있어요</li>'; }
  const ml = await mealFor(k);
  $('#mo-meal-card').hidden = !ml && !GAS;
  $('#mo-meal').innerHTML = ml ? ml.split(/\s*[,/]\s*/).filter(Boolean).map(x => `<span>${esc(x)}</span>`).join('') : `<p class="hint">${GAS ? '설정 → 나이스에서 학교를 고르면 급식이 떠요.' : ''}</p>`;
}
$('#tool-morn').addEventListener('click', e => {
  if (!S.uid) return;
  const pe = e.target.closest('[data-mo-prep]');
  if (pe){
    const i = +pe.dataset.moPrep, k = ymd(today());
    const base = (S.jDate === k && S.day) ? S.day : (MO.day || {});
    const cur = ((base.plan || [])[i] || {}).m || '';
    const inp = document.createElement('input'); inp.type = 'text'; inp.className = 'mo-pe-in'; inp.value = cur; inp.maxLength = 60; inp.setAttribute('aria-label', (i + 1) + '교시 메모');
    pe.replaceWith(inp); inp.focus(); inp.select();
    let done = false;
    const fin = ok => {
      if (done) return; done = true;
      const v = inp.value.trim();
      if (ok && v !== cur){
        const plan = Array.from({length:6}, (_, j) => Object.assign({}, (base.plan || [])[j] || {}));
        plan[i].m = v;
        const data = Object.assign({}, base, {plan, date:k});
        if (S.jDate === k && S.day){ S.day = data; } MO.day = data;
        queueSet(DAYPATH(k), () => data, false);
      }
      renderMorning(false);
    };
    inp.addEventListener('keydown', ev => { if (ev.key === 'Enter'){ ev.preventDefault(); fin(true); } else if (ev.key === 'Escape'){ ev.preventDefault(); fin(false); } });
    inp.addEventListener('blur', () => fin(true));
    return;
  }
  const r = rt(), k = ymd(today());
  const c = e.target.closest('[data-mo]');
  if (c){ const dn = Object.assign({}, r.done[k] || {}); if (dn[c.dataset.mo]) delete dn[c.dataset.mo]; else dn[c.dataset.mo] = Date.now(); r.done = Object.assign({}, r.done, {[k]:dn}); saveRoutine(); renderMorning(false); return; }
  const ed = e.target.closest('[data-mo-edit]');
  if (ed){
    const id = ed.dataset.moEdit, daily = !!ed.dataset.daily, li = ed.closest('li');
    const cur = (daily ? r.items : (r.extra[k] || [])).find(x => x.id === id); if (!cur) return;
    MO.editing = true;
    li.innerHTML = `<form class="mo-edf"><input type="text" value="${esc(cur.name)}" maxlength="200" aria-label="할 일 고치기"><button type="submit" class="btn small primary">저장</button><button type="button" class="btn small" data-mo-cancel>취소</button></form>`;
    const inp = li.querySelector('input'); inp.focus(); inp.select();
    li.querySelector('form').addEventListener('submit', ev => {
      ev.preventDefault(); const v = inp.value.trim(); if (!v) return; MO.editing = false;
      if (daily) r.items = r.items.map(x => x.id === id ? Object.assign({}, x, {name:v.slice(0, 200)}) : x);
      else r.extra = Object.assign({}, r.extra, {[k]:(r.extra[k] || []).map(x => x.id === id ? Object.assign({}, x, {name:v.slice(0, 200)}) : x)});
      saveRoutine(); renderMorning(false); toast(daily ? '매일 할 일을 고쳤어요. 내일부터도 바뀐 이름으로 나와요.' : '고쳤어요.');
    });
    li.querySelector('[data-mo-cancel]').onclick = ev => { ev.stopPropagation(); MO.editing = false; renderMorning(false); };
    return;
  }
  if (e.target.closest('.mo-edf')) return;
  const d = e.target.closest('[data-mo-del]');
  if (d){ const gone = (r.extra[k] || []).find(x => x.id === d.dataset.moDel); r.extra = Object.assign({}, r.extra, {[k]:(r.extra[k] || []).filter(x => x.id !== d.dataset.moDel)}); saveRoutine(); renderMorning(false); ((gone && gone.imgs) || []).forEach(dropImage); return; }
  const dd = e.target.closest('[data-mo-ddel]');
  if (dd){ if (!twoStep(dd, '빼기?')) return; r.items = r.items.filter(x => x.id !== dd.dataset.moDdel); saveRoutine(); renderMorning(false); }
});
$('#mo-add').addEventListener('submit', e => {
  e.preventDefault(); if (!S.uid) return;
  const v = $('#mo-new').value.trim(); if (!v) return;
  const r = rt(), k = ymd(today());
  r.extra = Object.assign({}, r.extra, {[k]:(r.extra[k] || []).concat([{id:rid(), name:v.slice(0, 200)}])});
  $('#mo-new').value = ''; saveRoutine(); renderMorning(false);
});
$('#mo-daily-add').addEventListener('submit', e => {
  e.preventDefault(); if (!S.uid) return;
  const v = $('#mo-daily-new').value.trim(); if (!v) return;
  const r = rt(); r.items = r.items.concat([{id:rid(), name:v.slice(0, 200), at:Date.now()}]);
  $('#mo-daily-new').value = ''; saveRoutine(); renderMorning(false);
});
$('#mo-big').onclick = () => { MO.size = Math.min(1.8, MO.size + .15); $('#tool-morn').style.setProperty('--mo', MO.size); };
$('#mo-small').onclick = () => { MO.size = Math.max(.7, MO.size - .15); $('#tool-morn').style.setProperty('--mo', MO.size); };
async function bulkLate(kind){
  const k = ymd(today());
  const late = S.journal.filter(e => e.cat === '할일' && !e.done && e.date && e.date < k);
  if (!late.length) return;
  const col = S.db.doc(PROFILE()).collection('journal');
  let n = 0;
  for (const e of late){ try { await col.doc(e.id).update(kind === 'today' ? {date:k} : {done:true}); n++; } catch (er){ wErr(er, false); break; } }
  toast(kind === 'today' ? `밀린 할 일 ${n}개를 오늘로 옮겼어요.` : `밀린 할 일 ${n}개를 끝냈어요.`);
}

/* ================= 칠판 모드 ================= */
const BD = {size:1};
function nextSchoolDay(k){ let d = fromYmd(k); for (let i = 0; i < 20; i++){ d = addDays(d, 1); const x = ymd(d); if (isSchoolDay(x)) return x; } return ymd(addDays(fromYmd(k), 1)); }
async function openBoard(k){
  const nx = nextSchoolDay(k);
  BD.k = k; BD.nx = nx;
  $('#board').hidden = false; document.body.classList.add('boarding');
  const d = fromYmd(k), n = fromYmd(nx);
  $('#bd-date').textContent = `${d.getMonth() + 1}월 ${d.getDate()}일 ${WD[d.getDay()]}요일`;
  $('#bd-next-h').textContent = `${n.getMonth() + 1}월 ${n.getDate()}일 (${WD[n.getDay()]}) 시간표`;
  $('#bd-notice').textContent = '불러오는 중…'; $('#bd-tt').innerHTML = ''; $('#bd-prep').innerHTML = '';
  let g = null, dn = null;
  if (S.db){
    try { const s = await S.db.doc('daily/' + k).get(); g = s.exists ? s.data() : null; } catch (e){}
    if (S.uid) try { const s = await S.db.doc(DAYPATH(nx)).get(); dn = s.exists ? s.data() : null; } catch (e){}
  }
  $('#bd-notice').textContent = g && g.notice ? g.notice : '아직 이 날 알림장이 없어요. 학년 공간 "일일계획·알림장"에 적으면 여기 떠요.';
  const sf = subjFor(nx), plan = (dn && dn.plan) || [];
  if (sf.off) $('#bd-tt').innerHTML = `<li class="off">${esc(sf.off)}</li>`;
  else { const L = lunchAt(); let h = ''; for (let i = 0; i < 6; i++){ if (i === L) h += '<li class="lunch">점심</li>'; const p = plan[i] || {}; const s = p.s !== undefined && p.s !== null && p.s !== '' ? p.s : expand((sf.s || [])[i]); if (s) h += `<li><span>${i + 1}</span><b>${esc(s)}</b></li>`; } $('#bd-tt').innerHTML = h || '<li class="off">시간표가 비어 있어요</li>'; }
  const prep = plan.map(p => p && p.p).filter(Boolean);
  if (dn && dn.memo) prep.push(dn.memo);
  $('#bd-prep').innerHTML = prep.length ? `<h3>준비물 · 챙길 것</h3><ul>${prep.map(x => `<li>${esc(x)}</li>`).join('')}</ul>` : '';
  const ml = await mealFor(k);
  $('#bd-meal').innerHTML = ml ? `<h3>오늘 급식</h3><p>${esc(ml)}</p>` : '';
}
function closeBoard(){ $('#board').hidden = true; document.body.classList.remove('boarding'); if (document.fullscreenElement) document.exitFullscreen().catch(() => {}); }
$('#bd-close').onclick = closeBoard;
$('#bd-big').onclick = () => { BD.size = Math.min(1.8, BD.size + .15); $('#board').style.setProperty('--bd', BD.size); };
$('#bd-small').onclick = () => { BD.size = Math.max(.7, BD.size - .15); $('#board').style.setProperty('--bd', BD.size); };
$('#bd-full').onclick = () => { const el = $('#board'); if (document.fullscreenElement) document.exitFullscreen().catch(() => {}); else if (el.requestFullscreen) el.requestFullscreen().catch(() => toast('이 화면에서는 전체 화면을 쓸 수 없어요.')); };
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('#board').hidden) closeBoard(); });

/* ================= 구글 버전 전용: 나이스 · 구글 캘린더 ================= */
const GAS = window.__gasCall || null;
const NE = {meal:{}};
async function mealFor(k){
  const ne = S.settings.neis; if (!GAS || !ne || !ne.code) return '';
  if (NE.meal[k] !== undefined) return NE.meal[k];
  try { const r = await GAS('neisMeal', ne.office, ne.code, k.replace(/-/g, ''), k.replace(/-/g, '')); NE.meal[k] = r.filter(x => /중식/.test(x.kind) || r.length === 1).map(x => x.menu.replace(/\n/g, ', ')).join(' / '); }
  catch (e){ NE.meal[k] = ''; }
  return NE.meal[k];
}
async function renderMeal(){
  const els = $$('.meal-today'); if (!els.length) return;
  const m = await mealFor(ymd(today()));
  els.forEach(el => { el.hidden = !m; el.innerHTML = m ? `<span class="d">급식</span><span class="t">${esc(m)}</span>` : ''; });
}
$('#ne-find').onclick = async () => {
  if (!GAS) return;
  const q = $('#ne-q').value.trim(); if (!q){ toast('학교 이름을 적어 주세요.'); return; }
  $('#ne-res').innerHTML = '<option>찾는 중…</option>';
  try {
    const r = await GAS('neisSchools', q);
    NE.schools = r;
    $('#ne-res').innerHTML = r.length ? r.map((s, i) => `<option value="${i}">${esc(s.name)} · ${esc(s.addr || '')}</option>`).join('') : '<option value="">찾지 못했어요</option>';
  } catch (e){ $('#ne-res').innerHTML = `<option value="">${esc(String(e.message || e).replace(/^.*neis:\s*/, ''))}</option>`; }
};
$('#ne-key-save').onclick = async () => {
  if (!GAS) return;
  try { await GAS('setNeisKey', $('#ne-key').value.trim()); $('#ne-key').value = ''; toast('나이스 인증키를 저장했어요.'); NE.meal = {}; renderMeal(); } catch (e){ toast(String(e.message || e).replace(/^.*?:\s*/, '')); }
};
$('#ne-import').onclick = async () => {
  const ne = S.settings.neis; if (!GAS || !ne){ toast('먼저 학교를 찾아 저장해 주세요.'); return; }
  if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  const sy = syStart(), from = `${sy}0301`, to = `${sy + 1}0228`;
  const b = $('#ne-import'); b.disabled = true; b.textContent = '가져오는 중…';
  try {
    const rows = await GAS('neisSchedule', ne.office, ne.code, from, to, (String(S.settings.gradeName).match(/\d/) || ['0'])[0]);
    const have = new Set(S.events.map(e => e.id));
    let n = 0;
    for (const r of rows){
      if (/토요휴업/.test(r.name)) continue;
      const id = 'neis-' + r.date + '-' + Array.from(r.name).reduce((h, c) => (h * 31 + c.charCodeAt(0)) >>> 0, 7).toString(36);
      if (have.has(id)) continue;
      const k = `${r.date.slice(0, 4)}-${r.date.slice(4, 6)}-${r.date.slice(6, 8)}`;
      await S.db.doc('events/' + id).set({date:k, time:null, title:`[학사] ${r.name}${r.off ? ' (' + r.off + ')' : ''}`, who:'전체', kind:r.off ? 'off' : guessKind(r.name) === 'etc' ? 'event' : guessKind(r.name), createdBy:S.uid, createdAt:Date.now(), src:'neis'}); n++;
    }
    toast(n ? `나이스 학사일정 ${n}개를 학년 일정에 넣었어요.` : '새로 넣을 학사일정이 없어요.');
  } catch (e){ toast('학사일정을 가져오지 못했어요. ' + String(e.message || e).replace(/^.*neis:\s*/, '')); }
  b.disabled = false; b.textContent = '학사일정 학년 일정으로 가져오기';
};
/* 구글 캘린더: 고른 것만 보내요 */
const GCALP = () => `data/users/${S.uid}/gcal`;
const GC = {busy:false, ev:{}};
const gcalOn = () => !!GAS && !!S.uid;
function gcalItem(key){
  const [t, id] = [key.slice(0, key.indexOf(':')), key.slice(key.indexOf(':') + 1)];
  if (t === 'ev'){ const e = S.events.find(x => x.id === id); return e && {title:`[${S.settings.gradeName || '학년'}] ${e.title}`, date:e.date, time:e.time || '', end:''}; }
  if (t === 'tk'){ const e = S.tasks.find(x => x.id === id); return e && e.due && !e.done && {title:`[학년 할 일] ${e.title}`, date:e.due, time:'', end:''}; }
  if (t === 'j'){ const e = S.journal.find(x => x.id === id); if (!e || !e.date || (e.cat === '할일' && e.done)) return null; const nm = (e.students || []).map(stuName).join(', '); return {title:e.cat === '할일' ? `[할 일] ${e.text}` : `[${e.cat}] ${nm ? nm + ' ' : ''}${e.text}`, date:e.date, time:e.time || '', end:e.end || ''}; }
  return null;
}
const gsig = it => [it.title, it.date, it.time, it.end].join('|');
const gcalHas = key => !!(((S.gcal || {}).sent || {})[key]);
function calBtn(key){ if (!gcalOn()) return ''; const on = gcalHas(key); return `<button type="button" class="btn small calbtn ${on ? 'on' : ''}" data-cal="${esc(key)}" title="${on ? '내 구글 캘린더에서 빼기' : '내 구글 캘린더에 넣기'}" aria-pressed="${on}">${on ? '캘린더 ✓' : '캘린더에'}</button>`; }
function saveGcal(){ queueSet(GCALP(), () => ({target:S.gcal.target || 'app', show:!!S.gcal.show, sent:S.gcal.sent || {}, updatedAt:Date.now()}), false); }
async function gcalToggle(key, force){
  if (!gcalOn()) return;
  S.gcal = S.gcal || {target:'app', show:false, sent:{}}; S.gcal.sent = Object.assign({}, S.gcal.sent);
  const cur = S.gcal.sent[key];
  try {
    if (cur && force !== true){ await GAS('calDel', cur.gid, S.gcal.target || 'app'); delete S.gcal.sent[key]; toast('구글 캘린더에서 뺐어요.'); }
    else { const it = gcalItem(key); if (!it){ toast('날짜가 있는 기록만 캘린더에 넣을 수 있어요.'); return; } const gid = await GAS('calPut', it, cur ? cur.gid : '', S.gcal.target || 'app'); S.gcal.sent[key] = {gid, sig:gsig(it)}; if (force !== true) toast('구글 캘린더에 넣었어요.'); }
    saveGcal(); rerenderCal();
  } catch (e){ toast('구글 캘린더에 연결하지 못했어요. ' + String(e.message || e).replace(/^.*?:\s*/, '')); }
}
function rerenderCal(){ if (S.space === 'me') renderMe(); else { renderDay(); renderTasks(); } }
async function gcalSync(){
  if (S.arc || !gcalOn() || GC.busy || !S.gcal || !S.gcal.sent) return;
  if (S.pending.size) return;
  GC.busy = true;
  try {
    const sent = Object.assign({}, S.gcal.sent); let ch = false;
    for (const [key, v] of Object.entries(sent)){
      const it = gcalItem(key);
      if (!it){ try { await GAS('calDel', v.gid, S.gcal.target || 'app'); } catch (e){} delete sent[key]; ch = true; continue; }
      if (gsig(it) !== v.sig){ try { const gid = await GAS('calPut', it, v.gid, S.gcal.target || 'app'); sent[key] = {gid, sig:gsig(it)}; ch = true; } catch (e){} }
    }
    if (ch){ S.gcal.sent = sent; saveGcal(); }
  } finally { GC.busy = false; }
}
let gcalTimer; function gcalSoon(){ if (S.arc || !gcalOn()) return; clearTimeout(gcalTimer); gcalTimer = setTimeout(gcalSync, 4000); }
async function loadGEvents(){
  if (!gcalOn() || !S.gcal || !S.gcal.show) { GC.ev = {}; return; }
  const a = ymd(addDays(today(), -7)), b = ymd(addDays(today(), 35));
  try { const r = await GAS('calEvents', a, b); const m = {}; r.forEach(e => { (m[e.date] = m[e.date] || []).push(e); }); GC.ev = m; if (S.space === 'me') { renderToday(); if (S.meTab === 'day') renderDayBoard(); } } catch (e){ GC.ev = {}; }
}
const gEventsOn = k => (GC.ev[k] || []);
function addAfter(key, sel){ if (gcalOn() && $(sel) && $(sel).checked) gcalToggle(key, true); }
['#cal-also-g', '#cal-also-j'].forEach(id => { const el = $(id); if (!el) return; try { el.checked = localStorage.getItem('cal' + id) === '1'; } catch (e){} el.addEventListener('change', () => { try { localStorage.setItem('cal' + id, el.checked ? '1' : '0'); } catch (e){} }); });


/* ---------- 구글 계정 바꾸기 (구글 버전) ---------- */
const APP_URL_FALLBACK = '';
function acctUrls(){
  const w = window.__gasWho || {};
  const base = (w.appUrl && /\/exec$/.test(w.appUrl)) ? w.appUrl : APP_URL_FALLBACK;
  const m = base.match(/^(https:\/\/script\.google\.com)(\/a\/macros\/[^/]+|\/macros)\/s\/([^/]+)\/(exec|dev)/);
  const nth = m ? [0, 1, 2, 3].map(n => `${m[1]}${m[2].startsWith('/a/') ? '/u/' + n + m[2] : '/macros/u/' + n}/s/${m[3]}/exec`) : [];
  return {base, nth};
}
function openAcct(){
  const w = window.__gasWho || {}, u = acctUrls();
  const err = window.__gasWhoErr;
  $('#ac-email').textContent = w.email || (window.__gasWho || err ? '알 수 없음' : '(확인 중)');
  let st;
  if (err) st = '교무수첩 서버에 연결하지 못했어요: ' + err + ' · 만든 선생님께 Code.gs를 새로 붙여 넣고 "새 버전"으로 배포했는지 확인해 달라고 해 주세요.';
  else if (w.deployOk === false) st = '만든 선생님의 배포 설정 문제예요. 배포 관리 → 편집에서 "다음 사용자 인증 정보로 실행"을 "웹 앱에 액세스하는 사용자"로 바꾸고 "새 버전"으로 배포해야 열려요. 계정을 바꿔도 해결되지 않아요.';
  else if (w.sharedOk === false) st = '이 계정으로 열 수 있는 학년 공간이 없어요. 학교 계정으로 바꾸거나, 설정·위 안내의 "학년 공간 정하기"에서 초대 링크로 들어가거나 새로 만들어요.';
  else if (w.email) st = '학년 공유 기록을 열 수 있는 계정이에요.';
  else st = '아직 서버 답을 기다리는 중이에요. 잠시 뒤 다시 눌러 보세요. 계속 이렇게 나오면 만든 선생님께 Code.gs를 새로 붙여 넣었는지 확인해 달라고 해 주세요.';
  $('#ac-state').textContent = st;
  const cont = u.base || '';
  $('#ac-choose').href = 'https://accounts.google.com/AccountChooser?continue=' + encodeURIComponent(cont);
  $('#ac-choose').hidden = false;
  $('#ac-nth').innerHTML = u.nth.map((x, i) => `<a class="btn small" href="${esc(x)}" target="_top" rel="noopener">${i + 1}번째 로그인 계정</a>`).join('');
  openDlg('#dlg-acct');
}
function renderAcctChip(){
  const w = window.__gasWho, el = $('#acct-chip'); if (!el) return;
  if (!w || !w.email){ el.hidden = true; return; }
  el.hidden = false; el.textContent = w.email.split('@')[0] + (w.sharedOk === false ? ' ⚠' : '');
  el.classList.toggle('warn', w.sharedOk === false);
}
window.addEventListener('gas-who', () => { renderAcctChip(); banner($('#banner-text').textContent || ''); if (!$('#dlg-acct').hidden) openAcct(); });
renderAcctChip(); if (window.__gasWho && window.__gasWho.sharedOk === false) banner('');

/* ---------- 학년 공간 정하기 · 초대 (구글 버전) ---------- */
let gradePickShown = false;
function gradePickSoon(){
  if (!window.__GAS_MODE) return;
  $('#bn-grade').hidden = false;
  banner('아직 들어간 학년 공간이 없어요. 나의 공간은 그대로 쓸 수 있어요.');
  if (!gradePickShown){ gradePickShown = true; setTimeout(openGradePick, 300); }
}
function openGradePick(){
  const w = window.__gasWho || {};
  $('#gj-email').textContent = w.email || '(확인 중)';
  $('#gj-why').textContent = window.__gasJoinErr ? window.__gasJoinErr
    : w.sharedOk === false && !w.noGrade ? '이 계정으로는 지금 학년 공유 기록 시트를 열 수 없어요. 다른 계정으로 바꾸거나, 초대를 받거나, 새로 만들어요.'
    : w.sharedOk === false ? '이 계정으로 들어간 학년 공간이 아직 없어요.'
    : '지금 학년 공간에서 다른 학년 공간으로 옮겨요. 지금 공간의 기록은 그대로 남아요.';
  $('#gj-msg').textContent = ''; $('#gj-name').value = $('#gj-name').value || (S.settings.gradeName || '');
  closeDlgs(); openDlg('#dlg-grade');
}
async function gradeEntered(msg){
  $('#gj-msg').textContent = '학년 공간을 불러오는 중…';
  try {
    const w = await window.__gasReset();
    window.__gasJoinErr = '';
    S.isOwner = !!(w && w.isOwner);
    if (!S.uid && w && w.uid){ S.uid = w.uid; S.privateOk = true; S.privateOffMsg = ''; startPrivate(); }
    if (w && w.sharedOk){ S.canWrite = true; document.body.classList.remove('ro'); $('#bn-grade').hidden = true; banner(''); }
    renderAcctChip(); renderStrip(); renderAll(); closeDlgs(); toast(msg);
  } catch (e){ $('#gj-msg').textContent = '불러오지 못했어요. 페이지를 다시 열어 주세요.'; }
}
$('#gj-join').onclick = async () => {
  const code = $('#gj-code').value.trim(); if (!code){ $('#gj-code').focus(); return; }
  const b = $('#gj-join'); b.disabled = true; $('#gj-msg').textContent = '들어가는 중…';
  try { await window.__gasCall('joinGrade', code); await gradeEntered('학년 공간에 들어왔어요.'); }
  catch (e){ $('#gj-msg').textContent = String((e && e.message) || e).replace(/^.*missing:\s*/, ''); }
  finally { b.disabled = false; }
};
$('#gj-new').onclick = async () => {
  const b = $('#gj-new');
  if (!twoStep(b, '새로 만들까요? 한 번 더')) return;
  b.disabled = true; $('#gj-msg').textContent = '내 드라이브에 학년 공유 기록 시트를 만드는 중…';
  try { await window.__gasCall('createGrade', $('#gj-name').value.trim() || '3학년', +$('#gj-count').value || 4); await gradeEntered('새 학년 공간을 만들었어요. 설정에서 동학년 선생님을 초대해 보세요.'); }
  catch (e){ $('#gj-msg').textContent = '만들지 못했어요. ' + String((e && e.message) || e).slice(0, 120); }
  finally { b.disabled = false; }
};
function inviteLink(){
  const w = window.__gasWho || {}; const base = (w.appUrl && /\/exec$/.test(w.appUrl)) ? w.appUrl : '';
  return base && w.gradeId ? `${base}?g=${w.gradeId}` : '';
}
function renderGradeInvite(){
  const w = window.__gasWho || {};
  $('#gi-cur').textContent = w.sharedOk ? `지금 학년 공간: ${S.settings.gradeName || ''} · ${S.isOwner ? '내가 만든 공간이에요.' : '동학년 선생님이 만든 공간이에요.'}` : '아직 들어간 학년 공간이 없어요.';
  $('#gi-owner').hidden = !(w.sharedOk && S.isOwner);
  $('#gi-link').value = inviteLink();
  $('#gi-link').closest('.row').hidden = !$('#gi-link').value;
}
$('#open-settings').addEventListener('click', () => { if (window.__GAS_MODE) renderGradeInvite(); $$('#gi-box textarea, #gi-box input').forEach(el => { el.disabled = false; }); });
$('#gi-send').onclick = async () => {
  const v = $('#gi-emails').value.trim(); if (!v){ $('#gi-emails').focus(); return; }
  const b = $('#gi-send'); b.disabled = true;
  try {
    const r = await window.__gasCall('inviteGrade', v);
    $('#gi-emails').value = (r.bad || []).join('\n');
    toast(r.ok && r.ok.length ? `${r.ok.length}명을 초대했어요. 초대 링크를 보내 주세요.` : '초대할 구글 계정을 찾지 못했어요.');
    if (r.bad && r.bad.length) toast(`${r.bad.join(', ')} 은(는) 초대하지 못했어요. 주소를 확인해 주세요.`);
  } catch (e){ toast(String((e && e.message) || e).replace(/^.*missing:\s*/, '').slice(0, 120)); }
  finally { b.disabled = false; }
};
$('#gi-copy').onclick = async () => {
  const v = $('#gi-link').value; if (!v) return;
  try { await navigator.clipboard.writeText(v); toast('초대 링크를 복사했어요.'); }
  catch (e){ $('#gi-link').select(); toast('링크를 골라 두었어요. Ctrl+C로 복사해 주세요.'); }
};
window.addEventListener('gas-who', () => { const w = window.__gasWho; if (w && w.deployOk !== false && w.sharedOk === false) gradePickSoon(); });
if (window.__gasNoGrade) gradePickSoon();


/* ---------- 버전 · 바뀐 것 알림 ---------- */
const APP_VERSION = '2.15';
const CHANGELOG = [
  ['2.15', '11월 19일', [
    '큰 모니터에서 학년 첫 화면 맨 위 칸이 얇아졌어요. "끝낼 일"이 오늘 학년 일정 아래 한 줄로 붙고, 가까운 3개만 보여요. 나머지는 "+n개 더"를 누르면 할 일 탭에서 봐요.',
    '큰 모니터 학년 첫 화면: 오늘 일정은 맨 위에 보여서 가운데 "그날 일정" 칸은 숨겼어요. 달력에서 다른 날을 누르면 다시 나와요. "학년 참고사항"은 입력 칸 아래로 옮겼어요.',
    '수업자료: 과목을 고르면 단원별 칸이 생겨요. 학기마다 목차를 한 번 넣어 두면 동학년 모두에게 단원 칸이 보이고, 칸마다 자료를 넣을 수 있어요.',
    '새로고침해도 학년 공간 첫 화면이 아니라 보던 탭으로 돌아와요.',
    '예산: 줄마다 메모 칸과 산출내역 칸이 생기고, 비어 있는 에듀파인 칸(세부사업·원가통계비목)은 숨겨요. 학급 줄은 "반마다"를 누르면 반별 줄로 나눠져요.',
    '나의 공간 학생별: 왼쪽에 학생 이름이 두 줄(앞 번호 절반은 왼쪽, 뒤 절반은 오른쪽)로 있고, 누르면 오른쪽에 그 학생 카드와 누가기록이 한눈에 보이는 폭으로 나와요.',
    '알림장 제목 날짜를 내일이 아니라 쓰는 날(오늘)로 바꿨어요. 1번 시간표와 준비물은 그대로 다음 등교일 것이에요.',
    '할 일을 매주·매월 반복할 수 있어요. "매주 금요일 주간학습 안내 올리기", "매월 말일 출석부 마감"처럼 적거나, 학년 할 일 "고치기"에서 반복을 고르면 돼요. 끝내면 다음 차례가 저절로 생겨요.',
    '나의 공간에 "평가" 탭이 생겼어요. 평가 계획 한글 파일(.hwpx)을 올리면 과목·시기·단원·평가 요소가 원래 문서 순서대로 간단한 표로 정리되고, 줄을 누르면 성취기준과 성취수준이 펼쳐져요. 끝낸 평가는 체크하면 목록에서 빠지고, 이번 달 평가만 골라 보거나 직접 넣고 고칠 수도 있어요. 사진으로 올리기도 그대로 돼요.',
    '아침 안내 오늘 할 일에 긴 글(200자까지)을 쓰면 두세 줄로 넘어가요.',
    '위쪽에 "사용 안내" 버튼이 생겼어요. 누르면 화면 사진으로 된 안내서가 새 창으로 열려요. 동학년 선생님께 처음 쓰는 법을 알려 줄 때 써 보세요.',
    '수업자료 단원: 학년 진도표(한글 .hwp·.hwpx)를 "진도표 올리기"로 올리면 과목마다 "단원명" 칸을 읽어 단원 목차가 한 번에 들어가요. 3학년 출판사 목차(영어 천재 함순애, 미술 동아출판 포함)는 목록에서 고르기만 하면 돼요.',
    '위쪽 탭 줄 끝 "탭 정리"에서 안 쓰는 탭을 숨기고 ↑↓로 순서를 바꿀 수 있어요. 수업자료 과목 줄 끝 "과목 정리"로 안 쓰는 과목을 숨기거나 순서를 바꿔요. 둘 다 내 화면에만 적용돼요.'
  ]],
  ['2.12', '11월 18일 오후', [
    '큰 모니터에서 나의 공간 다른 탭을 눌러도 내용이 안 보이던 것, 학년 공간 다른 탭에서 입력 칸이 오른쪽에 붙던 것을 고쳤어요. 세 줄 배치는 학년 "오늘"과 나의 공간 "학급일지"에서만 써요.'
  ]],
  ['2.11', '11월 18일 오후', [
    '큰 모니터에서 화면을 양옆 끝까지 넓게 써요. 학년 공간은 달력 · 그날 일정과 넣기 · 공지와 자료가 세 줄로, 나의 공간은 오늘과 우리 학년 · 메모와 학급일지 · 학생 표가 세 줄로 나란히 보여요.',
    '전담 기본 시간표에 한글·엑셀 표를 붙여 넣으면 칸마다 나눠 들어가요. "기본 시간표로 다시 채우기" 버튼이 생겼어요.'
  ]],
  ['2.10', '11월 18일', [
    '교과 전담 선생님용 나의 공간이 생겼어요. 설정 맨 위 "나의 공간 쓰는 방식"에서 "교과 전담"을 고르면 오늘 수업 · 수업일지 · 진도표 · 반별 명렬 · 시간표·시수 탭으로 바뀌어요.',
    '전담 시간표·시수: 기본 시간표를 넣으면 학기 주별 시간표에 쭉 깔리고, 바뀐 주만 고쳐요. 휴일은 빼고 반별 시수를 세어 목표 시수와 비교해요. 한글·엑셀 표를 복사해 붙여 넣으면 칸마다 나눠 들어가요.',
    '전담 수업일지는 한 주 보기로 열리고, "똑같이"를 누르면 같은 학년 다른 반 빈칸에 같은 내용이 들어가요.',
    '나의 공간 첫 페이지 학생 표의 출결 칸에서 질병결석·출석인정결석 등을 바로 골라요.',
    '알림장: 줄 사이에서 Enter를 치면 아래 번호(안전 문구 포함)가 하나씩 밀려요. 그날 고른 안전 문구는 다시 열어도 그대로예요. 시간표의 "융"은 "학"으로 써요.',
    '아침 안내: 과목 옆에 짧은 메모를 쓸 수 있어요. 급식은 시간표 아래로 옮기고 오늘 할 일 칸을 넓혔어요.',
    '수업 계획에서 날짜를 넘기면 시간표도 같이 바뀌어요.'
  ]],
  ['2.09', '11월 17일', [
    '교실 도구에 "알림장"이 생겼어요. 내일 시간표·준비물·학사 일정과 안전 문구를 넣어 알림장을 만들고, 복사해서 학교종이에 붙여 넣어요. 크게 보기도 돼요.',
    '학년 공간에 "특별수업" 탭이 생겼어요. 강사 수업·검사처럼 반마다 시간을 정하는 일정을 모으고, 전담 시간·다른 수업과 겹치면 알려 줘요. 주간·월간으로 보고 달력에도 나와요.',
    '아침 안내: 점심 줄은 연한 회색, 화면을 넓게, 오늘 할 일은 한 줄에 하나씩, 고치기·사진 붙이기가 돼요.',
    '명부에서 끌어서 고를 때 화면이 따라 내려가요. 위쪽 교무수첩 아이콘이 바뀌었어요.'
  ]],
  ['2.08', '11월 17일', [
    '위쪽 탭 이름을 바꿀 수 있어요. 탭을 오른쪽 클릭하거나 두 번 누르면 돼요 (학년 탭은 학년 모두에게, 나의 공간 탭은 나에게만).',
    '이제 화면은 GitHub에서 자동으로 최신판을 받아 와요. 화면을 고칠 때마다 붙여 넣고 배포하지 않아도 돼요.',
    '화면이 제대로 안 뜨면 아래에 원인 메시지가 나와요. 캡처해서 보내 주세요.'
  ]],
  ['2.07', '11월 16일 오후', [
    '운영자료·나의 자료·공지·댓글·할 일 메모·학급일지 기록·자주 쓰는 문구에 적은 주소를 누르면 바로 열려요. 메모는 아래에 링크가 따로 생겨요.',
    '나의 공간 "자료" 탭을 맨 뒤로 옮겼어요.'
  ]],
  ['2.06', '11월 16일 오후', [
    '운영자료: 긴 글·주소가 옆 칸과 겹치지 않고 카드 안에서 스크롤돼요. 사진이 있는 자료는 한 줄 전체에 원본 크기로 보여요. 내용 칸에서 Ctrl+V로 사진을 붙여 넣어요.',
    '나의 공간에 "자료" 탭이 생겼어요. 운영자료와 같은 모양이고 나만 봐요.'
  ]],
  ['2.05', '11월 16일 오후', [
    '주소 하나로 다른 학년·다른 학교도 각자 학년 공간을 만들어 써요. 처음 열면 "새로 만들기" 또는 "초대 링크로 들어가기"를 골라요. 설정에서 동학년 선생님을 초대하고 초대 링크를 복사해요.',
    '반 이름: 학년 설정에 "사랑반, 나눔반…"을 넣으면 앱 곳곳에 반 이름으로 보여요. 나의 공간에서 맡은 반을 안 골랐으면 제목 아래에서 고르거나 직접 써요. 제목의 반 이름을 누르면 바꿔요.',
    '메모 "다 했어요"는 지우지 않고 "해결한 메모"에 모아 둬요. 다시 붙이거나 완전히 지울 수 있어요.',
    '교실 도구 아침 안내 시간표: 과목 이름만 크게, 준비물은 옆에 따로 보여요.',
    '학년 첫 화면 "오늘" 칸을 작게 줄이고 급식은 뺐어요. 새로 만든 탭에 "+ 사진 칸" 버튼이 생겼어요.'
  ]],
  ['2.04', '11월 16일 저녁', [
    '설정 → "새 학년도 시작하기": 지금 기록을 학년도 보관함에 통째로 넣은 뒤, 체크한 것(일정·할 일·공지·명부·학급일지 등)만 비워요. 새 학년도 첫날 이후 일정은 남아요.',
    '설정에서 지난 학년도 보관함을 "열어 보기"하면 그해 달력·공지·학급일지를 예전 모습 그대로 볼 수 있어요 (볼 수만 있고, 위 막대에서 돌아와요).',
    '보관할 때 구글 드라이브에 시트 백업본도 한 부씩 만들어 둬요.'
  ]],
  ['2.03', '11월 16일 저녁', [
    '협의·공지: 종류(동학년협의, 부장회의 전달, 교직원회의, 전학공, 위원회, 연수)로 나눠 보고, 글에 댓글과 투표(여러 개 고르기·마감)를 붙일 수 있어요.',
    '학년 첫 화면 공지는 최근 4개만 깔끔하게(고정 글 먼저, 내용은 두 줄). 나머지와 투표·댓글은 "지난 공지 더 보기"나 협의·공지 탭에서 봐요.',
    '학년 할 일도 일정처럼 색 분류가 저절로 붙어요("…보고서 제출" → 제출). 할 일 목록에서 분류를 바꿀 수 있어요.',
    '자료 탭은 "수업자료"로 이름을 바꾸고 "운영자료" 탭이 새로 생겼어요. 분류별 글·체크리스트·링크·사진·파일(3MB까지)을 올리고, "자주 쓰는 문구"를 복사해 바로 쓸 수 있어요.',
    '할 일 "보류", 내 할 일 분류(#학급 #학년 #학교 #업무 #연수 #개인), 상담 방법(대면·전화·문자), 체험학습 신청 기한 표시가 생겼어요.',
    '나의 공간: 제목 옆 설명 대신 내가 쓰는 한마디 칸, 메모와 입력칸을 나란히 놓고 학생 칸을 위로 올렸어요.'
  ]],
  ['2.02', '11월 16일 오후', [
    '학년 첫 화면: 제목 옆에 이번 학기 남은 등교일과 방학식 D-day가 보여요. "학년 참고사항" 칸이 생겨서 글·표(스프레드시트 색 그대로)·사진을 늘 펼쳐 둘 수 있어요.',
    '학년 달력: 날짜를 누르면 나오는 그날 칸이 입력 칸보다 위에 와요. 학년 공간에서 일일계획·알림장과 첫 화면의 "학년 탭" 칸은 뺐어요.',
    '나의 공간에 "수업 계획" 탭이 생겼어요. 교시별 단원·주제, 수업 활동, 준비물·메모, 되돌아보기를 한 표에서 넓게 써요.',
    '명부: 우리 반 명부와 학년 명부가 같은지 보여 주고, 버튼 하나로 맞추거나 "저절로 맞추기"를 켤 수 있어요. 표를 스프레드시트처럼 끌어서 고르고 복사·붙여넣기·지우기 해요.',
    '교실 도구: 뽑기는 한 번에 여러 명·여자만·남자만, 순서 정하기도 여자만·남자만. 모둠 뽑기에 쓰는 주사위(나온 숫자 빼기 선택)가 생겼어요. 아침 안내의 오늘 할 일 글씨가 커졌어요.'
  ]],
  ['2.01', '11월 16일', [
    '학년 첫 페이지 맨 위가 "끝낼 일"로 바뀌었어요. 학년 할 일과 "제출" 일정이 밀린 일 · 이번 주 · 다음 주로 모이고, 체크하면 끝, "미루기"로 다음 주로 넘겨요.',
    '학년 달력 일정에 사안별 색이 생겼어요 (제출·행사·회의·업무·수업·학부모·출장·휴업). "월 / 주" 보기도 고를 수 있고, 제목이 시간보다 먼저 보여요.',
    '나의 공간 학급일지 위에 "우리 학년" 칸이 생겼어요. 다가오는 학년 일정과 끝낼 일을 여기서도 보고 체크해요.',
    '학급일지에 학생 이름만 적어도 학생 카드로 모여요. "행발 김지한 …"처럼 적으면 학생 카드의 행발 누가기록에 쌓여요.',
    '교실 도구에 "아침 안내"가 생겼어요. 오늘 시간표·급식·매일 할 일을 교실 화면에 띄우고 체크해요.',
    '통합 검색(위쪽 "검색" 또는 Ctrl+K), 평가 계획 붙여넣기, 주간 수업일지, 칠판 모드, 예산·명부 탭, 자료 링크 과목별 페이지가 들어왔어요.',
    '구글 버전: 내 구글 캘린더로 고른 일정만 보내기, 나이스 급식·학사일정, 계정 바꾸기 버튼.'
  ]]
];
function newsHtml(list){ return `<ul class="news-l">${list.map(t => `<li>${esc(t)}</li>`).join('')}</ul>`; }
function openNews(){
  const [v, d, list] = CHANGELOG[0];
  $('#news-h').textContent = `버전 ${v} · ${d}에 바뀐 것`;
  $('#news-body').innerHTML = newsHtml(list);
  const old = CHANGELOG.slice(1);
  $('#news-old').innerHTML = old.map(([ov, od, ol]) => `<h4>버전 ${ov} · ${od}</h4>${newsHtml(ol)}`).join('');
  $('.news-old').hidden = !old.length;
  openDlg('#dlg-news');
}
function seenNews(){
  try { localStorage.setItem('seenVersion', APP_VERSION); } catch (e){}
  if (S.db && S.uid && S.profile.seenVersion !== APP_VERSION){ S.profile.seenVersion = APP_VERSION; saveProfile(); }
}
$('#news-ok').onclick = () => { seenNews(); closeDlgs(); };
$('#ver-btn').textContent = 'v' + APP_VERSION;
$('#ver-btn').onclick = openNews;
let newsChecked = false;
function maybeShowNews(){
  if (S.arc) return;
  if (newsChecked || window.__NO_NEWS) return;
  let ls = null; try { ls = localStorage.getItem('seenVersion'); } catch (e){}
  if (ls === APP_VERSION){ newsChecked = true; return; }
  if (S.uid && !S.profileLoaded) return;
  newsChecked = true;
  if (S.profile.seenVersion === APP_VERSION){ try { localStorage.setItem('seenVersion', APP_VERSION); } catch (e){} return; }
  if (!$$('.overlay').some(o => !o.hidden)) openNews();
}


/* ---------- 수업 계획 (크게 쓰는 페이지) ---------- */
/* 날짜를 넘기기 전에 쓰던 칸을 마무리해요 (사파리는 버튼을 눌러도 칸에서 커서가 안 빠져요) */
function blurIn(sel){ const a = document.activeElement; if (a && a.closest && a.closest(sel) && a.blur) a.blur(); }
const PP_F = [['t', '단원 · 주제', '3단원 분수 (2/8차시)', 1], ['a', '수업 활동', '도입 - 전개 - 정리', 1], ['p', '준비물 · 메모', '활동지 25장', 1], ['r', '되돌아보기', '잘된 점, 다음에 챙길 것', 1]];
function renderPlanPage(){
  const k = S.jDate, d = S.day || {};
  $('#pp-label').textContent = fmtLong(k); $('#pp-date').value = k;
  const sf = subjFor(k), tt = sf.s || [];
  $('#pp-src').textContent = sf.off ? `${sf.off} · 수업이 없는 날이에요` : '과목은 시간표에서 가져와요. 칸을 벗어나면 저장되고, 학급일지 첫 페이지의 수업 계획과 같은 기록이에요.';
  $('#pp-ev').innerHTML = schoolEvents(k).map(t => `<span class="chip school">학교 행사 · ${esc(t)}</span>`).join('') + planOn(k).map(it => `<span class="chip">평가 · ${esc(it.name)}</span>`).join('');
  if (document.activeElement && document.activeElement.closest('#pp-rows, #pp-memo')) return;
  const plan = d.plan || [], L = lunchAt();
  let h = `<div class="tablewrap"><table class="pp-t"><thead><tr><th class="n">교시</th><th class="s">과목</th>${PP_F.map(([f, n]) => `<th class="c-${f}">${n}</th>`).join('')}</tr></thead><tbody>`;
  for (let i = 0; i < 6; i++){
    const p = plan[i] || {};
    const subj = p.s !== undefined && p.s !== null ? p.s : expand(tt[i]);
    if (i === L) h += `<tr class="lunch"><td colspan="${PP_F.length + 2}">점심</td></tr>`;
    h += `<tr><td class="n">${i + 1}</td><td class="s"><input id="pp-s-${i}" data-pp-i="${i}" data-pp-f="s" value="${esc(subj || '')}" placeholder="${esc(expand(tt[i]) || '과목')}" aria-label="${i + 1}교시 과목"></td>${PP_F.map(([f, n, ph]) => `<td class="c-${f}"><textarea id="pp-${f}-${i}" data-pp-i="${i}" data-pp-f="${f}" rows="1" placeholder="${i === 0 ? esc(ph) : ''}" aria-label="${i + 1}교시 ${n}">${esc(p[f] || '')}</textarea></td>`).join('')}</tr>`;
  }
  h += '</tbody></table></div>';
  $('#pp-rows').innerHTML = h;
  $$('#pp-rows textarea').forEach(growTa);
  if (document.activeElement !== $('#pp-memo')) $('#pp-memo').value = d.memo || '';
}
function growTa(t){ t.style.height = 'auto'; t.style.height = Math.min(240, t.scrollHeight + 2) + 'px'; }
$('#pp-rows').addEventListener('input', e => { if (e.target.matches('textarea')) growTa(e.target); });
$('#pp-rows').addEventListener('change', e => {
  const el = e.target.closest('[data-pp-f]'); if (!el || !S.uid) return;
  const i = +el.dataset.ppI, f = el.dataset.ppF, k = S.jDate;
  const base = (subjFor(k).s || []).map(expand);
  const plan = ((S.day && S.day.plan) || []).slice(); while (plan.length < 6) plan.push({});
  let v = el.value.replace(/\s+$/, '');
  if (f === 's') v = v.trim() === (base[i] || '') ? null : v.trim();
  plan[i] = Object.assign({}, plan[i] || {}, {[f]:v});
  S.day.plan = plan; saveDay();
  $('#pp-save').textContent = '저장했어요 ' + new Date().toTimeString().slice(0, 5);
});
$('#pp-memo').addEventListener('change', e => { if (!S.uid) return; S.day.memo = e.target.value; saveDay(); $('#pp-save').textContent = '저장했어요 ' + new Date().toTimeString().slice(0, 5); });
$('#p-plan').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#p-plan'))) renderPlanPage(); }, 0));
const ppGo = k => { blurIn('#p-plan'); setJDate(k); renderPlanPage(); };
$('#pp-prev').onclick = () => ppGo(ymd(addDays(fromYmd(S.jDate), -1)));
$('#pp-next').onclick = () => ppGo(ymd(addDays(fromYmd(S.jDate), 1)));
$('#pp-today').onclick = () => ppGo(ymd(today()));
$('#pp-date').addEventListener('change', e => { if (e.target.value) ppGo(e.target.value); });


/* ---------- 나의 공간: 평가 (평가 계획 사진) ---------- */
const EVP = () => `data/users/${S.uid}/evalplan`;
S.ev = {imgs:[], items:[]};
const evSave = () => { if (!S.uid) return; queueSet(EVP(), () => ({imgs:(S.ev.imgs || []).slice(), items:JSON.parse(JSON.stringify(S.ev.items || [])), updatedAt:Date.now()}), false); };
const EV = {subj:'all', when:'all', open:null, edit:null, sort:'subj', showDone:false};
try { const v = localStorage.getItem('evSort'); if (v === 'subj' || v === 'when') EV.sort = v; } catch (e){}
const EV_LV = ['매우 잘함', '잘함', '보통', '노력 요함'];
const evItems = () => (S.ev.items || []);
const evMonth = it => { const m = String(it.when || '').match(/(\d{1,2})\s*월/); return m ? +m[1] : null; };
const evTags = it => (String(it.method || '').match(/\[([^\]]+)\]/g) || []).map(x => x.slice(1, -1)).filter((x, i, a) => a.indexOf(x) === i);
function renderEval(){
  if (S.meTab !== 'eval') return;
  const all = evItems(), im = S.ev.imgs || [];
  $('#ev-photo-n').textContent = im.length ? `${im.length}장` : '';
  if (!all.length && im.length && !$('#ev-photos').open) $('#ev-photos').open = true;
  renderEvPhotos();
  const subs = [...new Set(all.map(x => x.subj || '기타'))];
  if (EV.subj !== 'all' && !subs.includes(EV.subj)) EV.subj = 'all';
  $('#ev-subj').innerHTML = all.length ? [['all', `전체 ${all.length}`]].concat(subs.map(x => [x, `${x} ${all.filter(y => (y.subj || '기타') === x).length}`])).map(([k, n]) => `<button type="button" class="stab" data-evs="${esc(k)}" ${EV.subj === k ? 'aria-current="page"' : ''}>${esc(n)}</button>`).join('') : '';
  $$('#ev-when button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === EV.when));
  const cm = today().getMonth() + 1, nm = cm % 12 + 1;
  const thisN = all.filter(x => evMonth(x) === cm).length;
  const doneN = all.filter(x => x.done).length;
  $('#ev-sum').textContent = all.length ? `남은 평가 ${all.length - doneN}개 · 이번 달(${cm}월) ${all.filter(x => !x.done && evMonth(x) === cm).length}개. 끝낸 평가는 ☐를 눌러 체크해요.` : '';
  $('#ev-done-tg').hidden = !doneN; $('#ev-done-tg').textContent = EV.showDone ? '끝낸 평가 숨기기' : `끝낸 평가 ${doneN}개 보기`;
  let list = all.map((x, i) => Object.assign({_i:i}, x));
  if (EV.subj !== 'all') list = list.filter(x => (x.subj || '기타') === EV.subj);
  if (!EV.showDone) list = list.filter(x => !x.done);
  if (EV.when === 'now') list = list.filter(x => evMonth(x) === cm);
  if (EV.when === 'next') list = list.filter(x => [cm, nm].includes(evMonth(x)));
  const mo = x => { const m = evMonth(x); return m == null ? 99 : (m + 9) % 12; };
  const so = {}; subs.forEach((x, i) => so[x] = i);
  if (EV.sort === 'when') list.sort((a, b) => mo(a) - mo(b) || a._i - b._i);
  else list.sort((a, b) => a._i - b._i);
  $$('#ev-sort button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === EV.sort));
  list.forEach((x, k) => { x._first = k === 0 || (list[k - 1].subj || '기타') !== (x.subj || '기타'); });
  if (!all.length && EV.edit == null){ $('#ev-table').innerHTML = '<div class="jd-empty">평가 계획 한글 파일(.hwpx)을 가져오면 과목·시기·평가 요소가 표로 정리돼요. 위 "한글 파일(.hwpx)에서 가져오기"를 눌러 주세요.<br><small>.hwp 파일이면 한글에서 "다른 이름으로 저장 → HWPX"로 저장한 뒤 올려 주세요.</small></div>'; return; }
  let k0 = 0;
  let h = '<div class="tablewrap"><table class="ev-t"><thead><tr><th class="ck" aria-label="끝냄"></th><th class="n">시기</th><th>과목</th><th>단원</th><th>평가 요소</th><th>방법</th></tr></thead><tbody>';
  if (EV.edit === -1) h += `<tr class="ev-open"><td colspan="6">${evForm({})}</td></tr>`;
  list.forEach(x => {
    const m = evMonth(x), now = m === cm;
    h += `<tr class="ev-row ${x.done ? 'done' : ''} ${now ? 'now' : ''} ${EV.sort === 'subj' && x._first && k0++ ? 'grp' : ''} ${EV.open === x._i ? 'on' : ''}" data-evi="${x._i}" tabindex="0"><td class="ck"><button type="button" class="chk ${x.done ? 'on' : ''}" data-evck="${x._i}" aria-label="${x.done ? '안 끝낸 평가로 되돌리기' : '평가 끝냄'}"></button></td><td class="n">${esc(x.when || '')}</td><td class="sj">${EV.sort === 'subj' && x._first === false ? '' : esc(x.subj || '')}</td><td class="u">${esc(x.unit || '')}</td><td class="el">${esc(x.elem || '')}</td><td class="tg">${evTags(x).map(t => `<span class="chip">${esc(t)}</span>`).join('')}</td></tr>`;
    if (EV.open === x._i){
      h += `<tr class="ev-open"><td colspan="6">${EV.edit === x._i ? evForm(x) : `<div class="ev-det">
        ${x.std ? `<div><b>성취기준</b><p>${esc(x.std)}</p></div>` : ''}
        ${x.method ? `<div><b>수업·평가 방법</b><p>${esc(x.method)}</p></div>` : ''}
        ${(x.levels || []).length ? `<div><b>성취수준</b><table class="ev-lv">${x.levels.map(([n, t]) => `<tr><th>${esc(n)}</th><td>${esc(t)}</td></tr>`).join('')}</table></div>` : x.lvText ? `<div><b>성취수준</b><p>${esc(x.lvText)}</p></div>` : ''}
        <div class="row"><span class="grow"></span><button type="button" class="btn small" data-evedit="${x._i}">고치기</button><button type="button" class="btn small" data-evrm="${x._i}">지우기</button></div></div>`}</td></tr>`;
    }
  });
  if (!list.length && EV.edit !== -1) h += `<tr><td colspan="6" class="hint" style="text-align:center;padding:14px">${EV.when === 'now' ? '이번 달 남은 평가가 없어요.' : doneN && !EV.showDone ? '남은 평가가 없어요. 다 끝냈어요!' : '해당하는 평가가 없어요.'}</td></tr>`;
  $('#ev-table').innerHTML = h + '</tbody></table></div>';
}
function evForm(x){
  const F = (f, n, ta, ph) => `<label class="f" for="evf-${f}">${n}${ta ? `<textarea id="evf-${f}" rows="2" placeholder="${ph || ''}">${esc(x[f] || '')}</textarea>` : `<input id="evf-${f}" value="${esc(x[f] || '')}" placeholder="${ph || ''}">`}</label>`;
  const lv = x.levels && x.levels.length ? x.levels : EV_LV.map(n => [n, '']);
  return `<form class="ev-form" id="ev-form"><div class="jl-grid">${F('subj', '과목', 0, '국어')}${F('when', '평가 시기', 0, '10월')}${F('unit', '단원 (평가영역)', 0, '4. 서로 존중하며 대화해요 (듣기·말하기)')}</div>
    ${F('elem', '평가 요소', 1)}${F('std', '성취기준', 1, '[4국01-04] …')}${F('method', '수업·평가 방법', 1, '[실기][협력적 문제해결력 평가] …')}
    <div><b style="font-size:13px">성취수준</b>${lv.map(([n, t], i) => `<div class="row" style="margin-top:4px"><span style="min-width:70px;font-size:13px">${esc(n)}</span><input id="evf-lv${i}" value="${esc(t)}" style="flex:1" aria-label="${esc(n)}"></div>`).join('')}</div>
    <div class="row" style="margin-top:8px"><span class="grow"></span><button type="button" class="btn" data-evcancel>취소</button><button type="submit" class="btn primary">저장</button></div></form>`;
}
function renderEvPhotos(){
  const im = S.ev.imgs || [];
  $('#ev-list').innerHTML = im.length ? im.map((r, i) => `<figure class="ev-item"><div class="ev-bar"><b>${i + 1}</b><span class="grow"></span><button type="button" class="btn small" data-evmv="-1" data-i="${i}" ${i ? '' : 'disabled'} aria-label="${i + 1}번째 사진 위로">위로</button><button type="button" class="btn small" data-evmv="1" data-i="${i}" ${i < im.length - 1 ? '' : 'disabled'} aria-label="${i + 1}번째 사진 아래로">아래로</button><button type="button" class="btn small" data-evdel="${i}" aria-label="${i + 1}번째 사진 지우기">지우기</button></div><div class="ev-img">${thumbsHtml([r], '')}</div></figure>`).join('')
    : '<p class="hint" style="margin:4px 0">올린 사진이 없어요.</p>';
  hydrateImgs();
}
$('#ev-subj').addEventListener('click', e => { const b = e.target.closest('[data-evs]'); if (!b) return; EV.subj = b.dataset.evs; EV.open = null; EV.edit = null; renderEval(); });
$('#ev-done-tg').onclick = () => { EV.showDone = !EV.showDone; renderEval(); };
$('#ev-sort').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (!b) return; EV.sort = b.dataset.v; try { localStorage.setItem('evSort', EV.sort); } catch (er){} renderEval(); });
$('#ev-when').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (!b) return; EV.when = b.dataset.v; renderEval(); });
$('#ev-new').onclick = () => { if (!S.uid) return; EV.edit = -1; EV.open = null; renderEval(); const f = $('#evf-subj'); if (f){ if (EV.subj !== 'all') f.value = EV.subj; f.focus(); } };
$('#ev-table').addEventListener('click', e => {
  const ck = e.target.closest('[data-evck]');
  if (ck){ if (!S.uid) return; const it = S.ev.items[+ck.dataset.evck]; if (!it) return; it.done = !it.done; it.doneAt = it.done ? Date.now() : null; if (it.done && EV.open === +ck.dataset.evck) EV.open = null; evSave(); renderEval(); if (it.done) toast(`${it.subj} 평가를 끝냈어요.${EV.showDone ? '' : ' 목록에서 숨겼어요.'}`); return; }
  if (e.target.closest('[data-evcancel]')){ EV.edit = null; renderEval(); return; }
  const ed = e.target.closest('[data-evedit]'); if (ed){ EV.edit = +ed.dataset.evedit; renderEval(); return; }
  const rm = e.target.closest('[data-evrm]'); if (rm){ if (!twoStep(rm, '정말 지울까요?')) return; S.ev.items.splice(+rm.dataset.evrm, 1); EV.open = null; evSave(); renderEval(); return; }
  if (e.target.closest('.ev-form')) return;
  const r = e.target.closest('[data-evi]'); if (!r) return;
  const i = +r.dataset.evi; EV.open = EV.open === i ? null : i; EV.edit = null; renderEval();
});
$('#ev-table').addEventListener('keydown', e => { if (e.key === 'Enter' && e.target.matches('[data-evi]')){ e.preventDefault(); e.target.click(); } });
$('#ev-table').addEventListener('submit', e => {
  e.preventDefault(); if (!S.uid) return;
  const g = id => ($('#evf-' + id) || {}).value || '';
  const cur = EV.edit >= 0 ? S.ev.items[EV.edit] || {} : {};
  const lvNames = cur.levels && cur.levels.length ? cur.levels.map(l => l[0]) : EV_LV;
  const it = {subj:g('subj').trim() || '기타', when:g('when').trim(), unit:g('unit').trim(), elem:g('elem').trim(), std:g('std').trim(), method:g('method').trim(), levels:lvNames.map((n, i) => [n, g('lv' + i).trim()]).filter(l => l[1]), lvText:cur.lvText || '', done:!!cur.done, doneAt:cur.doneAt || null};
  if (!it.elem && !it.unit){ toast('단원이나 평가 요소를 적어 주세요.'); return; }
  S.ev.items = S.ev.items || [];
  if (EV.edit >= 0){ S.ev.items[EV.edit] = it; EV.open = EV.edit; } else { S.ev.items.push(it); EV.open = S.ev.items.length - 1; }
  EV.edit = null; evSave(); renderEval(); toast('저장했어요.');
});
/* 한글(.hwpx) 평가 계획 읽기: hwpx는 zip 안에 표가 XML로 들어 있어요 */
async function unzipText(buf, want){
  const dv = new DataView(buf), u8 = new Uint8Array(buf), out = {};
  let e = buf.byteLength - 22; while (e >= 0 && dv.getUint32(e, true) !== 0x06054b50) e--;
  if (e < 0) throw new Error('zip');
  let p = dv.getUint32(e + 16, true); const n = dv.getUint16(e + 10, true), td = new TextDecoder();
  for (let k = 0; k < n; k++){
    if (dv.getUint32(p, true) !== 0x02014b50) break;
    const method = dv.getUint16(p + 10, true), csize = dv.getUint32(p + 20, true), nl = dv.getUint16(p + 28, true), xl = dv.getUint16(p + 30, true), cl = dv.getUint16(p + 32, true), off = dv.getUint32(p + 42, true);
    const name = td.decode(u8.subarray(p + 46, p + 46 + nl)); p += 46 + nl + xl + cl;
    if (!want(name)) continue;
    const ds = off + 30 + dv.getUint16(off + 26, true) + dv.getUint16(off + 28, true), data = u8.subarray(ds, ds + csize);
    out[name] = method === 0 ? td.decode(data) : await new Response(new Blob([data]).stream().pipeThrough(new DecompressionStream('deflate-raw'))).text();
  }
  return out;
}
function evParseXml(xmls){
  const items = []; let subj = '';
  const lname = el => el.localName;
  const kids = (el, n) => [...el.children].filter(c => lname(c) === n);
  const cellText = tc => [...tc.getElementsByTagNameNS('*', 'p')].map(p => [...p.getElementsByTagNameNS('*', 't')].map(t => t.textContent).join('')).map(x => x.replace(/\s+/g, ' ').trim()).filter(Boolean).join(' ').trim();
  xmls.forEach(xml => {
    const doc = new DOMParser().parseFromString(xml, 'application/xml');
    [...doc.getElementsByTagNameNS('*', 'tbl')].forEach(tbl => {
      const rows = kids(tbl, 'tr').map(tr => kids(tr, 'tc').map(tc => { const a = kids(tc, 'cellAddr')[0], sp = kids(tc, 'cellSpan')[0]; return {c:+(a && a.getAttribute('colAddr') || 0), rs:+(sp && sp.getAttribute('rowSpan') || 1), t:cellText(tc)}; }));
      if (!rows.length) return;
      if (rows.length === 1){ const t = rows[0].map(c => c.t).join(' '); const m = t.match(/\d\s*학년\s*\d\s*학기\s*(.+)$/); if (m) subj = m[1].trim(); return; }
      const head = rows[0], col = re => (head.find(c => re.test(c.t.replace(/\s/g, ''))) || {}).c;
      const cE = col(/평가요소/); if (cE == null) return;
      const cS = col(/성취기준/), cU = col(/단원|평가영역/), cM = col(/방법/), cL = col(/성취수준/), cW = col(/시기/);
      const at = (r, c) => (c == null ? '' : ((r.find(x => x.c === c) || {}).t || ''));
      let cur = null;
      rows.slice(1).forEach(r => {
        const starts = r.some(x => x.c === cE);
        if (starts){
          cur = {subj:subj || '기타', std:at(r, cS), unit:at(r, cU), elem:at(r, cE).replace(/^▪\s*/, '').replace(/\s▪\s*/g, ' · '), method:at(r, cM).replace(/^▪\s*/, '').replace(/\s▪\s*/g, ' · '), when:at(r, cW), levels:[], lvText:''};
          items.push(cur);
        }
        if (!cur || cL == null) return;
        const nm = at(r, cL), tx = at(r, cL + 1);
        if (EV_LV.includes(nm.replace(/\s+/g, ' '))) cur.levels.push([nm, tx]);
        else if (starts && nm) cur.lvText = nm;
      });
    });
  });
  return items;
}
$('#ev-file-btn').onclick = () => { if (!S.uid) return; $('#ev-file').value = ''; $('#ev-file').click(); };
$('#ev-file').addEventListener('change', async e => {
  const f = e.target.files && e.target.files[0]; if (!f) return;
  if (/\.hwp$/i.test(f.name)){ toast('.hwp 파일은 읽을 수 없어요. 한글에서 "다른 이름으로 저장 → HWPX"로 저장한 뒤 올려 주세요.'); return; }
  try {
    const xs = await unzipText(await f.arrayBuffer(), n => /^Contents\/section\d+\.xml$/.test(n));
    const items = evParseXml(Object.keys(xs).sort((a, b) => a.localeCompare(b, 'en', {numeric:true})).map(k => xs[k]));
    if (!items.length){ toast('파일에서 평가 표를 찾지 못했어요. "평가 요소" 칸이 있는 표인지 확인해 주세요.'); return; }
    const had = (S.ev.items || []).length;
    const key = x => `${x.subj}|${x.elem}`, was = {}; (S.ev.items || []).forEach(x => { if (x.done) was[key(x)] = x.doneAt || Date.now(); });
    items.forEach(x => { if (was[key(x)]){ x.done = true; x.doneAt = was[key(x)]; } });
    S.ev.items = items; EV.subj = 'all'; EV.open = null; EV.edit = null; evSave(); renderEval();
    toast(`${new Set(items.map(x => x.subj)).size}개 과목, ${items.length}개 평가를 가져왔어요.${had ? ' (예전 목록은 바꿨어요)' : ''}`);
  } catch (er){ console.error(er); toast('파일을 읽지 못했어요. 한글에서 HWPX로 다시 저장해 보세요.'); }
});
$('#ev-list').addEventListener('click', async e => {
  if (!S.uid) return;
  const mv = e.target.closest('[data-evmv]'), del = e.target.closest('[data-evdel]');
  const im = S.ev.imgs || [];
  if (mv){ const i = +mv.dataset.i, j = i + +mv.dataset.evmv; if (j < 0 || j >= im.length) return; [im[i], im[j]] = [im[j], im[i]]; evSave(); renderEval(); return; }
  if (del){ if (!twoStep(del, '정말 지울까요?')) return; const r = im.splice(+del.dataset.evdel, 1)[0]; evSave(); renderEval(); if (r) dropImage(r); }
});
$('#p-eval').addEventListener('dragover', e => { if ([...(e.dataTransfer.types || [])].includes('Files')){ e.preventDefault(); } });
$('#p-eval').addEventListener('drop', e => { const f = [...(e.dataTransfer.files || [])].filter(x => /^image\//.test(x.type)); if (!f.length) return; e.preventDefault(); attach('eval', f); });

/* ================= 교과 전담: 시간표·시수, 오늘 수업 ================= */
const JDP = () => `data/users/${S.uid}/jd`;
function jdTermDefault(){
  const d = today(), y = d.getFullYear(), m = d.getMonth() + 1;
  if (m >= 3 && m <= 7) return [`${y}-03-02`, `${y}-07-31`];
  if (m >= 8) return [`${y}-08-17`, `${y + 1}-02-28`];
  return [`${y - 1}-08-17`, `${y}-02-28`];
}
function jdNorm(j){
  j = j || {};
  if (!j.base || typeof j.base !== 'object') j.base = {};
  for (let w = 1; w <= 5; w++){ const a = Array.isArray(j.base[w]) ? j.base[w] : []; j.base[w] = Array.from({length:6}, (_, i) => String(a[i] || '')); }
  if (!j.weeks || typeof j.weeks !== 'object') j.weeks = {};
  if (!j.targets || typeof j.targets !== 'object') j.targets = {};
  if (!j.last || typeof j.last !== 'object') j.last = {};
  const [f, t] = jdTermDefault(); if (!j.from) j.from = f; if (!j.to) j.to = t;
  j.subject = j.subject || '';
  return j;
}
S.jd = jdNorm({});
const jdSave = () => { if (!S.uid) return; queueSet(JDP(), () => JSON.parse(JSON.stringify(Object.assign({}, S.jd, {updatedAt:Date.now()}))), false); };
const jdCls = v => String(v || '').trim();
/* 41 → 4-1 처럼 읽기 좋게 */
const jdLabel = v => { v = jdCls(v); const m = v.match(/^([1-6])([1-9])$/); return m ? `${m[1]}-${m[2]}` : v; };
function jdWeekCells(mon){ const o = S.jd.weeks[mon]; return o && o.c ? o.c : null; }
function jdCell(mon, wd, p){ const c = jdWeekCells(mon); return jdCls(c ? (c[wd] || [])[p] : S.jd.base[wd][p]); }
function jdOff(k){ const d = fromYmd(k), w = d.getDay(); if (w === 0 || w === 6) return '주말'; if (HOLIDAYS[k]) return HOLIDAYS[k]; const o = subjFor(k).off; return o || ''; }
function jdWeeks(){
  const out = []; if (!S.jd.from || !S.jd.to || S.jd.from > S.jd.to) return out;
  let m = fromYmd(mondayOf(S.jd.from)); const end = S.jd.to;
  for (let i = 0; i < 60 && ymd(m) <= end; i++, m = addDays(m, 7)) out.push(ymd(m));
  return out;
}
const jdInTerm = k => k >= S.jd.from && k <= S.jd.to;
/* 주별 반 시수: {mon: {cls: n}} — 학기 밖 날, 쉬는 날은 세지 않아요 */
function jdCount(){
  const per = {}, all = new Set();
  jdWeeks().forEach(mon => {
    const c = {};
    for (let wd = 1; wd <= 5; wd++){
      const k = ymd(addDays(fromYmd(mon), wd - 1)); if (!jdInTerm(k) || jdOff(k)) continue;
      for (let p = 0; p < 6; p++){ const v = jdCell(mon, wd, p); if (v){ c[v] = (c[v] || 0) + 1; all.add(v); } }
    }
    per[mon] = c;
  });
  Object.values(S.jd.base).forEach(a => a.forEach(v => v && all.add(jdCls(v))));
  Object.keys(S.jd.targets).forEach(v => all.add(v));
  const cls = [...all].filter(Boolean).sort((a, b) => a.localeCompare(b, 'ko', {numeric:true}));
  return {per, cls};
}
function renderJTT(){
  if (!$('#p-jtt') || S.meTab !== 'jtt') return;
  const ae = document.activeElement;
  if (ae !== $('#jt-subj')) $('#jt-subj').value = S.jd.subject || '';
  if (ae !== $('#jt-from')) $('#jt-from').value = S.jd.from || '';
  if (ae !== $('#jt-to')) $('#jt-to').value = S.jd.to || '';
  // 기본 시간표
  let b = '<table class="jt-base"><thead><tr><th></th>' + [1, 2, 3, 4, 5].map(w => `<th>${WD[w]}</th>`).join('') + '</tr></thead><tbody>';
  for (let p = 0; p < 6; p++){ b += `<tr><th>${p + 1}교시</th>` + [1, 2, 3, 4, 5].map(w => `<td><input id="jb-${w}-${p}" data-jb="${w},${p}" value="${esc(S.jd.base[w][p])}" aria-label="${WD[w]}요일 ${p + 1}교시 반"></td>`).join('') + '</tr>'; }
  $('#jt-base').innerHTML = b + '</tbody></table>';
  renderJTTWeeks(); renderJTTSum();
}
function renderJTTWeeks(){
  const {per, cls} = jdCount(), tk = ymd(today()), curMon = mondayOf(ymd(today()));
  let h = '<table class="jt-weeks"><thead><tr><th rowspan="2">주</th><th rowspan="2">기간</th><th rowspan="2">확정</th>' + [1, 2, 3, 4, 5].map(w => `<th colspan="6" class="dsep">${WD[w]}</th>`).join('') + (cls.length ? `<th colspan="${cls.length}" class="dsep">이번 주 시수</th>` : '') + '<th rowspan="2"></th></tr><tr>';
  for (let w = 1; w <= 5; w++) for (let p = 0; p < 6; p++) h += `<th class="${p === 0 ? 'dsep' : ''}">${p + 1}</th>`;
  h += cls.map((c, i) => `<th class="${i === 0 ? 'dsep' : ''}">${esc(jdLabel(c))}</th>`).join('') + '</tr></thead><tbody>';
  jdWeeks().forEach((mon, i) => {
    const m0 = fromYmd(mon), fri = addDays(m0, 4), o = S.jd.weeks[mon] || {};
    h += `<tr class="${ymd(fri) < tk ? 'past' : ''}"><td class="wk ${mon === curMon ? 'now' : ''}">${i + 1}</td><td class="wk ${mon === curMon ? 'now' : ''}">${m0.getMonth() + 1}.${m0.getDate()}~${fri.getMonth() + 1}.${fri.getDate()}</td><td><input type="checkbox" data-jok="${mon}" ${o.ok ? 'checked' : ''} aria-label="${i + 1}주 확정"></td>`;
    for (let w = 1; w <= 5; w++){
      const k = ymd(addDays(m0, w - 1)), off = !jdInTerm(k) ? '학기 밖' : jdOff(k);
      for (let p = 0; p < 6; p++){
        const v = jdCell(mon, w, p), chg = o.c && v !== jdCls(S.jd.base[w][p]);
        h += `<td class="${p === 0 ? 'dsep' : ''} ${off ? 'off' : ''} ${chg ? 'chg' : ''}" ${off && p === 0 ? `title="${esc(off)}"` : ''}><input data-jw="${mon},${w},${p}" value="${esc(v)}" aria-label="${i + 1}주 ${WD[w]} ${p + 1}교시"></td>`;
      }
    }
    h += cls.map((c, j) => { const n = (per[mon] || {})[c] || 0; return `<td class="cnt ${n ? '' : 'z'} ${j === 0 ? 'dsep' : ''}">${n}</td>`; }).join('');
    h += `<td>${o.c ? `<button type="button" class="btn small" data-jreset="${mon}" title="이 주를 기본 시간표로 되돌리기">기본으로</button>` : ''}</td></tr>`;
  });
  $('#jt-weeks').innerHTML = h + '</tbody></table>';
}
function renderJTTSum(){
  const {per, cls} = jdCount(), tk = ymd(today());
  if (!cls.length){ $('#jt-sum').innerHTML = '<p class="hint" style="margin:0">아래 기본 시간표에 반을 적으면 여기서 반별 시수를 세어 줘요.</p>'; return; }
  const sumTo = (c, lim) => { let n = 0; jdWeeks().forEach(mon => { for (let w = 1; w <= 5; w++){ const k = ymd(addDays(fromYmd(mon), w - 1)); if (!jdInTerm(k) || jdOff(k) || (lim && k > lim)) continue; for (let p = 0; p < 6; p++) if (jdCell(mon, w, p) === c) n++; } }); return n; };
  let h = '<table class="jt-sum"><thead><tr><th>반</th><th>목표 시수</th><th>시간표대로 하면</th><th>차이</th><th>오늘까지</th><th>남은 시수</th></tr></thead><tbody>';
  cls.forEach(c => {
    const t = S.jd.targets[c], tot = sumTo(c), done = sumTo(c, tk), tn = t === '' || t == null ? null : +t;
    const diff = tn == null ? '' : tot - tn;
    h += `<tr><td class="cls">${esc(jdLabel(c))}</td><td><input type="number" min="0" max="999" data-jtg="${esc(c)}" value="${tn == null ? '' : tn}" aria-label="${esc(jdLabel(c))} 목표 시수"></td><td>${tot}</td>
      <td class="${diff === '' ? '' : diff === 0 ? 'good' : 'bad'}">${diff === '' ? '' : diff === 0 ? '딱 맞음' : diff > 0 ? `${diff}시간 많음` : `${-diff}시간 모자람`}</td><td>${done}</td><td>${tn == null ? '' : Math.max(0, tn - done)}</td></tr>`;
  });
  $('#jt-sum').innerHTML = h + '</tbody></table>';
}
$('#p-jtt').addEventListener('change', e => {
  const el = e.target; if (!S.uid) return;
  if (el.id === 'jt-subj'){ S.jd.subject = el.value.trim(); jdSave(); renderHeader(); return; }
  if (el.id === 'jt-from' || el.id === 'jt-to'){ if (el.value) S.jd[el.id === 'jt-from' ? 'from' : 'to'] = el.value; jdSave(); renderJTT(); return; }
  if (el.dataset.jb){ const [w, p] = el.dataset.jb.split(',').map(Number); S.jd.base[w][p] = jdCls(el.value); jdSave(); renderJTTWeeks(); renderJTTSum(); return; }
  if (el.dataset.jw){
    const [mon, w, p] = el.dataset.jw.split(','); const o = Object.assign({}, S.jd.weeks[mon] || {});
    const c = o.c ? JSON.parse(JSON.stringify(o.c)) : JSON.parse(JSON.stringify(S.jd.base));
    c[w][+p] = jdCls(el.value);
    const same = [1, 2, 3, 4, 5].every(x => (c[x] || []).every((v, i) => jdCls(v) === jdCls(S.jd.base[x][i])));
    if (same) delete o.c; else o.c = c;
    S.jd.weeks[mon] = o; jdSave();
    const td = el.parentElement; td.classList.toggle('chg', jdCls(el.value) !== jdCls(S.jd.base[w][+p]));
    renderJTTSum(); setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#jt-weeks'))) renderJTTWeeks(); }, 0);
    return;
  }
  if (el.dataset.jok){ const mon = el.dataset.jok; S.jd.weeks[mon] = Object.assign({}, S.jd.weeks[mon] || {}, {ok:el.checked}); jdSave(); return; }
  if (el.dataset.jtg){ const v = el.value.trim(); if (v === '') delete S.jd.targets[el.dataset.jtg]; else S.jd.targets[el.dataset.jtg] = Math.max(0, Math.round(+v) || 0); jdSave(); renderJTTSum(); }
});
$('#jt-weeks').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#jt-weeks'))) renderJTTWeeks(); }, 0));
$('#jt-weeks').addEventListener('click', e => { const b = e.target.closest('[data-jreset]'); if (!b) return; const o = Object.assign({}, S.jd.weeks[b.dataset.jreset] || {}); delete o.c; S.jd.weeks[b.dataset.jreset] = o; jdSave(); renderJTTWeeks(); renderJTTSum(); });
/* 엔터·화살표로 칸 옮기기 */
$('#p-jtt').addEventListener('keydown', e => {
  const el = e.target; if (!(el.dataset && (el.dataset.jw || el.dataset.jb))) return;
  const key = e.key; if (!['Enter', 'ArrowDown', 'ArrowUp', 'ArrowLeft', 'ArrowRight'].includes(key)) return;
  if ((key === 'ArrowLeft' && el.selectionStart > 0) || (key === 'ArrowRight' && el.selectionEnd < el.value.length)) return;
  const tbl = el.closest('table'), cells = [...tbl.querySelectorAll('input[data-jw],input[data-jb]')];
  const tr = el.closest('tr'), rows = [...tbl.querySelectorAll('tbody tr')], ri = rows.indexOf(tr), ci = [...tr.querySelectorAll('input[data-jw],input[data-jb]')].indexOf(el);
  let t = null;
  if (key === 'ArrowLeft') t = cells[cells.indexOf(el) - 1];
  else if (key === 'ArrowRight') t = cells[cells.indexOf(el) + 1];
  else { const r = rows[ri + (key === 'ArrowUp' ? -1 : 1)]; if (r) t = r.querySelectorAll('input[data-jw],input[data-jb]')[ci]; }
  if (t){ e.preventDefault(); t.focus(); t.select(); }
});
/* 한글·엑셀 표를 기본 시간표에 붙여 넣기: 칸마다 나눠 넣어요 */
function jdGridFromClip(cd){
  const html = cd.getData('text/html') || '', text = cd.getData('text/plain') || '';
  let rows = [];
  if (/<table/i.test(html)){
    const doc = new DOMParser().parseFromString(html, 'text/html'), t = doc.querySelector('table');
    rows = [...t.querySelectorAll('tr')].map(tr => [...tr.children].filter(c => /^T[DH]$/.test(c.tagName)).map(c => { const v = (c.innerText || c.textContent || '').replace(/\s+/g, ' ').trim(); const span = +c.getAttribute('colspan') || 1; return Array(span).fill(v); }).flat());
  } else if (text.includes('\t') || text.trim().includes('\n')){
    rows = text.replace(/\r/g, '').replace(/\n+$/, '').split('\n').map(l => l.split('\t').map(x => x.replace(/\s+/g, ' ').trim()));
  }
  rows = rows.filter(r => r.some(Boolean));
  return rows.length > 1 || (rows[0] && rows[0].length > 1) ? rows : null;
}
$('#jt-base').addEventListener('paste', e => {
  const el = e.target.closest('[data-jb]'); if (!el || !S.uid) return;
  const g = jdGridFromClip(e.clipboardData); if (!g) return;
  e.preventDefault();
  const DAYS = {'월':1, '화':2, '수':3, '목':4, '금':5};
  const dayOf = v => { const m = String(v).match(/^([월화수목금])(요일)?$/); return m ? DAYS[m[1]] : 0; };
  let colDay = null, r0 = 0;
  const hi = g.findIndex(r => r.filter(v => dayOf(v)).length >= 3);
  if (hi >= 0){ colDay = g[hi].map(dayOf); r0 = hi + 1; }
  const body = g.slice(r0);
  const perOf = v => { const m = String(v).match(/^(\d)\s*(교시)?$/); return m ? +m[1] : 0; };
  const hasPerCol = body.filter(r => perOf(r[0])).length >= Math.min(3, body.length);
  const [w0, p0] = el.dataset.jb.split(',').map(Number);
  let n = 0;
  body.forEach((r, ri) => {
    const p = hasPerCol ? perOf(r[0]) - 1 : (colDay ? ri : p0 - 0 + ri);
    if (p < 0 || p > 5) return;
    r.forEach((v, ci) => {
      if (hasPerCol && ci === 0) return;
      const w = colDay ? colDay[ci] : w0 + ci - (hasPerCol ? 1 : 0);
      if (!w || w < 1 || w > 5) return;
      S.jd.base[w][p] = jdCls(v).slice(0, 20); n++;
    });
  });
  if (!n){ toast('표에서 반을 찾지 못했어요. 요일 줄과 교시 칸까지 함께 복사해 보세요.'); return; }
  jdSave(); renderJTT(); toast(`기본 시간표 ${n}칸을 채웠어요. 주별 시간표에도 그대로 깔렸어요.`);
});
$('#jt-refill').onclick = e => {
  if (!S.uid) return;
  const ch = Object.values(S.jd.weeks).filter(o => o.c).length;
  if (ch && !twoStep(e.currentTarget, `고친 ${ch}주를 기본으로 되돌릴까요?`)) return;
  Object.keys(S.jd.weeks).forEach(m => { const o = Object.assign({}, S.jd.weeks[m]); delete o.c; S.jd.weeks[m] = o; });
  jdSave(); renderJTT(); toast('학기 전체를 기본 시간표로 채웠어요. 바뀐 주만 칸을 고치면 돼요.');
};
/* 스프레드시트 붙여 넣기 */
$('#jt-paste-open').onclick = () => { $('#jt-paste').hidden = false; $('#jt-paste-txt').focus(); };
$('#jt-paste-cancel').onclick = () => { $('#jt-paste').hidden = true; };
function jdParseSheet(text){
  const rows = String(text || '').replace(/\r/g, '').split('\n').map(l => l.split('\t'));
  const hi = rows.findIndex(r => r.filter(x => /^[1-7]$/.test(x.trim())).length >= 12);
  if (hi < 0) return {err:'교시 번호 줄(1 2 3 4 5 6 1 2 …)을 찾지 못했어요. 그 줄부터 함께 복사해 주세요.'};
  const map = []; let day = 0, prev = 99;
  rows[hi].forEach((x, ci) => { const n = +x.trim(); if (!/^[1-7]$/.test(x.trim())) return; if (n <= prev) day++; prev = n; if (day >= 1 && day <= 5 && n <= 6) map.push([ci, day, n - 1]); });
  const now = today(), sy = now.getMonth() + 1 >= 3 ? now.getFullYear() : now.getFullYear() - 1;
  const weeks = {}; let first = null, last = null;
  rows.slice(hi + 1).forEach(r => {
    const di = r.findIndex(x => /^\s*\d{1,2}\s*\.\s*\d{1,2}\s*-/.test(x)); if (di < 0) return;
    const m = r[di].match(/(\d{1,2})\s*\.\s*(\d{1,2})/); const mo = +m[1], dd = +m[2];
    const d = new Date(mo >= 3 ? sy : sy + 1, mo - 1, dd); const mon = mondayOf(ymd(d));
    const c = {1:['', '', '', '', '', ''], 2:['', '', '', '', '', ''], 3:['', '', '', '', '', ''], 4:['', '', '', '', '', ''], 5:['', '', '', '', '', '']};
    map.forEach(([ci, w, p]) => { c[w][p] = jdCls(r[ci]); });
    const ok = r.slice(di + 1, di + 3).some(x => /^(TRUE|true|✔|✓|o|O|확정)$/.test(x.trim()));
    weeks[mon] = {c, ok}; if (!first || mon < first) first = mon; if (!last || mon > last) last = mon;
  });
  if (!first) return {err:'"3. 9- 3.13"처럼 기간이 적힌 줄을 찾지 못했어요.'};
  // 기본 시간표 = 칸마다 가장 많이 나온 반
  const base = {};
  for (let w = 1; w <= 5; w++){ base[w] = []; for (let p = 0; p < 6; p++){ const cnt = {}; Object.values(weeks).forEach(o => { const v = o.c[w][p]; cnt[v] = (cnt[v] || 0) + 1; }); base[w][p] = Object.entries(cnt).sort((a, b) => b[1] - a[1])[0][0]; } }
  return {weeks, base, first, last};
}
$('#jt-paste-txt').addEventListener('input', () => { const r = jdParseSheet($('#jt-paste-txt').value); $('#jt-paste-info').textContent = r.err || `${Object.keys(r.weeks).length}주를 찾았어요 (${fmtMD(r.first)} 주 ~ ${fmtMD(r.last)} 주).`; });
$('#jt-paste-go').onclick = () => {
  if (!S.uid){ toast('로그인한 상태로 열어야 쓸 수 있어요.'); return; }
  const r = jdParseSheet($('#jt-paste-txt').value); if (r.err){ toast(r.err); return; }
  S.jd.base = r.base; S.jd.weeks = {};
  Object.entries(r.weeks).forEach(([mon, o]) => { const same = [1, 2, 3, 4, 5].every(w => o.c[w].every((v, i) => v === r.base[w][i])); S.jd.weeks[mon] = same ? {ok:o.ok} : o; });
  S.jd.from = r.first; S.jd.to = ymd(addDays(fromYmd(r.last), 4));
  jdSave(); $('#jt-paste').hidden = true; $('#jt-paste-txt').value = ''; $('#jt-paste-info').textContent = '';
  renderJTT(); toast(`${Object.keys(r.weeks).length}주 시간표를 넣었어요.`);
};

/* ---------- 오늘 수업 ---------- */
function jdDayClasses(k){
  const w = fromYmd(k).getDay(); if (w < 1 || w > 5 || !jdInTerm(k)) return [];
  const mon = mondayOf(k);
  return Array.from({length:6}, (_, p) => jdCell(mon, w, p));
}
function renderJDay(){
  if (S.meTab !== 'jday') return;
  const k = S.jDate, d = S.day || {}, log = d.jd || {};
  $('#jd-label').textContent = fmtLong(k); $('#jd-date').value = k;
  const off = jdOff(k);
  $('#jd-ev').innerHTML = (off && off !== '주말' ? `<span class="chip school">쉬는 날 · ${esc(off)}</span>` : '') + schoolEvents(k).map(t => `<span class="chip school">학교 행사 · ${esc(t)}</span>`).join('');
  if (document.activeElement && document.activeElement.closest('#jd-cards, #jd-memo')) return;
  if (document.activeElement !== $('#jd-memo')) $('#jd-memo').value = d.memo || '';
  const cls = jdDayClasses(k), has = cls.some(Boolean);
  if (!has){
    const noTT = !Object.values(S.jd.base).some(a => a.some(Boolean)) && !Object.keys(S.jd.weeks).length;
    $('#jd-cards').innerHTML = `<div class="jd-empty">${noTT ? '먼저 <a href="#me-jtt">시간표·시수</a>에 전담 시간표를 넣어 주세요. 그러면 날마다 들어갈 반이 여기 차례로 떠요.' : off ? `${esc(off)}이라 수업이 없어요.` : '이 날은 들어가는 수업이 없어요.'}</div>`;
    return;
  }
  $('#jd-cards').innerHTML = cls.map((c, p) => {
    if (!c) return '';
    const L = log[p + 1] || {}, last = S.jd.last[c];
    const showLast = last && last.date < k;
    return `<div class="jd-card ${L.done ? 'done' : ''} ${off ? 'off' : ''}">
      <div class="pn">${p + 1}교시</div>
      <div class="cl">${esc(jdLabel(c))}${L.c && L.c !== c ? `<small>원래 ${esc(jdLabel(L.c))}</small>` : ''}</div>
      <div class="bd">
        ${jlCardLine(c, L)}
        ${showLast ? `<div class="last">지난 시간 <b>${fmtMD(last.date)}</b> · ${esc(last.t || '(내용 없음)')}${last.n ? ` · <span style="color:var(--warn)">${esc(last.n)}</span>` : ''}</div>` : ''}
        <textarea rows="1" data-jdf="t" data-jdp="${p + 1}" data-jdc="${esc(c)}" placeholder="오늘 한 내용 · 진도 (예: 피구 규칙 익히기, 2/4차시)" aria-label="${p + 1}교시 ${esc(jdLabel(c))} 수업 내용">${esc(L.t || '')}</textarea>
        <div class="row"><input type="text" data-jdf="n" data-jdp="${p + 1}" data-jdc="${esc(c)}" value="${esc(L.n || '')}" placeholder="특이사항 (예: 김○○ 준비물 안 가져옴)" aria-label="${p + 1}교시 특이사항" style="flex:1">
        <label class="row" style="gap:4px;white-space:nowrap"><input type="checkbox" data-jdf="done" data-jdp="${p + 1}" data-jdc="${esc(c)}" ${L.done ? 'checked' : ''}> 수업함</label></div>
      </div></div>`;
  }).join('');
  $$('#jd-cards textarea').forEach(growTa);
}
$('#jd-cards').addEventListener('input', e => { if (e.target.matches('textarea')) growTa(e.target); });
const JLW = {days:{}, mon:null, t:0, view:'week'};
function jdDayDoc(k){ if (k === S.jDate && S.day) return S.day; return JLW.days[k] || (JLW.days[k] = {}); }
function jdDayPut(k){ const D = jdDayDoc(k); JLW.days[k] = D; if (k === S.jDate && S.day === D) saveDay(); else queueSet(DAYPATH(k), () => Object.assign({}, D, {date:k}), false); }
/* 한 칸 기록을 고치고 저장 (진도·지난 시간까지 함께) */
function jdLogPut(k, p, c, patch){
  const D = jdDayDoc(k), jd = Object.assign({}, D.jd || {});
  const L = Object.assign({c}, jd[p] || {}, patch); L.c = c;
  if (patch.t && !L.done && k <= ymd(today())) L.done = true;
  jlMarkFromDay(c, k, L);
  jd[p] = L; D.jd = jd; jdDayPut(k);
  const prev = S.jd.last[c];
  if ((L.t || L.n) && k <= ymd(today()) && (!prev || prev.date <= k)){ S.jd.last[c] = {date:k, t:L.t || '', n:L.n || ''}; jdSave(); }
  return L;
}
function jdLogChange(e){
  const el = e.target.closest('[data-jdf]'); if (!el || !S.uid) return;
  const k = el.dataset.k || S.jDate, p = el.dataset.jdp, c = el.dataset.jdc, f = el.dataset.jdf;
  const L = jdLogPut(k, p, c, {[f]:f === 'done' ? el.checked : el.value.trim()});
  const tm = '저장했어요 ' + new Date().toTimeString().slice(0, 5); $('#jd-save').textContent = tm; $('#jl-save').textContent = tm;
  if (f === 'done') { renderJDay(); renderJLes(true); }
  else { const card = el.closest('.jd-card, tr'); if (card) card.classList.toggle('done', !!L.done); const cb = card && card.querySelector('[data-jdf="done"]'); if (cb) cb.checked = !!L.done; }
}
$('#jd-cards').addEventListener('change', jdLogChange);
$('#jd-memo').addEventListener('change', e => { if (!S.uid) return; S.day.memo = e.target.value; saveDay(); $('#jd-save').textContent = '저장했어요 ' + new Date().toTimeString().slice(0, 5); });
$('#p-jday').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#jd-cards, #jd-memo'))) renderJDay(); }, 0));
const jdGo = k => { blurIn('#p-jday'); setJDate(k); renderJDay(); };
$('#jd-prev').onclick = () => jdGo(ymd(addDays(fromYmd(S.jDate), -1)));
$('#jd-next').onclick = () => jdGo(ymd(addDays(fromYmd(S.jDate), 1)));
$('#jd-today').onclick = () => jdGo(ymd(today()));
$('#jd-date').addEventListener('change', e => { if (e.target.value) jdGo(e.target.value); });
$('#st-role').addEventListener('change', e => { if (!S.uid || (e.target.value === 'jd') === isJD()) return; closeDlgs(); setRole(e.target.value); });
$('#cls-ask-jd').onclick = () => setRole(isJD() ? '' : 'jd');
function setRole(to){
  if (!S.uid) return;
  S.profile.role = to; if (to) S.profile.myClass = S.profile.myClass || '';
  saveProfile(); S.clsAsk = !to && !S.profile.myClass; renderHeader(); applyRoute('me'); try { history.replaceState(null, '', '#me'); } catch (e){}
  toast(to ? '전담 모드로 바꿨어요. 나의 공간 시간표·시수 탭에 전담 시간표를 넣어 주세요.' : '담임 모드로 바꿨어요.');
}


/* ---------- 전담: 학년 · 차시 수업일지 ---------- */
const JLP = () => `data/users/${S.uid}/jdles`;
const JCP = () => `data/users/${S.uid}/jdcls`;
function jlNorm(j){ j = j || {}; if (!j.g || typeof j.g !== 'object') j.g = {}; Object.values(j.g).forEach(g => { if (!Array.isArray(g.list)) g.list = []; g.list.forEach(x => { if (!x.done || typeof x.done !== 'object') x.done = {}; }); }); return j; }
S.jl = jlNorm({}); S.jc = {c:{}};
const jlSave = () => { if (!S.uid) return; queueSet(JLP(), () => JSON.parse(JSON.stringify(Object.assign({}, S.jl, {updatedAt:Date.now()}))), false); };
const jcSave = () => { if (!S.uid) return; queueSet(JCP(), () => JSON.parse(JSON.stringify(Object.assign({}, S.jc, {updatedAt:Date.now()}))), false); };
const jdMD = k => { const d = fromYmd(k); return `${d.getMonth() + 1}/${d.getDate()}`; };
const jdGrade = c => { const m = jdLabel(c).match(/^(\d)/); return m ? m[1] : '기타'; };
function jdAllCls(){ return jdCount().cls; }
function jdGrades(){ const gs = new Set(jdAllCls().map(jdGrade)); Object.keys(S.jl.g).forEach(g => gs.add(g)); return [...gs].sort((a, b) => a.localeCompare(b, 'ko', {numeric:true})); }
const jdGradeCls = g => jdAllCls().filter(c => jdGrade(c) === g);
const jlList = g => ((S.jl.g[g] || {}).list) || [];
function jlNext(c){ return jlList(jdGrade(c)).find(x => !x.done[c]) || null; }
const jlTitle = x => `${x.u ? x.u + ' · ' : ''}${x.k || ''}${x.q ? ' · ' + x.q : ''}`;
function jlCardLine(c, L){
  const les = L.les && jlList(jdGrade(c)).find(x => x.id === L.les);
  const x = les || jlNext(c); if (!x) return jlList(jdGrade(c)).length ? '<div class="last">이 반은 넣어 둔 차시를 다 했어요.</div>' : '';
  const extra = [x.pg ? `${x.pg}쪽` : '', x.prep ? `준비물 ${x.prep}` : '', x.hw ? `과제 ${x.hw}` : ''].filter(Boolean).join(' · ');
  return `<div class="last" style="color:var(--fg)">${les ? '오늘 한 차시' : '다음 차시'} <b>${esc(jlTitle(x))}</b>${extra ? ` <span style="color:var(--muted)">· ${esc(extra)}</span>` : ''}</div>`;
}
function jlMarkFromDay(c, k, L){
  const list = jlList(jdGrade(c)); if (!list.length) return;
  if (L.done){
    let x = L.les && list.find(y => y.id === L.les);
    if (!x){ x = jlNext(c); if (!x) return; L.les = x.id; }
    x.done[c] = Object.assign({}, x.done[c] || {}, {d:(x.done[c] && x.done[c].d) || k}); if (L.n) x.done[c].n = L.n;
  } else if (L.les){ const x = list.find(y => y.id === L.les); if (x && x.done[c] && x.done[c].d === k) delete x.done[c]; delete L.les; }
  jlSave();
}
function jlCurG(sel){ const gs = jdGrades(); if (!gs.includes(sel)) sel = gs[0] || null; return sel; }
function gradeTabs(el, cur, attr){ const gs = jdGrades(); el.innerHTML = gs.length ? gs.map(g => `<button type="button" class="stab" ${attr}="${esc(g)}" ${g === cur ? 'aria-current="page"' : ''}>${/^\d$/.test(g) ? g + '학년' : esc(g)}</button>`).join('') : ''; }
function jlRow(k, p, c, L, opt){
  const nx = jlNext(c), ph = (L.done || !nx) ? '' : jlTitle(nx);
  const T = f => `<td><textarea rows="1" data-k="${k}" data-jdf="${f}" data-jdp="${p + 1}" data-jdc="${esc(c)}" placeholder="${f === 't' ? esc(ph) : ''}" aria-label="${fmtMD(k)} ${p + 1}교시 ${esc(jdLabel(c))}">${esc(L[f] || '')}</textarea></td>`;
  return `<tr class="${L.done ? 'done' : ''}">${opt.day ? `<td class="n">${opt.day}</td>` : ''}<td class="n">${p + 1}</td><td class="s"><b>${esc(jdLabel(c))}</b></td>${T('t')}${T('a')}${T('pp')}${T('n')}<td class="n"><input type="checkbox" data-k="${k}" data-jdf="done" data-jdp="${p + 1}" data-jdc="${esc(c)}" ${L.done ? 'checked' : ''} aria-label="${p + 1}교시 수업함"></td><td class="n"><button type="button" class="btn small jl-cp" data-jlcp="${k}|${p + 1}|${esc(c)}" title="이 줄 내용을 같은 학년 다른 반 빈칸에 똑같이 넣어요">똑같이</button></td></tr>`;
}
const JL_HEAD = day => `<thead><tr>${day ? '<th class="n">요일</th>' : ''}<th class="n">교시</th><th class="s">반</th><th>단원 · 차시</th><th>수업 활동</th><th>준비물 · 과제</th><th>특이사항</th><th class="n">함</th><th class="n"></th></tr></thead>`;
async function jlLoadWeek(force){
  const mon = mondayOf(S.jDate);
  if (!force && JLW.mon === mon && Date.now() - JLW.t < 60000) return;
  JLW.mon = mon; JLW.t = Date.now();
  const ks = [0, 1, 2, 3, 4].map(i => ymd(addDays(fromYmd(mon), i)));
  await Promise.all(ks.map(async k => { if (k === S.jDate || busy(DAYPATH(k))) return; try { const sn = await S.db.doc(DAYPATH(k)).get(); JLW.days[k] = sn.exists ? JSON.parse(JSON.stringify(sn.data())) : {}; } catch (e){ JLW.days[k] = JLW.days[k] || {}; } }));
}
async function renderJLes(noFetch){
  if (S.meTab !== 'jles') return;
  const wk = JLW.view === 'week', k = S.jDate;
  $$('#jl-view button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === JLW.view));
  $('#jl-memo-wrap').hidden = wk;
  if (wk){ const m = fromYmd(mondayOf(k)), f = addDays(m, 4); $('#jl-label').textContent = `${m.getMonth() + 1}월 ${m.getDate()}일 ~ ${f.getMonth() + 1}월 ${f.getDate()}일`; }
  else $('#jl-label').textContent = fmtLong(k);
  $('#jl-date').value = k;
  if (document.activeElement && document.activeElement.closest('#jl-rows textarea, #jl-memo')) return;
  if (wk && S.db && S.uid && !noFetch){ await jlLoadWeek(false); if (S.meTab !== 'jles' || (document.activeElement && document.activeElement.closest('#jl-rows textarea'))) return; }
  const noTT = !Object.values(S.jd.base).some(a => a.some(Boolean)) && !Object.keys(S.jd.weeks).length;
  if (noTT){ $('#jl-ev').innerHTML = ''; $('#jl-rows').innerHTML = '<div class="jd-empty">먼저 <a href="#me-jtt">시간표·시수</a>에 전담 시간표를 넣어 주세요.</div>'; return; }
  if (wk){
    const mon = mondayOf(k); let h = '', any = false;
    $('#jl-ev').innerHTML = '';
    for (let i = 0; i < 5; i++){
      const dk = ymd(addDays(fromYmd(mon), i)), off = jdOff(dk), cls = jdDayClasses(dk), log = (jdDayDoc(dk).jd) || {}, ev = schoolEvents(dk);
      const lab = `${WD[fromYmd(dk).getDay()]}<br><small>${fromYmd(dk).getMonth() + 1}/${fromYmd(dk).getDate()}</small>`;
      h += `<tr class="jl-dayh ${dk === ymd(today()) ? 'today' : ''}"><td colspan="9"><b>${fmtMD(dk)}</b>${off && off !== '주말' ? ` <span class="chip school">쉬는 날 · ${esc(off)}</span>` : ''}${ev.map(t => ` <span class="chip school">${esc(t)}</span>`).join('')}${!cls.some(Boolean) && !off ? ' <span class="hint">수업 없음</span>' : ''}</td></tr>`;
      if (off) continue;
      cls.forEach((c, p) => { if (c){ any = true; h += jlRow(dk, p, c, log[p + 1] || {}, {day:lab}); } });
    }
    $('#jl-rows').innerHTML = `<div class="tablewrap"><table class="pp-t jl-t">${JL_HEAD(true)}<tbody>${h}</tbody></table></div>`;
  } else {
    const d = S.day || {}, log = d.jd || {}, off = jdOff(k);
    $('#jl-ev').innerHTML = (off && off !== '주말' ? `<span class="chip school">쉬는 날 · ${esc(off)}</span>` : '') + schoolEvents(k).map(t => `<span class="chip school">학교 행사 · ${esc(t)}</span>`).join('');
    if (document.activeElement !== $('#jl-memo')) $('#jl-memo').value = d.memo || '';
    const cls = jdDayClasses(k);
    if (!cls.some(Boolean)){ $('#jl-rows').innerHTML = `<div class="jd-empty">${off ? `${esc(off)}이라 수업이 없어요.` : '이 날은 들어가는 수업이 없어요.'}</div>`; return; }
    const L0 = lunchAt(); let h = '';
    cls.forEach((c, p) => {
      if (p === L0) h += '<tr class="lunch"><td colspan="8">점심</td></tr>';
      if (!c){ h += `<tr class="none"><td class="n">${p + 1}</td><td class="s" colspan="7" style="color:var(--muted)">—</td></tr>`; return; }
      h += jlRow(k, p, c, log[p + 1] || {}, {});
    });
    $('#jl-rows').innerHTML = `<div class="tablewrap"><table class="pp-t jl-t">${JL_HEAD(false)}<tbody>${h}</tbody></table></div>`;
  }
  $$('#jl-rows textarea').forEach(growTa);
}
/* 똑같이: 같은 학년 다른 반의 빈칸에 이 줄 내용을 넣어요 (하루 보기는 그날, 주간 보기는 그 주) */
$('#jl-rows').addEventListener('click', e => {
  const b = e.target.closest('[data-jlcp]'); if (!b || !S.uid) return;
  const [k, p, c] = b.dataset.jlcp.split('|');
  const src = (jdDayDoc(k).jd || {})[p] || {};
  const pick = {t:src.t || '', a:src.a || '', pp:src.pp || ''};
  if (!pick.t && !pick.a && !pick.pp){ toast('먼저 이 줄에 내용을 적어 주세요.'); return; }
  const g = jdGrade(c), days = JLW.view === 'week' ? [0, 1, 2, 3, 4].map(i => ymd(addDays(fromYmd(mondayOf(S.jDate)), i))) : [S.jDate];
  let n = 0; const got = new Set();
  days.forEach(dk => {
    if (jdOff(dk)) return;
    jdDayClasses(dk).forEach((c2, p2) => {
      if (!c2 || c2 === c || jdGrade(c2) !== g || got.has(c2)) return;
      const L = (jdDayDoc(dk).jd || {})[p2 + 1] || {};
      const patch = {}; ['t', 'a', 'pp'].forEach(f => { if (!L[f] && pick[f]) patch[f] = pick[f]; });
      if (!Object.keys(patch).length) return;
      jdLogPut(dk, String(p2 + 1), c2, patch); n++; got.add(c2);
    });
  });
  toast(n ? `같은 학년 ${n}칸에 똑같이 넣었어요.` : '채울 빈칸이 없어요. (같은 학년 다른 반의 빈칸에만 넣어요)');
  renderJLes(true);
});
$('#jl-rows').addEventListener('input', e => { if (e.target.matches('textarea')) growTa(e.target); });
$('#jl-rows').addEventListener('change', jdLogChange);
$('#jl-memo').addEventListener('change', e => { if (!S.uid) return; S.day.memo = e.target.value; saveDay(); $('#jl-save').textContent = '저장했어요 ' + new Date().toTimeString().slice(0, 5); });
$('#p-jles').addEventListener('focusout', () => setTimeout(() => { if (!(document.activeElement && document.activeElement.closest('#jl-rows, #jl-memo'))) renderJLes(true); }, 0));
const jlGo = k => { blurIn('#p-jles'); setJDate(k); renderJLes(); };
$('#jl-prev').onclick = () => jlGo(ymd(addDays(fromYmd(S.jDate), JLW.view === 'week' ? -7 : -1)));
$('#jl-next').onclick = () => jlGo(ymd(addDays(fromYmd(S.jDate), JLW.view === 'week' ? 7 : 1)));
$('#jl-view').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (!b) return; JLW.view = b.dataset.v; try { localStorage.setItem('jlView', JLW.view); } catch (er){} renderJLes(); });
try { const v = localStorage.getItem('jlView'); if (v === 'day' || v === 'week') JLW.view = v; } catch (e){}
$('#jl-today').onclick = () => jlGo(ymd(today()));
$('#jl-date').addEventListener('change', e => { if (e.target.value) jlGo(e.target.value); });
function jlParse(text, g){
  const out = []; let unit = '';
  String(text || '').replace(/\r/g, '').split('\n').forEach(line => {
    if (!line.trim()) return;
    if (line.includes('\t')){
      const c = line.split('\t').map(x => x.trim());
      if (/^(단원|단원명)$/.test(c[0]) || /^(차시|학습\s*문제|학습\s*주제)$/.test(c[1] || '') || /^학습\s*(문제|주제|목표)$/.test(c[2] || '')) return;
      if (c[0]) unit = c[0];
      if (!c[1] && !c[2]) return;
      out.push({u:unit, k:c[1] || '', q:c[2] || '', pg:c[3] || ''});
      return;
    }
    const m = line.trim().match(/^(.*?)[\s(]*(\d{1,2})\s*(차시|시간)?\)?$/);
    if (m && m[1] && +m[2] > 0 && +m[2] <= 20){ unit = m[1].trim(); for (let i = 1; i <= +m[2]; i++) out.push({u:unit, k:`${i}/${m[2]}`, q:'', pg:''}); }
    else { unit = line.trim(); out.push({u:unit, k:'1/1', q:'', pg:''}); }
  });
  return out.map((x, i) => Object.assign({id:'l' + Date.now().toString(36) + i, prep:'', hw:'', flow:'', board:'', done:{}}, x));
}
$('#jl-paste').addEventListener('input', () => { const r = jlParse($('#jl-paste').value); $('#jl-paste-info').textContent = r.length ? `${new Set(r.map(x => x.u)).size}개 단원, ${r.length}개 차시를 찾았어요.` : ''; });
$('#jl-paste-go').onclick = () => {
  if (!S.uid || !JP.g) return;
  const r = jlParse($('#jl-paste').value); if (!r.length){ toast('붙여 넣은 내용이 없어요.'); return; }
  const g = S.jl.g[JP.g] = S.jl.g[JP.g] || {list:[]}; g.list = g.list.concat(r); jlSave();
  $('#jl-paste').value = ''; $('#jl-paste-info').textContent = ''; $('#jl-add').open = false; renderJProg(); toast(`${r.length}개 차시를 넣었어요.`);
};
$('#jl-clear').onclick = e => { if (!S.uid || !JP.g || !jlList(JP.g).length) return; if (!twoStep(e.currentTarget, `${JP.g}학년 차시 목록을 다 지울까요?`)) return; delete S.jl.g[JP.g]; jlSave(); renderJProg(); };

/* ---------- 전담: 진도표 ---------- */
const JP = {g:null, v:'les', month:null};
function renderJProg(){
  if (S.meTab !== 'jprog') return;
  JP.g = jlCurG(JP.g); gradeTabs($('#jp-grades'), JP.g, 'data-jpg');
  $$('#jp-view button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === JP.v));
  $('#jp-les').hidden = JP.v !== 'les'; $('#jp-cal').hidden = JP.v !== 'cal';
  $('#jp-grades').style.visibility = JP.v === 'cal' ? 'hidden' : '';
  if (JP.v === 'cal') return renderJProgCal();
  $('#jl-add').hidden = !JP.g;
  if (!JP.g){ $('#jp-table').innerHTML = '<div class="jd-empty">먼저 <a href="#me-jtt">시간표·시수</a>에 전담 시간표를 넣어 주세요.</div>'; return; }
  const list = jlList(JP.g), cls = jdGradeCls(JP.g);
  if (!list.length){ $('#jp-table').innerHTML = `<div class="jd-empty">${JP.g}학년 차시 목록이 아직 없어요. 위 "단원·차시 목록 넣기"를 열어 붙여 넣으면 반별 진도표가 만들어져요.</div>`; $('#jl-add').open = true; return; }
  const nexts = {}; cls.forEach(c => { const n = jlNext(c); if (n) nexts[c] = n.id; });
  const cnt = c => list.filter(x => x.done[c]).length;
  let h = `<table class="jp-t"><thead><tr><th>단원</th><th>차시</th><th>학습 문제</th>${cls.map(c => `<th>${esc(jdLabel(c))}<br><small>${cnt(c)}/${list.length}</small></th>`).join('')}</tr></thead><tbody>`;
  let pu = null;
  list.forEach(x => {
    h += `<tr><td class="u">${x.u !== pu ? esc(x.u || '') : ''}</td><td>${esc(x.k || '')}</td><td class="q" title="${esc(x.q || '')}">${esc(x.q || '')}</td>${cls.map(c => { const d = x.done[c]; return `<td class="c ${d ? 'on' : ''} ${nexts[c] === x.id ? 'next' : ''}" data-jpc="${x.id}" data-c="${esc(c)}" title="${d && d.n ? esc(d.n) : ''}">${d ? `${fromYmd(d.d).getMonth() + 1}/${fromYmd(d.d).getDate()}` : ''}</td>`; }).join('')}</tr>`;
    pu = x.u;
  });
  $('#jp-table').innerHTML = h + '</tbody></table>';
}
function renderJProgCal(){
  const t = today(); if (!JP.month) JP.month = new Date(t.getFullYear(), t.getMonth(), 1);
  const m = JP.month, y = m.getFullYear(), mo = m.getMonth();
  $('#jpc-label').textContent = `${y}년 ${mo + 1}월`;
  const by = {};
  Object.entries(S.jl.g).forEach(([g, o]) => (o.list || []).forEach(x => Object.entries(x.done || {}).forEach(([c, d]) => { (by[d.d] = by[d.d] || []).push({c, x}); })));
  let h = [1, 2, 3, 4, 5].map(w => `<div class="h">${WD[w]}</div>`).join('');
  let d = fromYmd(mondayOf(ymd(m))); const tk = ymd(t);
  for (let i = 0; i < 6 && (i === 0 || d.getMonth() === mo); i++){
    for (let w = 0; w < 5; w++){
      const k = ymd(addDays(d, w)), dd = addDays(d, w), off = jdOff(k);
      const es = (by[k] || []).sort((a, b) => a.c.localeCompare(b.c, 'ko', {numeric:true}));
      h += `<div class="d ${dd.getMonth() !== mo ? 'out' : ''} ${k === tk ? 'today' : ''}"><div class="n">${dd.getDate()}${off && off !== '주말' ? ` <span style="color:var(--holiday)">${esc(off)}</span>` : ''}</div>${es.map(e => `<div class="e"><b>${esc(jdLabel(e.c))}</b> ${esc(e.x.k || '')} ${esc((e.x.q || e.x.u || '').slice(0, 18))}</div>`).join('')}</div>`;
    }
    d = addDays(d, 7);
  }
  $('#jpc-grid').innerHTML = h;
}
$('#jp-grades').addEventListener('click', e => { const b = e.target.closest('[data-jpg]'); if (!b) return; JP.g = b.dataset.jpg; renderJProg(); });
$('#jp-view').addEventListener('click', e => { const b = e.target.closest('[data-v]'); if (!b) return; JP.v = b.dataset.v; renderJProg(); });
$('#jpc-prev').onclick = () => { JP.month = new Date(JP.month.getFullYear(), JP.month.getMonth() - 1, 1); renderJProgCal(); };
$('#jpc-next').onclick = () => { JP.month = new Date(JP.month.getFullYear(), JP.month.getMonth() + 1, 1); renderJProgCal(); };
$('#jpc-now').onclick = () => { JP.month = null; renderJProgCal(); };
$('#jp-table').addEventListener('click', e => {
  const td = e.target.closest('[data-jpc]'); if (!td || !S.uid) return;
  const x = jlList(JP.g).find(y => y.id === td.dataset.jpc); if (!x) return;
  const c = td.dataset.c; if (x.done[c]) delete x.done[c]; else x.done[c] = {d:ymd(today())};
  jlSave(); renderJProg();
});

/* ---------- 전담: 반별 명렬표 · 누가기록 ---------- */
const JC = {c:null, paste:false};
function jcData(c){ const o = S.jc.c[c] = S.jc.c[c] || {}; if (!Array.isArray(o.st)) o.st = []; if (!Array.isArray(o.cols)) o.cols = []; if (!o.v) o.v = {}; if (!Array.isArray(o.notes)) o.notes = []; return o; }
const JC_CYCLE = ['', 'O', 'X', '△'];
function renderJCls(){
  if (S.meTab !== 'jcls') return;
  const cls = jdAllCls().concat(Object.keys(S.jc.c).filter(c => !jdAllCls().includes(c)));
  if (!cls.includes(JC.c)) JC.c = cls[0] || null;
  $('#jc-tabs').innerHTML = cls.map(c => `<button type="button" class="stab" data-jcc="${esc(c)}" ${c === JC.c ? 'aria-current="page"' : ''}>${esc(jdLabel(c))}</button>`).join('');
  if (!JC.c){ $('#jc-main').innerHTML = '<div class="jd-empty">먼저 <a href="#me-jtt">시간표·시수</a>에 전담 시간표를 넣어 주세요. 시간표에 나온 반마다 명렬표가 생겨요.</div>'; return; }
  const o = jcData(JC.c), st = o.st;
  const ae = document.activeElement;
  let h = `<section class="jt-sec"><div class="row" style="flex-wrap:wrap;gap:8px 14px"><b style="font-size:16px">${esc(jdLabel(JC.c))}</b>
    <label class="row" for="jc-teacher" style="gap:6px">담임 <input id="jc-teacher" value="${esc(o.teacher || '')}" placeholder="선생님 이름" style="width:120px"></label>
    <span class="hint">학생 ${st.length}명</span><span class="grow"></span><button type="button" class="btn small" id="jc-paste-open">${st.length ? '명단 다시 붙여 넣기' : '명단 붙여 넣기'}</button></div>
    <div id="jc-paste" ${JC.paste || !st.length ? '' : 'hidden'} style="margin-top:8px"><p class="hint" style="margin:0 0 4px">한 줄에 한 명씩 붙여 넣어요. "번호[탭]이름"이나 이름만 있어도 돼요. 담임 선생님께 받은 명단을 그대로 복사해 오면 돼요.</p>
    <textarea id="jc-paste-txt" rows="4" placeholder="1	김가나&#10;2	이다라"></textarea><div class="row" style="margin-top:6px"><span class="grow"></span><button type="button" class="btn primary" id="jc-paste-go">명단 넣기</button></div></div></section>`;
  if (st.length){
    h += `<section class="jt-sec"><div class="row" style="flex-wrap:wrap;gap:6px;margin-bottom:8px"><b>체크 · 평가</b><span class="hint">체크 칸은 누를 때마다 O → X → △ → 빈칸으로 바뀌어요.</span><span class="grow"></span>
      <input id="jc-col-name" placeholder="새 칸 이름 (예: 과제 1, 줄넘기 평가)" style="width:220px"><select id="jc-col-type" style="width:auto"><option value="chk">체크</option><option value="txt">글·점수</option></select><button type="button" class="btn small" id="jc-col-add">칸 더하기</button></div>
      <div class="jt-wrap"><table class="jc-t"><thead><tr><th>번호</th><th>이름</th>${o.cols.map(cl => `<th>${esc(cl.name)}<small>${cl.d ? fmtMD(cl.d) : ''} <button type="button" class="x" data-jcdel="${cl.id}" aria-label="${esc(cl.name)} 칸 지우기" style="font-size:11px">×</button></small></th>`).join('')}</tr></thead><tbody>`;
    st.forEach(s0 => { h += `<tr><td>${esc(s0.no)}</td><td class="nm">${esc(s0.name)}</td>${o.cols.map(cl => { const v = (o.v[cl.id] || {})[s0.no] || ''; return cl.t === 'txt' ? `<td><input data-jcv="${cl.id}" data-no="${esc(s0.no)}" value="${esc(v)}" aria-label="${esc(s0.name)} ${esc(cl.name)}"></td>` : `<td><button type="button" class="ck ${v === '△' ? 'T' : v}" data-jck="${cl.id}" data-no="${esc(s0.no)}" aria-label="${esc(s0.name)} ${esc(cl.name)} ${v || '빈칸'}">${esc(v)}</button></td>`; }).join('')}</tr>`; });
    h += `<tr><td colspan="2" class="jc-sum">O / X / 빈칸</td>${o.cols.map(cl => { if (cl.t === 'txt') return '<td></td>'; const vs = st.map(s0 => (o.v[cl.id] || {})[s0.no] || ''); return `<td class="jc-sum">${vs.filter(v => v === 'O').length}/${vs.filter(v => v === 'X').length}/${vs.filter(v => !v).length}</td>`; }).join('')}</tr>`;
    h += '</tbody></table></div></section>';
    h += `<section class="jt-sec"><b>누가기록</b><form id="jc-note-form" class="row" style="flex-wrap:wrap;gap:6px;margin-top:8px"><input type="date" id="jc-note-d" value="${ymd(today())}" style="width:auto" aria-label="날짜"><select id="jc-note-no" style="width:auto" aria-label="학생"><option value="">반 전체</option>${st.map(s0 => `<option value="${esc(s0.no)}">${esc(s0.no)} ${esc(s0.name)}</option>`).join('')}</select><input id="jc-note-t" placeholder="예: 줄넘기 모둠 활동에서 친구를 잘 도와줌" style="flex:1;min-width:200px" aria-label="기록"><button type="submit" class="btn small primary">적기</button></form>
      <div class="jc-notes">${o.notes.slice().sort((a, b) => a.d < b.d ? 1 : a.d > b.d ? -1 : 0).map(n => { const s1 = st.find(s0 => s0.no === n.no); return `<div class="jc-note"><span class="dt">${fmtMD(n.d)}</span><span class="who">${s1 ? esc(s1.no + ' ' + s1.name) : '반 전체'}</span><span class="tx">${esc(n.t)}</span><button type="button" class="x" data-jcnd="${n.id}" aria-label="지우기">×</button></div>`; }).join('') || '<p class="hint" style="margin:4px 0 0">아직 기록이 없어요.</p>'}</div></section>`;
  }
  $('#jc-main').innerHTML = h;
}
$('#jc-tabs').addEventListener('click', e => { const b = e.target.closest('[data-jcc]'); if (!b) return; JC.c = b.dataset.jcc; JC.paste = false; renderJCls(); });
$('#jc-main').addEventListener('click', e => {
  if (!S.uid || !JC.c) return; const o = jcData(JC.c);
  if (e.target.id === 'jc-paste-open'){ JC.paste = true; renderJCls(); $('#jc-paste-txt').focus(); return; }
  if (e.target.id === 'jc-paste-go'){
    const rows = $('#jc-paste-txt').value.replace(/\r/g, '').split('\n').map(l => l.split('\t').map(x => x.trim()).filter(Boolean)).filter(r => r.length);
    let auto = 0; const st = [];
    rows.forEach(r => { let no, name; if (r.length >= 2 && /^\d+$/.test(r[0])){ no = r[0]; name = r[1]; } else { const m = r[0].match(/^(\d+)[.\s]+(.+)$/); if (m){ no = m[1]; name = m[2]; } else { no = String(++auto); name = r[0]; } } if (/^\d+$/.test(no)) auto = Math.max(auto, +no); if (name && !/^(이름|성명|번호)$/.test(name)) st.push({no, name:name.slice(0, 20)}); });
    if (!st.length){ toast('명단을 찾지 못했어요.'); return; }
    o.st = st; JC.paste = false; jcSave(); renderJCls(); toast(`${st.length}명을 넣었어요.`); return;
  }
  if (e.target.id === 'jc-col-add'){ const name = $('#jc-col-name').value.trim(); if (!name){ $('#jc-col-name').focus(); return; } o.cols.push({id:'c' + Date.now().toString(36), name:name.slice(0, 20), t:$('#jc-col-type').value, d:ymd(today())}); jcSave(); renderJCls(); return; }
  const ck = e.target.closest('[data-jck]');
  if (ck){ const m = o.v[ck.dataset.jck] = o.v[ck.dataset.jck] || {}; const v = JC_CYCLE[(JC_CYCLE.indexOf(m[ck.dataset.no] || '') + 1) % JC_CYCLE.length]; if (v) m[ck.dataset.no] = v; else delete m[ck.dataset.no]; jcSave(); renderJCls(); return; }
  const cd = e.target.closest('[data-jcdel]');
  if (cd){ if (!twoStep(cd, '지울까요?')) return; o.cols = o.cols.filter(c => c.id !== cd.dataset.jcdel); delete o.v[cd.dataset.jcdel]; jcSave(); renderJCls(); return; }
  const nd = e.target.closest('[data-jcnd]');
  if (nd){ if (!twoStep(nd, '지울까요?')) return; o.notes = o.notes.filter(n => n.id !== nd.dataset.jcnd); jcSave(); renderJCls(); }
});
$('#jc-main').addEventListener('change', e => {
  if (!S.uid || !JC.c) return; const o = jcData(JC.c);
  if (e.target.id === 'jc-teacher'){ o.teacher = e.target.value.trim().slice(0, 20); jcSave(); return; }
  const v = e.target.closest('[data-jcv]'); if (v){ const m = o.v[v.dataset.jcv] = o.v[v.dataset.jcv] || {}; const t = v.value.trim(); if (t) m[v.dataset.no] = t.slice(0, 40); else delete m[v.dataset.no]; jcSave(); }
});
$('#jc-main').addEventListener('submit', e => {
  if (e.target.id !== 'jc-note-form') return; e.preventDefault(); if (!S.uid || !JC.c) return;
  const t = $('#jc-note-t').value.trim(); if (!t){ $('#jc-note-t').focus(); return; }
  const o = jcData(JC.c); o.notes.push({id:'n' + Date.now().toString(36), d:$('#jc-note-d').value || ymd(today()), no:$('#jc-note-no').value, t:t.slice(0, 300)});
  jcSave(); renderJCls(); $('#jc-note-t').focus();
});
$('#jc-main').addEventListener('focusout', () => setTimeout(() => { const a = document.activeElement; if (!(a && a.closest('#jc-main'))) renderJCls(); }, 0));


/* ---------- 학년 참고사항 (글·표·사진) ---------- */
const GM_TAGS = new Set(['B', 'STRONG', 'I', 'EM', 'U', 'BR', 'P', 'DIV', 'SPAN', 'TABLE', 'THEAD', 'TBODY', 'TR', 'TD', 'TH', 'UL', 'OL', 'LI', 'H3', 'H4', 'COLGROUP', 'COL']);
const GM_CSS = ['background-color', 'color', 'font-weight', 'text-align', 'font-style', 'text-decoration'];
function cleanHtml(html){
  const doc = new DOMParser().parseFromString(`<div>${html || ''}</div>`, 'text/html');
  const walk = node => {
    [...node.childNodes].forEach(ch => {
      if (ch.nodeType === 3) return;
      if (ch.nodeType !== 1){ ch.remove(); return; }
      if (/^(SCRIPT|STYLE|META|LINK|TITLE|IFRAME|OBJECT|EMBED|SVG|MATH|TEMPLATE|NOSCRIPT)$/.test(ch.tagName)){ ch.remove(); return; }
      walk(ch);
      if (!GM_TAGS.has(ch.tagName)){ ch.replaceWith(...ch.childNodes); return; }
      const keep = {};
      if ((ch.tagName === 'TD' || ch.tagName === 'TH')){ ['colspan', 'rowspan'].forEach(a => { const v = ch.getAttribute(a); if (v && /^\d{1,2}$/.test(v)) keep[a] = v; }); }
      const st = ch.getAttribute('style') || '';
      const css = st.split(';').map(x => x.split(':')).filter(([p, v]) => p && v && GM_CSS.includes(p.trim().toLowerCase()) && /^[#a-z0-9(),.\s%-]+$/i.test(v.trim())).map(([p, v]) => `${p.trim().toLowerCase()}:${v.trim()}`).join(';');
      [...ch.attributes].forEach(a => ch.removeAttribute(a.name));
      Object.entries(keep).forEach(([a, v]) => ch.setAttribute(a, v));
      if (css) ch.setAttribute('style', css);
    });
  };
  const root = doc.body.firstChild; walk(root);
  return root.innerHTML;
}
function renderGMemo(){
  const ed = $('#gm-edit'); if (!ed) return;
  const m = S.gmemo || {};
  ed.contentEditable = S.canWrite ? 'true' : 'false';
  if (document.activeElement !== ed && !S.gmDirty) ed.innerHTML = cleanHtml(m.html || '');
  ed.classList.toggle('empty', !ed.textContent.trim() && !ed.querySelector('table'));
  $('#gm-thumbs').innerHTML = thumbsHtml(m.imgs || [], S.canWrite ? 'gmemo' : '');
}
async function saveGMemo(){
  if (!S.gmDirty || !S.canWrite || !S.db) return;
  const html = cleanHtml($('#gm-edit').innerHTML);
  S.gmDirty = false;
  try { await S.db.doc('grade/memo').set(Object.assign({}, S.gmemo || {}, {html, updatedAt:Date.now(), updatedBy:S.uid})); toast('학년 참고사항을 저장했어요.'); }
  catch (e){ S.gmDirty = true; wErr(e, true); }
}
$('#gm-edit').addEventListener('input', () => { S.gmDirty = true; $('#gm-edit').classList.remove('empty'); });
$('#gm-edit').addEventListener('blur', () => { saveGMemo(); });
$('#gm-edit').addEventListener('paste', e => {
  const cd = e.clipboardData; if (!cd) return;
  const html = cd.getData('text/html'), text = cd.getData('text/plain');
  if ([...(cd.files || [])].length && !text) return; // 사진은 아래 사진 칸으로
  e.preventDefault();
  let ins;
  if (html && /<table/i.test(html)) ins = cleanHtml(html.replace(/[\s\S]*?(<table[\s\S]*<\/table>)[\s\S]*/i, '$1'));
  else if (text && /\t/.test(text)) ins = '<table><tbody>' + pasteRows(text).map(r => '<tr>' + r.map(c => `<td>${esc(c)}</td>`).join('') + '</tr>').join('') + '</tbody></table>';
  else ins = esc(text || '').replace(/\n/g, '<br>');
  document.execCommand('insertHTML', false, ins + (/<table/.test(ins) ? '<p><br></p>' : ''));
  S.gmDirty = true;
});


/* ---------- 상담 방법 ---------- */
function cnsWay(t){ t = String(t || ''); if (/방문|대면|면담|내교|만나/.test(t)) return '대면'; if (/전화|통화|콜/.test(t)) return '전화'; if (/문자|하이톡|알림장|메시지|메세지|카톡|e알리미|이알리미|클래스팅/.test(t)) return '문자'; return ''; }

/* ---------- 할 일 분류 ---------- */
const TD_AREAS = ['학급', '학년', '학교', '업무', '연수', '개인'];
const areaOf = p => (p.tags || []).map(t => t.replace(/\s/g, '')).find(t => TD_AREAS.includes(t)) || null;
$('#cns-way').addEventListener('click', e => { const b = e.target.closest('[data-w]'); if (!b) return; S.cnsW = b.dataset.w; renderCns(); });
$('#td-area').addEventListener('click', e => { const b = e.target.closest('[data-area]'); if (!b) return; S.tdArea = b.dataset.area; renderTodo(); });

/* ---------- 공지 종류 ---------- */
const NK = ['공지', '동학년협의', '부장회의 전달', '교직원회의', '전학공', '위원회', '연수', '기타'];
function guessNk(t){ t = String(t || ''); if (/부장/.test(t)) return '부장회의 전달'; if (/전학공|전문적\s*학습/.test(t)) return '전학공'; if (/위원회|학운위|학성위|선도/.test(t)) return '위원회'; if (/연수/.test(t)) return '연수'; if (/교직원|월례|전직원/.test(t)) return '교직원회의'; if (/학년\s*(협의|회의)|동학년|협의/.test(t)) return '동학년협의'; return '공지'; }
const nkOf = n => NK.includes(n.kind) ? n.kind : guessNk(n.title);
$('#nk-tabs').addEventListener('click', e => { const b = e.target.closest('[data-nk]'); if (!b) return; S.nk = b.dataset.nk; renderNotices(); resolveNames(); });
$('#notices').addEventListener('change', async e => { const sl = e.target.closest('[data-nk-set]'); if (!sl) return; try { await S.db.doc('notices/' + sl.dataset.nkSet).update({kind:sl.value}); } catch (er){ wErr(er, true); } });

/* ---------- 공지 댓글 · 투표 ---------- */
function mkPoll(text, multi){
  const opts = String(text || '').split('\n').map(x => x.trim()).filter(Boolean).slice(0, 12);
  if (opts.length < 2) return null;
  return {options:opts.map((t, i) => ({id:'o' + i, text:t.slice(0, 60)})), multi:!!multi, votes:{}, closed:false, createdAt:Date.now()};
}
function pollHtml(n){
  if (S.pollEdit === n.id && !n.poll) return `<div class="poll-mk"><textarea id="pm-${n.id}" rows="3" placeholder="고를 것을 한 줄에 하나씩"></textarea><div class="row"><label class="row hint" for="pmm-${n.id}"><input type="checkbox" id="pmm-${n.id}"> 여러 개 고를 수 있게</label><span class="grow"></span><button type="button" class="btn small" data-act="poll-cancel" data-id="${n.id}">취소</button><button type="button" class="btn small primary" data-act="poll-save" data-id="${n.id}">투표 붙이기</button></div></div>`;
  const p = n.poll; if (!p || !Array.isArray(p.options)) return '';
  const votes = p.votes || {}, voters = Object.keys(votes).filter(u => Array.isArray(votes[u]) && votes[u].length);
  const mine = (votes[S.uid] || []);
  const cnt = o => voters.filter(u => votes[u].includes(o.id));
  const max = Math.max(1, ...p.options.map(o => cnt(o).length));
  const can = S.canWrite && !p.closed;
  return `<div class="poll ${p.closed ? 'closed' : ''}"><div class="poll-h"><b>투표</b><span class="hint">${p.multi ? '여러 개 고를 수 있어요 · ' : ''}${voters.length}명 참여${p.closed ? ' · 마감' : ''}</span>
    ${S.canWrite && (n.createdBy === S.uid || S.isOwner) ? `<button type="button" class="btn small" data-act="poll-close" data-id="${n.id}">${p.closed ? '다시 열기' : '마감'}</button>` : ''}</div>
    ${p.options.map(o => { const who = cnt(o), on = mine.includes(o.id); return `<button type="button" class="poll-o ${on ? 'on' : ''}" data-act="vote" data-id="${n.id}" data-opt="${o.id}" ${can ? '' : 'disabled'} aria-pressed="${on}">
      <i style="width:${Math.round(who.length / max * 100)}%"></i><span class="t">${on ? '✓ ' : ''}${esc(o.text)}</span><span class="c">${who.length}</span>
      ${who.length ? `<span class="who">${who.map(author).join(', ')}</span>` : ''}</button>`; }).join('')}</div>`;
}
function commentsHtml(n){
  const cm = Object.entries(n.comments || {}).filter(([, c]) => c && c.text).sort((a, b) => (a[1].at || 0) - (b[1].at || 0));
  const open = (S.openCmt || new Set()).has(n.id);
  const head = `<button type="button" class="linkbtn cm-toggle" data-act="cm-toggle" data-id="${n.id}">댓글 ${cm.length ? cm.length : '달기'}${open ? ' ▴' : ' ▾'}</button>`;
  if (!open) return `<div class="cm">${head}</div>`;
  return `<div class="cm open">${head}<div class="cm-list">${cm.map(([cid, c]) => `<div class="cm-i"><b>${author(c.by)}</b><span class="t">${linkify(esc(c.text))}</span><span class="mono hint">${c.at ? fmtMD(ymd(new Date(c.at))) : ''}</span>${c.by === S.uid ? `<button type="button" class="x" data-act="cm-del" data-id="${n.id}" data-cid="${cid}" aria-label="댓글 지우기">×</button>` : ''}</div>`).join('')}</div>
    ${S.canWrite ? `<div class="cm-add"><input type="text" id="cm-${n.id}" data-cm="${n.id}" placeholder="댓글 달기" autocomplete="off" aria-label="댓글"><button type="button" class="btn small primary" data-act="cm-add" data-id="${n.id}">등록</button></div>` : ''}</div>`;
}
async function noticeUpd(id, data){ try { await S.db.doc('notices/' + id).update(data); } catch (e){ wErr(e, true); } }
$('#notices').addEventListener('click', async e => {
  const b = e.target.closest('[data-act]'); if (!b) return;
  const act = b.dataset.act, id = b.dataset.id, n = S.notices.find(x => x.id === id);
  if (!['vote', 'cm-toggle', 'cm-add', 'cm-del', 'poll-open', 'poll-cancel', 'poll-save', 'poll-close'].includes(act)) return;
  e.stopPropagation();
  if (act === 'cm-toggle'){ S.openCmt = S.openCmt || new Set(); S.openCmt.has(id) ? S.openCmt.delete(id) : S.openCmt.add(id); renderNotices(); resolveNames(); if (S.openCmt.has(id)){ const i = $('#cm-' + id); if (i) i.focus(); } return; }
  if (!S.canWrite || !n){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  if (act === 'vote'){
    const p = n.poll; if (!p || p.closed) return;
    let mine = ((p.votes || {})[S.uid] || []).slice();
    const o = b.dataset.opt;
    mine = mine.includes(o) ? mine.filter(x => x !== o) : (p.multi ? mine.concat(o) : [o]);
    await noticeUpd(id, {poll:{votes:{[S.uid]:mine}}});
  } else if (act === 'cm-add'){
    const inp = $('#cm-' + id), t = inp.value.trim(); if (!t) return;
    inp.value = ''; inp.blur();
    await noticeUpd(id, {comments:{['c' + Date.now().toString(36) + Math.random().toString(36).slice(2, 5)]:{by:S.uid, text:t.slice(0, 500), at:Date.now()}}});
  } else if (act === 'cm-del'){
    if (!twoStep(b, '지울까요?')) return;
    await noticeUpd(id, {comments:{[b.dataset.cid]:null}});
  } else if (act === 'poll-open'){ S.pollEdit = id; renderNotices(); const t = $('#pm-' + id); if (t) t.focus(); }
  else if (act === 'poll-cancel'){ S.pollEdit = null; renderNotices(); }
  else if (act === 'poll-save'){
    const p = mkPoll($('#pm-' + id).value, $('#pmm-' + id).checked);
    if (!p){ toast('고를 것을 두 줄 이상 적어 주세요.'); return; }
    S.pollEdit = null; document.activeElement.blur(); await noticeUpd(id, {poll:p});
  } else if (act === 'poll-close'){ await noticeUpd(id, {poll:{closed:!(n.poll && n.poll.closed)}}); }
});
$('#notices').addEventListener('keydown', e => { const i = e.target.closest('[data-cm]'); if (i && e.key === 'Enter' && !e.isComposing){ e.preventDefault(); const b = i.parentElement.querySelector('[data-act="cm-add"]'); if (b) b.click(); } });
$('#notices').addEventListener('focusout', () => setTimeout(() => { if (S.noticeLater && !($('#notices').contains(document.activeElement) && document.activeElement.matches('input, textarea'))){ renderNotices(); resolveNames(); } }, 0));


/* ---------- 나의 공간 한마디 ---------- */
function renderMotto(){ const el = $('#me-motto'); if (!el || document.activeElement === el) return; el.textContent = S.profile.motto || ''; el.classList.toggle('empty', !S.profile.motto); }
$('#me-motto').addEventListener('keydown', e => { if (e.key === 'Enter'){ e.preventDefault(); e.target.blur(); } });
$('#me-motto').addEventListener('paste', e => { e.preventDefault(); const t = (e.clipboardData.getData('text/plain') || '').replace(/\s+/g, ' '); document.execCommand('insertText', false, t); });
$('#me-motto').addEventListener('blur', e => {
  if (!S.uid) return;
  const v = e.target.textContent.replace(/\s+/g, ' ').trim().slice(0, 120);
  if (v === (S.profile.motto || '')) { renderMotto(); return; }
  S.profile.motto = v; saveProfile(); renderMotto();
});

/* ================= 운영자료 ================= */
const OPS_CATS = ['학교 안내', '복무·결재', '문서 양식', '업무', '연수', '안전', '기타'];
const FILE_MAX = 3 * 1024 * 1024, PART = 200000;
const fmtSize = n => n >= 1048576 ? (n / 1048576).toFixed(1) + 'MB' : Math.max(1, Math.round(n / 1024)) + 'KB';
/* 글 속 주소(https://…, www.…)를 누를 수 있는 링크로 바꿔요. esc()를 거친 글에 써요. */
function linkify(h){
  return String(h || '').replace(/(^|[\s(（\[「『>])((?:https?:\/\/|www\.)[^\s<]+?)(?=[.,;:!?)\]」』'"]*(?:\s|<|$))/gi, (all, pre, u) => {
    const href = /^www\./i.test(u) ? 'https://' + u : u;
    return `${pre}<a class="autolink" href="${href}" target="_blank" rel="noopener noreferrer">${u}</a>`;
  });
}
document.addEventListener('click', e => { if (e.target.closest && e.target.closest('a.autolink')) e.stopPropagation(); }, true);
function bodyHtml(t){
  return esc(t || '').split('\n').map(l => {
    l = linkify(l);
    const m = l.match(/^\s*[-*]\s*\[( |x|X)\]\s*(.*)$/);
    if (m) return `<span class="ck-line"><span class="ckb">${m[1].trim() ? '☑' : '☐'}</span>${m[2]}</span>`;
    const b = l.match(/^\s*[-*•]\s+(.*)$/);
    if (b) return `<span class="ul-line">• ${b[1]}</span>`;
    return l ? `<span class="p-line">${l}</span>` : '<span class="sp-line"></span>';
  }).join('');
}
/* 운영자료(학년)와 나의 공간 자료는 같은 틀로 그려요 */
const OPG = {k:'g', p:'', stage:'ops', cat:'all', edit:null, files:[], list:() => S.ops || [], can:() => S.canWrite, shared:true,
  col:() => S.db.collection('ops'), doc:id => S.db.doc('ops/' + id), fdoc:(fid, i) => S.db.doc(`opsfiles/${fid}_${i}`), on:() => S.page === 'ops' && S.space === 'grade',
  empty:'학교 운영 안내, 복무·결재 라인, 문서 양식 파일처럼 자주 찾는 자료를 올려 두세요.'};
const OPM = {k:'m', p:'m', stage:'mops', cat:'all', edit:null, files:[], list:() => S.mops || [], can:() => !!(S.uid && S.db && !S.arc), shared:false,
  col:() => S.db.doc(PROFILE()).collection('ops'), doc:id => S.db.doc(PROFILE() + '/ops/' + id), fdoc:(fid, i) => S.db.doc(`data/users/${S.uid}/of_${fid}_${i}`), on:() => S.space === 'me' && S.meTab === 'mops',
  empty:'나만 볼 자료를 모아 두세요. 학급 운영 체크리스트, 자주 여는 링크, 양식 파일, 캡처 사진 같은 것들이요.'};
const opsEl = (C, id) => $('#' + C.p + id);
function opsCats(C){ return [...new Set((C.k === 'g' ? OPS_CATS : ['학급 운영', '수업', '업무', '개인', '기타']).concat(C.list().map(o => o.cat).filter(Boolean)))]; }
function renderOps(C){
  C = C || OPG;
  if (!C.on()) return;
  const list = C.list().slice().sort((a, b) => (a.cat || '').localeCompare(b.cat || '', 'ko') || (b.updatedAt || b.createdAt || 0) - (a.updatedAt || a.createdAt || 0));
  const used = [...new Set(list.map(o => o.cat || '기타'))];
  if (C.cat !== 'all' && !used.includes(C.cat)) C.cat = 'all';
  opsEl(C, 'ops-cats').innerHTML = [['all', `전체 <small>${list.length}</small>`]].concat(used.map(c => [c, `${esc(c)} <small>${list.filter(o => (o.cat || '기타') === c).length}</small>`])).map(([k, n]) => `<button type="button" class="stab" data-ocat="${esc(k)}" ${C.cat === k ? 'aria-current="page"' : ''}>${n}</button>`).join('');
  opsEl(C, 'of-cats').innerHTML = opsCats(C).map(c => `<option value="${esc(c)}">`).join('');
  const show = C.cat === 'all' ? list : list.filter(o => (o.cat || '기타') === C.cat);
  const canEd = C.can();
  opsEl(C, 'ops-list').innerHTML = show.length ? show.map(o => {
    const ok = /^https?:\/\//i.test(o.url || '');
    const wide = (o.imgs || []).length > 0;
    return `<article class="ops-card ${wide ? 'wide' : ''}"><div class="oc-h"><span class="chip">${esc(o.cat || '기타')}</span><h3>${esc(o.title || '(제목 없음)')}</h3>
      ${canEd ? `<span class="grow"></span><button type="button" class="btn small" data-oact="edit" data-id="${o.id}">고치기</button><button type="button" class="x" data-oact="del" data-id="${o.id}" aria-label="지우기">×</button>` : ''}</div>
      <div class="oc-scroll">
      ${o.body ? `<div class="oc-body">${bodyHtml(o.body)}</div>` : ''}
      ${ok ? `<a class="oc-link" href="${esc(o.url)}" target="_blank" rel="noopener noreferrer">${esc(o.url.replace(/^https?:\/\//, ''))}</a>` : ''}
      ${wide ? `<div class="oc-imgs">${thumbsHtml(o.imgs, '')}</div>` : ''}
      </div>
      ${(o.files || []).length ? `<div class="oc-files">${o.files.map(f => `<button type="button" class="ofile" data-oact="get" data-id="${o.id}" data-fid="${esc(f.fid)}"><span class="ico">${esc((f.name.split('.').pop() || '').slice(0, 4).toUpperCase())}</span><span class="nm">${esc(f.name)}</span><span class="sz">${fmtSize(f.size || 0)}</span></button>`).join('')}</div>` : ''}
    </article>`;
  }).join('') : `<p class="empty">${list.length ? '이 분류에 올린 자료가 없어요.' : C.empty}</p>`;
  hydrateImgs();
  if (C.k === 'g') renderPhrases();
}
function opsFormOpen(C, o){
  C.edit = o ? o.id : null;
  opsEl(C, 'ops-form').hidden = false;
  opsEl(C, 'of-title').value = o ? o.title || '' : '';
  opsEl(C, 'of-cat').value = o ? o.cat || '' : (C.cat !== 'all' ? C.cat : '');
  opsEl(C, 'of-body').value = o ? o.body || '' : '';
  opsEl(C, 'of-url').value = o ? o.url || '' : '';
  S.stage[C.stage] = o ? (o.imgs || []).slice() : []; renderStage(C.stage);
  C.files = o ? (o.files || []).map(f => Object.assign({}, f)) : [];
  renderOpsFiles(C);
  opsEl(C, 'of-save').textContent = o ? '고친 것 저장' : '저장';
  opsEl(C, 'of-title').focus();
}
function renderOpsFiles(C){
  opsEl(C, 'of-files').innerHTML = C.files.map((f, i) => `<span class="ofile small"><span class="nm">${esc(f.name)}</span><span class="sz">${f.pending ? '올릴 파일 · ' : ''}${fmtSize(f.size || 0)}</span><button type="button" class="x" data-ofrm="${i}" aria-label="파일 빼기">×</button></span>`).join('');
}
const readB64 = f => new Promise((res, rej) => { const r = new FileReader(); r.onload = () => res(String(r.result).split(',')[1] || ''); r.onerror = rej; r.readAsDataURL(f); });
async function putFile(C, f){
  const b64 = await readB64(f.file), fid = 'f' + rid(), n = Math.max(1, Math.ceil(b64.length / PART));
  for (let i = 0; i < n; i++){ opsEl(C, 'of-filehint').textContent = `${f.name} 올리는 중 ${i + 1}/${n}`; await C.fdoc(fid, i).set({d:b64.slice(i * PART, (i + 1) * PART), i, n, by:S.uid}); }
  return {fid, name:f.name, size:f.size, type:f.type, parts:n};
}
async function dropFile(C, f){ for (let i = 0; i < (f.parts || 1); i++){ try { await C.fdoc(f.fid, i).delete(); } catch (e){} } }
function wireOps(C){
  const noPerm = () => toast(C.k === 'g' ? '학년 공간을 고칠 권한이 없어요.' : '로그인한 상태에서만 올릴 수 있어요.');
  opsEl(C, 'ops-new').onclick = () => { if (!C.can()){ noPerm(); return; } opsFormOpen(C, null); };
  opsEl(C, 'of-cancel').onclick = () => { opsEl(C, 'ops-form').hidden = true; C.edit = null; C.files = []; S.stage[C.stage] = []; };
  opsEl(C, 'of-file').addEventListener('change', e => {
    [...(e.target.files || [])].forEach(f => {
      if (f.size > FILE_MAX){ toast(`${f.name}은(는) 3MB가 넘어서 올릴 수 없어요. 큰 파일은 구글 드라이브에 두고 링크로 넣어 주세요.`); return; }
      C.files.push({name:f.name, size:f.size, type:f.type || '', pending:true, file:f});
    });
    e.target.value = ''; renderOpsFiles(C);
  });
  opsEl(C, 'of-files').addEventListener('click', e => { const b = e.target.closest('[data-ofrm]'); if (!b) return; C.files.splice(+b.dataset.ofrm, 1); renderOpsFiles(C); });
  opsEl(C, 'ops-form').addEventListener('submit', async e => {
    e.preventDefault();
    if (!C.can() || !S.db){ noPerm(); return; }
    const title = opsEl(C, 'of-title').value.trim(); if (!title){ toast('제목을 적어 주세요.'); opsEl(C, 'of-title').focus(); return; }
    let url = opsEl(C, 'of-url').value.trim(); if (url && !/^https?:\/\//i.test(url)) url = 'https://' + url;
    const btn = opsEl(C, 'of-save'); btn.disabled = true;
    try {
      const files = [];
      for (const f of C.files) files.push(f.pending ? await putFile(C, f) : {fid:f.fid, name:f.name, size:f.size, type:f.type, parts:f.parts});
      const prev = C.edit ? C.list().find(o => o.id === C.edit) : null;
      if (prev) (prev.files || []).filter(f => !files.some(x => x.fid === f.fid)).forEach(f => dropFile(C, f));
      const data = {title, cat:opsEl(C, 'of-cat').value.trim() || '기타', body:opsEl(C, 'of-body').value.replace(/\s+$/, ''), url, imgs:(S.stage[C.stage] || []).slice(), files, updatedAt:Date.now(), updatedBy:S.uid};
      if (prev) await C.doc(prev.id).update(data);
      else await C.col().add(Object.assign(data, {createdBy:S.uid, createdAt:Date.now()}));
      opsEl(C, 'ops-form').hidden = true; C.edit = null; C.files = []; S.stage[C.stage] = []; C.cat = data.cat;
      toast('자료를 저장했어요.'); renderOps(C);
    } catch (er){ wErr(er, C.shared); }
    btn.disabled = false; opsEl(C, 'of-filehint').textContent = '한 파일 3MB까지 (한글·엑셀·PDF 등)';
  });
  opsEl(C, 'ops-cats').addEventListener('click', e => { const b = e.target.closest('[data-ocat]'); if (!b) return; C.cat = b.dataset.ocat; renderOps(C); });
  opsEl(C, 'ops-list').addEventListener('click', async e => {
    const b = e.target.closest('[data-oact]'); if (!b) return;
    const o = C.list().find(x => x.id === b.dataset.id); if (!o) return;
    if (b.dataset.oact === 'edit'){ opsFormOpen(C, o); window.scrollTo({top:opsEl(C, 'ops-form').getBoundingClientRect().top + window.scrollY - 80}); }
    else if (b.dataset.oact === 'del'){ if (!twoStep(b, '지울까요?')) return; try { (o.files || []).forEach(f => dropFile(C, f)); await C.doc(o.id).delete(); toast('지웠어요.'); } catch (er){ wErr(er, C.shared); } }
    else if (b.dataset.oact === 'get'){
      const f = (o.files || []).find(x => x.fid === b.dataset.fid); if (!f) return;
      b.disabled = true; toast(`${f.name} 받는 중…`);
      try {
        let b64 = '';
        for (let i = 0; i < (f.parts || 1); i++){ const sn = await C.fdoc(f.fid, i).get(); if (!sn.exists) throw {code:'missing'}; b64 += sn.data().d || ''; }
        const bin = atob(b64), u8 = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
        await save(f.name, new Blob([u8], {type:f.type || 'application/octet-stream'}));
      } catch (er){ toast(er && er.code === 'missing' ? '파일 일부를 찾지 못했어요. 다시 올려 주세요.' : '파일을 받지 못했어요.'); }
      b.disabled = false;
    }
  });
}
wireOps(OPG); wireOps(OPM);

/* ---------- 자주 쓰는 문구 ---------- */
const PH = {sc:'g', edit:null};
const phCol = () => PH.sc === 'g' ? S.db.collection('phrases') : S.db.doc(PROFILE()).collection('phrases');
function renderPhrases(){
  $$('#ph-scope button').forEach(b => b.setAttribute('aria-pressed', b.dataset.sc === PH.sc));
  const l = ((PH.sc === 'g' ? S.phG : S.phM) || []).slice().sort((a, b) => (a.title || '').localeCompare(b.title || '', 'ko'));
  const can = PH.sc === 'g' ? S.canWrite : !!S.uid;
  $('#ph-new').disabled = !can;
  $('#ph-list').innerHTML = l.length ? l.map(p => `<div class="ph"><div class="ph-h"><b>${esc(p.title || '문구')}</b><span class="grow"></span><button type="button" class="btn small primary" data-pact="copy" data-id="${p.id}">복사</button>${can ? `<button type="button" class="btn small" data-pact="edit" data-id="${p.id}">고치기</button><button type="button" class="x" data-pact="del" data-id="${p.id}" aria-label="지우기">×</button>` : ''}</div><div class="ph-t">${linkify(esc(p.text || ''))}</div></div>`).join('')
    : `<p class="hint" style="margin:0">${PH.sc === 'g' ? '학년이 함께 쓰는 하이톡·알림 문구를 모아 두면 "복사"로 바로 붙여 쓸 수 있어요.' : '나만 쓰는 문구예요. 다른 선생님에게는 보이지 않아요.'}</p>`;
}
$('#ph-scope').addEventListener('click', e => { const b = e.target.closest('[data-sc]'); if (!b) return; PH.sc = b.dataset.sc; $('#ph-form').hidden = true; renderPhrases(); });
$('#ph-new').onclick = () => { PH.edit = null; $('#ph-title').value = ''; $('#ph-text').value = ''; $('#ph-form').hidden = false; $('#ph-title').focus(); };
$('#ph-cancel').onclick = () => { $('#ph-form').hidden = true; PH.edit = null; };
$('#ph-form').addEventListener('submit', async e => {
  e.preventDefault(); if (!S.db) return;
  const title = $('#ph-title').value.trim(), text = $('#ph-text').value.replace(/\s+$/, '');
  if (!text){ toast('문구를 적어 주세요.'); return; }
  try {
    if (PH.edit) await phCol().doc(PH.edit).update({title:title || text.slice(0, 20), text, updatedAt:Date.now()});
    else await phCol().add({title:title || text.slice(0, 20), text, createdBy:S.uid, createdAt:Date.now()});
    $('#ph-form').hidden = true; PH.edit = null; toast('문구를 저장했어요.');
  } catch (er){ wErr(er, PH.sc === 'g'); }
});
$('#ph-list').addEventListener('click', async e => {
  const b = e.target.closest('[data-pact]'); if (!b) return;
  const l = (PH.sc === 'g' ? S.phG : S.phM) || [], p = l.find(x => x.id === b.dataset.id); if (!p) return;
  if (b.dataset.pact === 'copy'){
    try { await navigator.clipboard.writeText(p.text || ''); toast('복사했어요. 하이톡·메신저에 붙여 넣으면 돼요.'); }
    catch (er){ const t = b.closest('.ph').querySelector('.ph-t'); const r = document.createRange(); r.selectNodeContents(t); const sel = getSelection(); sel.removeAllRanges(); sel.addRange(r); toast('글을 골라 두었어요. Ctrl+C로 복사해 주세요.'); }
  } else if (b.dataset.pact === 'edit'){ PH.edit = p.id; $('#ph-title').value = p.title || ''; $('#ph-text').value = p.text || ''; $('#ph-form').hidden = false; $('#ph-text').focus(); }
  else if (b.dataset.pact === 'del'){ if (!twoStep(b, '지울까요?')) return; try { await phCol().doc(p.id).delete(); } catch (er){ wErr(er, PH.sc === 'g'); } }
});

BUD.g = makeBudget('g'); BUD.m = makeBudget('m');
ROS.g = makeRoster('g'); ROS.m = makeRoster('m');

/* ---------- classroom tools ---------- */
const T = {tool:'morn', total:300, remain:300, running:false, iv:null, end:0, pool:null, hist:[], seats:null};
const lsGet = (k, d) => { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : d; } catch (e){ return d; } };
const lsSet = (k, v) => { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e){} };
function showTool(name){
  const jdm = isJD();
  ['morn', 'note'].forEach(t => { const bt = document.querySelector(`[data-tool="${t}"]`); if (bt) bt.hidden = jdm; });
  if (jdm && (name === 'morn' || name === 'note')) name = 'timer';
  T.tool = name;
  $$('#tool-tabs button').forEach(b => b.setAttribute('aria-pressed', b.dataset.tool === name));
  ['morn', 'note', 'timer', 'pick', 'order', 'dice', 'seat', 'score'].forEach(t => { $('#tool-' + t).hidden = t !== name; });
  if (name === 'note') renderNoteTool();
  if (name === 'dice') diceInfo();
  if (name === 'morn') renderMorning(true);
  if (name === 'pick') pickInfo();
  if (name === 'seat') loadSeatRules();
  if (name === 'score') renderTeams();
}
function rosterForTools(){
  const r = S.profile.roster || [];
  if (r.length) return r.map(x => ({no:x.no, name:x.name || `${x.no}번`, sex:x.sex}));
  return Array.from({length:24}, (_, i) => ({no:i + 1, name:`${i + 1}번`}));
}
const shuffle = a => { const x = a.slice(); for (let i = x.length - 1; i > 0; i--){ const j = Math.floor(Math.random() * (i + 1)); [x[i], x[j]] = [x[j], x[i]]; } return x; };
function timerDraw(){
  const s = Math.max(0, Math.ceil(T.remain));
  $('#timer-face').textContent = `${pad(Math.floor(s / 60))}:${pad(s % 60)}`;
  $('#timer-go').textContent = T.running ? '잠깐 멈춤' : (T.remain < T.total && T.remain > 0 ? '이어서' : '시작');
}
function timerSet(sec){ clearInterval(T.iv); T.running = false; T.total = T.remain = sec; $('#timer-face').classList.remove('ring'); timerDraw(); }
function beep(){
  try {
    const ac = new (window.AudioContext || window.webkitAudioContext)();
    [0, .35, .7].forEach(t => { const o = ac.createOscillator(), g = ac.createGain(); o.frequency.value = 880; o.connect(g); g.connect(ac.destination);
      g.gain.setValueAtTime(.0001, ac.currentTime + t); g.gain.exponentialRampToValueAtTime(.3, ac.currentTime + t + .02); g.gain.exponentialRampToValueAtTime(.0001, ac.currentTime + t + .28);
      o.start(ac.currentTime + t); o.stop(ac.currentTime + t + .3); });
  } catch (e) {}
}
$('#timer-go').onclick = () => {
  if (T.running){ clearInterval(T.iv); T.running = false; timerDraw(); return; }
  if (T.remain <= 0) T.remain = T.total;
  $('#timer-face').classList.remove('ring');
  T.running = true; T.end = Date.now() + T.remain * 1000;
  T.iv = setInterval(() => {
    T.remain = (T.end - Date.now()) / 1000;
    if (T.remain <= 0){ T.remain = 0; clearInterval(T.iv); T.running = false; $('#timer-face').classList.add('ring'); beep(); }
    timerDraw();
  }, 200);
  timerDraw();
};
$('#timer-reset').onclick = () => timerSet(T.total);
$('#timer-set').onclick = () => { const m = parseInt($('#timer-min').value, 10); if (m > 0 && m <= 120) timerSet(m * 60); else toast('1분에서 120분 사이로 적어 주세요.'); };
const sxOf = id => (($(`#${id} [aria-pressed="true"]`) || {}).dataset || {}).sx || 'all';
['pick-sx', 'order-sx'].forEach(id => $('#' + id).addEventListener('click', e => { const b = e.target.closest('[data-sx]'); if (!b) return; $$(`#${id} button`).forEach(x => x.setAttribute('aria-pressed', x === b)); if (id === 'pick-sx'){ T.pool = null; pickInfo(); } }));
function poolFor(sx){ const all = rosterForTools(); if (sx === 'all') return all; return all.filter(r => r.sex === sx); }
function pickInfo(){
  const sx = sxOf('pick-sx'), all = poolFor(sx);
  if (!T.pool) T.pool = all.slice();
  const noSex = sx !== 'all' && !rosterForTools().some(r => r.sex);
  $('#pick-info').textContent = noSex ? '명부에 성별이 없어요. 명부 탭에서 성별을 넣으면 여자만·남자만 뽑을 수 있어요.' : (S.profile.roster || []).length ? `남은 학생 ${T.pool.length}명 / ${all.length}명${sx !== 'all' ? ` (${sx}자만)` : ''}` : `명단이 없어서 1~24번으로 뽑아요. 명부 탭에서 바꿀 수 있어요.`;
  $('#pick-hist').innerHTML = T.hist.map(h => `<span class="chip">${esc(h)}</span>`).join('');
}
$('#pick-go').onclick = () => {
  const norep = $('#pick-norep').checked, sx = sxOf('pick-sx');
  const want = Math.max(1, Math.min(30, parseInt($('#pick-n').value, 10) || 1));
  if (!T.pool || !T.pool.length) T.pool = poolFor(sx);
  const src = norep ? T.pool : poolFor(sx);
  if (!src.length){ toast(sx !== 'all' ? `${sx}자 학생이 없어요. 명부에 성별을 넣어 주세요.` : '뽑을 학생이 없어요.'); return; }
  const n = Math.min(want, src.length);
  const face = $('#pick-face'); face.classList.toggle('many', n > 1); face.style.setProperty('--n', n);
  let k = 0;
  const reduce = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  const show = list => { face.innerHTML = list.map(x => `<span>${esc(x.name)}</span>`).join(''); };
  const finish = () => {
    const got = shuffle(src).slice(0, n);
    show(got);
    if (norep) T.pool = T.pool.filter(x => !got.some(g => g.no === x.no));
    T.hist = got.map(g => g.name).concat(T.hist).slice(0, 40); pickInfo();
    if (want > n) toast(`남은 학생이 ${n}명뿐이라 ${n}명만 뽑았어요.`);
  };
  if (reduce){ finish(); return; }
  const iv = setInterval(() => { show(shuffle(src).slice(0, n)); if (++k > 12){ clearInterval(iv); finish(); } }, 60);
};
$('#pick-reset').onclick = () => { T.pool = null; T.hist = []; $('#pick-face').textContent = '?'; $('#pick-face').classList.remove('many'); pickInfo(); };
/* 주사위 */
const DICE = {left:null, hist:[]};
const PIPS = {1:[5], 2:[1, 9], 3:[1, 5, 9], 4:[1, 3, 7, 9], 5:[1, 3, 5, 7, 9], 6:[1, 3, 4, 6, 7, 9]};
function dieHtml(v, max){ return max <= 6 ? `<div class="die pips" aria-label="${v}">${PIPS[v].map(i => { const c = (i - 1) % 3, r = Math.floor((i - 1) / 3); return `<i style="left:${14 + c * 27}%;top:${14 + r * 27}%"></i>`; }).join('')}</div>` : `<div class="die num">${v}</div>`; }
const diceRep = () => ($('#dice-rep [aria-pressed="true"]') || {dataset:{rep:'1'}}).dataset.rep === '1';
const diceMax = () => Math.max(2, Math.min(40, parseInt($('#dice-max').value, 10) || 6));
function diceInfo(){
  const max = diceMax();
  if (!diceRep()){ if (!DICE.left || DICE.max !== max) { DICE.left = Array.from({length:max}, (_, i) => i + 1); DICE.max = max; } $('#dice-info').textContent = DICE.left.length ? `남은 숫자 ${DICE.left.join(', ')}` : '숫자를 다 썼어요. "다시 처음부터"를 누르세요.'; }
  else $('#dice-info').textContent = `1부터 ${max}까지 나와요. 같은 숫자가 또 나올 수 있어요.`;
  $('#dice-hist').innerHTML = DICE.hist.map(h => `<span class="chip">${h}</span>`).join('');
  if (!$('#dice-row').innerHTML) $('#dice-row').innerHTML = dieHtml(Math.min(6, max), max);
}
$('#dice-rep').addEventListener('click', e => { const b = e.target.closest('[data-rep]'); if (!b) return; $$('#dice-rep button').forEach(x => x.setAttribute('aria-pressed', x === b)); DICE.left = null; diceInfo(); });
['#dice-max', '#dice-n'].forEach(id => $(id).addEventListener('change', () => { DICE.left = null; $('#dice-row').innerHTML = ''; diceInfo(); }));
$('#dice-go').onclick = () => {
  const max = diceMax(), rep = diceRep();
  let n = Math.max(1, Math.min(12, parseInt($('#dice-n').value, 10) || 1));
  if (!rep){ diceInfo(); if (!DICE.left.length){ toast('숫자를 다 썼어요. "다시 처음부터"를 누르세요.'); return; } n = Math.min(n, DICE.left.length); }
  const roll = () => rep ? Array.from({length:n}, () => 1 + Math.floor(Math.random() * max)) : shuffle(DICE.left).slice(0, n);
  const row = $('#dice-row'); let k = 0;
  const finish = () => {
    const got = roll(); row.innerHTML = got.map(v => dieHtml(v, max)).join(''); row.classList.remove('rolling');
    if (!rep) DICE.left = DICE.left.filter(v => !got.includes(v));
    DICE.hist = [got.join(' · ')].concat(DICE.hist).slice(0, 30); diceInfo();
  };
  if (window.matchMedia('(prefers-reduced-motion: reduce)').matches){ finish(); return; }
  row.classList.add('rolling');
  const iv = setInterval(() => { row.innerHTML = Array.from({length:n}, () => dieHtml(1 + Math.floor(Math.random() * Math.min(max, max)), max)).join(''); if (++k > 10){ clearInterval(iv); finish(); } }, 70);
};
$('#dice-reset').onclick = () => { DICE.left = null; DICE.hist = []; $('#dice-row').innerHTML = ''; diceInfo(); };
/* 순서 정하기 */
function renderOrder(){
  const list = T.order || [], n = T.shown || 0;
  $('#order-list').innerHTML = list.slice(0, n).map((r, i) => `<li class="${i === n - 1 && n < list.length + 1 && T.oneByOne ? 'new' : ''}"><b>${i + 1}</b>${esc(r.name)}</li>`).join('');
  $('#order-next').hidden = !(T.oneByOne && n < list.length);
  $('#order-next').textContent = `다음 (${n}/${list.length})`;
}
$('#order-go').onclick = () => {
  const sx = sxOf('order-sx'); const src = poolFor(sx);
  if (!src.length){ toast(sx !== 'all' ? `${sx}자 학생이 없어요. 명부에 성별을 넣어 주세요.` : '학생이 없어요.'); return; }
  T.order = shuffle(src); T.oneByOne = $('#order-one').checked;
  T.shown = T.oneByOne ? 1 : T.order.length; renderOrder();
};
$('#order-next').onclick = () => { T.shown = Math.min((T.order || []).length, (T.shown || 0) + 1); renderOrder(); };

/* 자리 바꾸기 */
const SEATDOC = () => `data/users/${S.uid}/seat`;
const nums = t => (t || '').match(/\d{1,3}/g) || [];
const pairsOf = t => (t || '').split('\n').map(l => nums(l).map(Number)).filter(p => p.length >= 2).map(p => [p[0], p[1]]);
function seatRules(){ return {together:pairsOf($('#sr-together').value), apart:pairsOf($('#sr-apart').value), front:nums($('#sr-front').value).map(Number)}; }
function seatState(){ return {cols:$('#seat-cols').value, pairs:$('#seat-pairs').checked, mix:$('#seat-mix').checked, together:$('#sr-together').value, apart:$('#sr-apart').value, front:$('#sr-front').value, last:(T.seats || []).map(r => r ? r.no : null)}; }
function applySeatState(st){
  if (!st) return;
  if (st.cols) $('#seat-cols').value = st.cols;
  $('#seat-pairs').checked = st.pairs !== false; $('#seat-mix').checked = !!st.mix;
  $('#sr-together').value = st.together || ''; $('#sr-apart').value = st.apart || ''; $('#sr-front').value = st.front || '';
  if (Array.isArray(st.last) && st.last.length){
    const by = {}; rosterForTools().forEach(r => { by[r.no] = r; });
    const list = st.last.map(n => n == null ? null : by[n] || null);
    if (list.filter(Boolean).length) T.seats = list;
  }
}
async function loadSeatRules(){
  if (T.seatLoaded){ renderSeats(T.seats || rosterForTools()); return; }
  T.seatLoaded = true;
  let st = lsGet('seat-state', null);
  if (S.db && S.uid){ try { const snap = await S.db.doc(SEATDOC()).get(); if (snap.exists) st = snap.data(); } catch (e) {} }
  applySeatState(st);
  renderSeats(T.seats || rosterForTools());
}
function saveSeatState(){
  const st = seatState(); lsSet('seat-state', st);
  if (S.db && S.uid) queueSet(SEATDOC(), () => st, false);
}
function seatGeom(n){
  const C = Math.max(2, Math.min(10, parseInt($('#seat-cols').value, 10) || 6));
  return {C, R:Math.ceil(n / C)};
}
function seatScore(arr, C, rules, opt){
  const pos = {}; arr.forEach((r, i) => { if (r) pos[r.no] = i; });
  const rc = i => [Math.floor(i / C), i % C];
  const desk = i => { const [r, c] = rc(i); return r * 100 + Math.floor(c / 2); };
  const adj = (i, j) => { const [a, b] = rc(i), [c, d] = rc(j); return (a === c && Math.abs(b - d) === 1) || (b === d && Math.abs(a - c) === 1); };
  const mates = (i, j) => opt.pairs ? desk(i) === desk(j) && i !== j : (rc(i)[0] === rc(j)[0] && Math.abs(i - j) === 1);
  let hard = 0, soft = 0; const bad = new Set();
  rules.together.forEach(([x, y]) => { if (pos[x] == null || pos[y] == null) return; if (!mates(pos[x], pos[y])){ hard++; bad.add(x); bad.add(y); } });
  rules.apart.forEach(([x, y]) => { if (pos[x] == null || pos[y] == null) return; if (adj(pos[x], pos[y]) || mates(pos[x], pos[y])){ hard++; bad.add(x); bad.add(y); } });
  const frontRows = Math.max(1, Math.ceil(rules.front.filter(n => pos[n] != null).length / C));
  rules.front.forEach(n => { if (pos[n] == null) return; if (rc(pos[n])[0] >= frontRows){ hard++; bad.add(n); } });
  if (opt.mix) for (let i = 0; i < arr.length; i++){ const j = opt.pairs ? (i % 2 === 0 ? i + 1 : -1) : i + 1; if (j < 0 || j >= arr.length || rc(i)[0] !== rc(j)[0]) continue; const a = arr[i], b = arr[j]; if (a && b && a.sex && b.sex && a.sex === b.sex) soft++; }
  return {score:hard * 100 + soft, hard, bad};
}
function arrangeSeats(){
  const list = rosterForTools(), rules = seatRules(), opt = {pairs:$('#seat-pairs').checked, mix:$('#seat-mix').checked};
  const {C, R} = seatGeom(list.length);
  const slots = R * C;
  let best = null;
  for (let restart = 0; restart < 12; restart++){
    const arr = shuffle(list.concat(Array(slots - list.length).fill(null)));
    let cur = seatScore(arr, C, rules, opt);
    for (let k = 0; k < 2500 && cur.score > 0; k++){
      const i = Math.floor(Math.random() * slots), j = Math.floor(Math.random() * slots); if (i === j) continue;
      [arr[i], arr[j]] = [arr[j], arr[i]];
      const nx = seatScore(arr, C, rules, opt);
      if (nx.score <= cur.score) cur = nx; else [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    if (!best || cur.score < best.res.score) best = {arr:arr.slice(), res:cur};
    if (best.res.score === 0) break;
  }
  return best;
}
function renderSeats(list, res){
  const n = list.length, {C} = seatGeom(n);
  const pairs = $('#seat-pairs').checked;
  T.seats = list;
  const flip = $('#tool-seat').classList.contains('flip');
  const cells = list.map((r, i) => ({r, i}));
  const shown = flip ? cells.slice().reverse() : cells;
  $('#seats').style.setProperty('--cols', C);
  const bad = (res && res.bad) || new Set();
  $('#seats').innerHTML = shown.map(({r, i}, k) => {
    const c = k % C;
    const pr = pairs && c % 2 === 0 && c < C - 1 ? '' : (pairs && c % 2 === 1 && c < C - 1 ? 'pr' : '');
    if (!r) return `<div class="seat empty ${pr}" aria-hidden="true"></div>`;
    return `<div class="seat ${r.sex === '여' ? 'f' : r.sex === '남' ? 'm' : ''} ${pr} ${bad.has(r.no) ? 'bad' : ''}"><span class="no">${r.no}</span>${esc(r.name)}</div>`;
  }).join('');
}
$('#seat-go').onclick = () => {
  const best = arrangeSeats();
  renderSeats(best.arr, best.res);
  $('#seat-msg').textContent = best.res.hard ? `조건 ${best.res.hard}개를 지키지 못했어요. 빨간 테두리 학생을 확인해 주세요. 한 줄 자리 수를 바꾸거나 조건을 줄이면 지키기 쉬워져요.` : (seatRules().together.length + seatRules().apart.length + seatRules().front.length ? '조건을 모두 지켰어요.' : '');
  saveSeatState();
};
['#seat-cols', '#seat-pairs', '#seat-mix'].forEach(id => $(id).addEventListener('change', () => { renderSeats(T.seats && T.seats.length ? T.seats.filter(Boolean).concat() : rosterForTools()); saveSeatState(); }));
['#sr-together', '#sr-apart', '#sr-front'].forEach(id => $(id).addEventListener('change', saveSeatState));
$('#seat-rules-btn').onclick = () => { const p = $('#seat-rules'); p.hidden = !p.hidden; $('#seat-rules-btn').setAttribute('aria-expanded', !p.hidden); };
$('#seat-flip').onclick = () => { const on = $('#tool-seat').classList.toggle('flip'); $('#seat-flip').setAttribute('aria-pressed', on); $('#seat-flip').textContent = on ? '학생 쪽에서 보기' : '교사 쪽에서 보기'; renderSeats(T.seats || rosterForTools()); };
$('#seat-print').onclick = () => {
  const flip = $('#tool-seat').classList.contains('flip');
  const C = seatGeom((T.seats || []).length).C;
  const board = '<div style="border:1px solid #000;text-align:center;padding:6px;margin:8mm auto;width:50%;font-weight:700">교탁 · 칠판</div>';
  const grid = `<div style="display:grid;grid-template-columns:repeat(${C},1fr);gap:6px">${$('#seats').innerHTML}</div>`;
  printDoc(`<div class="pdoc"><h1 style="font-size:18pt">${esc((S.settings.gradeName || '') + ' ' + (S.profile.myClass || ''))} 자리 배치도</h1>${flip ? grid + board : board + grid}</div>`);
};

function teamsState(){
  const n = Math.max(2, Math.min(8, parseInt($('#score-n').value, 10) || 4));
  let st = lsGet('score-teams', []);
  while (st.length < n) st.push({name:`${st.length + 1}모둠`, pts:0});
  return st.slice(0, n);
}
function renderTeams(){
  const st = teamsState(); const max = Math.max(...st.map(t => t.pts));
  $('#teams').innerHTML = st.map((t, i) => `<div class="team ${max > 0 && t.pts === max ? 'lead' : ''}">
    <input type="text" id="team-name-${i}" data-team="${i}" value="${esc(t.name)}" aria-label="${i + 1}번째 모둠 이름">
    <div class="pts">${t.pts}</div>
    <div class="row"><button type="button" class="btn" data-pts="${i}" data-d="-1" aria-label="1점 빼기">−1</button><button type="button" class="btn primary" data-pts="${i}" data-d="1" aria-label="1점 더하기">+1</button></div></div>`).join('');
}
$('#teams').addEventListener('click', e => {
  const b = e.target.closest('[data-pts]'); if (!b) return;
  const st = teamsState(); st[+b.dataset.pts].pts += +b.dataset.d; lsSet('score-teams', st); renderTeams();
});
$('#teams').addEventListener('change', e => {
  const inp = e.target.closest('[data-team]'); if (!inp) return;
  const st = teamsState(); st[+inp.dataset.team].name = inp.value.trim() || `${+inp.dataset.team + 1}모둠`; lsSet('score-teams', st);
});
$('#score-n').addEventListener('change', renderTeams);
$('#score-reset').onclick = () => { const st = teamsState().map(t => Object.assign(t, {pts:0})); lsSet('score-teams', st); renderTeams(); };
$('#open-tools').onclick = () => { $('#tools').hidden = false; showTool(T.tool); timerDraw(); };
$('#tools-close').onclick = async () => { $('#tools').hidden = true; try { if (document.fullscreenElement) await document.exitFullscreen(); } catch (e) {} };
$('#tools-full').onclick = () => { const on = $('#tools').classList.toggle('focus'); $('#tools-full').textContent = on ? '도구 줄 보이기' : '전체 화면'; };

document.addEventListener('keydown', e => { if (e.key === 'Escape'){ if (!$('#big').hidden) $('#big-close').click(); else if (!$('#tools').hidden && $$('.overlay').every(o => o.hidden)) $('#tools-close').click(); else closeDlgs(); } });
$$('.overlay').forEach(o => o.addEventListener('click', e => { if (e.target === o) closeDlgs(); }));
window.addEventListener('hashchange', () => applyRoute(routeOf(location.hash)));

window.__parse = parseLine; window.__cat = inferCat; window.__att = inferAtt;
(() => {
  let r0 = routeOf(location.hash);
  if (!location.hash || location.hash === '#'){ try { const v = localStorage.getItem('gyomu.lastRoute'); if (v && /^[A-Za-z0-9_-]+$/.test(v)){ r0 = v; history.replaceState(null, '', '#' + v); } } catch (e){} }
  applyRoute(r0);
})();
$('#note-done-btn').onclick = () => { S.notesDoneOpen = !S.notesDoneOpen; renderNotesDone(); };

$('#me-class').onclick = () => { if (!S.uid || S.arc) return; S.clsAsk = !S.clsAsk || (!S.profile.myClass && !isJD()); renderHeader(); if (S.clsAsk) $('#cls-ask-sel').focus(); };
$('#cls-ask-form').addEventListener('submit', e => {
  e.preventDefault(); const t = $('#cls-ask-txt').value.trim(); if (!t){ $('#cls-ask-txt').focus(); return; }
  setMyClass(clsCanon(t)); $('#cls-ask-txt').value = '';
});
$('#cls-ask-sel').addEventListener('change', () => setMyClass($('#cls-ask-sel').value));
function setMyClass(v){
  if (!S.uid || !v) return;
  S.profile.myClass = v; S.profile.role = ''; S.clsAsk = false; saveProfile(); if (S.space === 'me') applyRoute(S.route);
  if ($('#r-class')) $('#r-class').value = v;
  let pulled = 0;
  try { const n = clsNo(v); const st = n ? gradeClass(n).students : []; if (n && !(S.profile.roster || []).length && st.length){ rosterGradeToMine(n); pulled = st.length; } } catch (e){}
  rosterAutoSync('grade'); renderHeader(); renderTasks(); renderToday(); if (S.space === 'me') renderMe();
  const L = clsLabel(v);
  if (pulled) toast(`${L} 선생님으로 정하고, 학년 명부에서 우리 반 학생 ${pulled}명을 가져왔어요.`);
  else if (!clsNo(v)) toast(`${L} 선생님으로 정했어요. 학년 설정의 "반 이름"에 ${L}을 넣어 두면 학년 명부·학년 일정과도 이어져요.`);
  else toast(`${L} 선생님으로 정했어요. 제목의 반 이름을 누르면 바꿀 수 있어요.`);
}

/* ---------- 위쪽 탭 이름 바꾸기 (오른쪽 클릭 · 두 번 클릭) ---------- */
function pgName(space, r, n){ const m = space === 'me' ? (S.profile.pageNames || {}) : (S.settings.pageNames || {}); return m[r] || n; }
function startRename(a){
  const key = a.dataset.ren; if (!key || S.arc) return;
  const isMe = S.space === 'me';
  if (isMe ? !S.uid : !S.canWrite){ toast(isMe ? '로그인한 상태에서만 바꿀 수 있어요.' : '학년 공간을 고칠 권한이 없어요.'); return; }
  const def = key.startsWith('t:') ? '' : ((isMe ? curMP() : GPAGES).find(x => x[0] === key) || [])[1] || '';
  S.renaming = true;
  const old = a.textContent;
  a.innerHTML = `<input class="ren-in" value="${esc(old)}" maxlength="20" aria-label="탭 이름" style="width:${Math.max(4, old.length + 2)}em">`;
  const inp = a.querySelector('input'); inp.focus(); inp.select();
  let done = false;
  const finish = async ok => {
    if (done) return; done = true; S.renaming = false;
    const v = inp.value.trim();
    if (ok && v !== old){
      try {
        if (key.startsWith('t:')){ if (v) await S.db.doc('tabs/' + key.slice(2)).update({name:v}); }
        else if (isMe){ const m = Object.assign({}, S.profile.pageNames || {}); if (!v || v === def) delete m[key]; else m[key] = v; S.profile.pageNames = m; saveProfile(); }
        else { const m = Object.assign({}, S.settings.pageNames || {}); if (!v || v === def) delete m[key]; else m[key] = v; S.settings.pageNames = m; await S.db.doc('grade/settings').set(Object.assign({}, S.settings, {pageNames:m})); }
        toast(v ? `탭 이름을 "${v}"(으)로 바꿨어요.` : '원래 이름으로 돌렸어요.');
      } catch (er){ wErr(er, !isMe); }
    }
    renderStrip(); renderPageHead(); if (isMe) renderMe(); else renderTabPage();
  };
  inp.addEventListener('keydown', e => { if (e.key === 'Enter'){ e.preventDefault(); finish(true); } else if (e.key === 'Escape'){ e.preventDefault(); finish(false); } e.stopPropagation(); });
  inp.addEventListener('blur', () => finish(true));
  inp.addEventListener('click', e => { e.preventDefault(); e.stopPropagation(); });
}
$('#sheetbar').addEventListener('contextmenu', e => { const a = e.target.closest('a.stab[data-ren]'); if (!a || S.renaming) return; e.preventDefault(); startRename(a); });
$('#sheetbar').addEventListener('dblclick', e => { const a = e.target.closest('a.stab[data-ren]'); if (!a || S.renaming) return; e.preventDefault(); startRename(a); });

/* 학생 칸: 학급일지 탭에서는 메모·입력칸 오른쪽 위로 올려요 */
function placeStuCol(){
  const col = $('#stu-col'), dock = $('#stu-dock'), row = $('#me-row2'), board = $('#j-dayview');
  if (!col || !dock) return;
  const want = S.space === 'me' && S.meTab === 'day' && WK.mode !== 'week' && window.innerWidth > 740;
  const main = $('#me-main');
  if (!placeStuCol.home) placeStuCol.home = {p:main.parentElement, n:main.nextSibling};
  if (want && col.parentElement !== dock){ dock.appendChild(col); row.appendChild(main); }
  else if (!want && col.parentElement !== board){ board.appendChild(col); placeStuCol.home.p.insertBefore(main, placeStuCol.home.n); }
  dock.hidden = !want; row.classList.toggle('docked', want); board.classList.toggle('solo', want);
}
window.addEventListener('resize', () => { clearTimeout(placeStuCol.t); placeStuCol.t = setTimeout(placeStuCol, 150); });

/* ---------- 교실 도구 · 알림장 (내일 시간표 + 안전 문구) ---------- */
const NOTEP = () => `data/users/${S.uid}/noticebank`;
const NT_CATS = [
  ['rec', '이달 추천'], ['school', '학교 안전'], ['friend', '친구·학폭예방'], ['traffic', '교통'], ['life', '생활·가정'],
  ['health', '건강·감염병'], ['season', '계절·날씨'], ['media', '매체·사이버'], ['stranger', '낯선 사람'], ['vacation', '방학'], ['mine', '내 문구']
];
const NT_TAG = {school:'[안전교육]', friend:'[학폭예방]', traffic:'[교통안전]', life:'[생활안전]', health:'[건강]', season:'[안전교육]', media:'[매체안전]', stranger:'[안전교육]', vacation:'[방학안전]', mine:'[안전교육]'};
/* 기본으로 들어 있는 문구 (s: 어울리는 달) */
const NT_BANK = [
  ['school', '복도와 계단에서는 걸어서 다녀요.'],
  ['school', '계단은 오른쪽으로, 난간을 잡고 한 칸씩 다녀요.'],
  ['school', '교실에서 의자를 뒤로 젖히거나 의자로 장난치지 않아요.'],
  ['school', '문을 여닫을 때는 뒤에 친구가 있는지 먼저 살펴요.'],
  ['school', '책상이나 사물함 위에 올라가지 않아요.'],
  ['school', '가위·칼 같은 도구는 날을 내 쪽으로 해서 건네요.'],
  ['school', '운동장에서 모래를 뿌리거나 돌을 던지지 않아요.'],
  ['school', '체육 시간 전에는 준비 운동을 꼭 해요.'],
  ['school', '흥분했을 때일수록 한 번 멈추고 천천히 움직여요.'],
  ['school', '바닥에 떨어진 뾰족한 물건을 보면 선생님께 알려요.'],
  ['school', '화재 경보가 울리면 선생님을 따라 차분히 대피해요.'],
  ['school', '수업 시간에 방해되는 물건은 가방에 넣어 둬요.'],
  ['friend', '친구가 "하지 마"라고 하면 바로 멈춰요.'],
  ['friend', '나에게는 장난이어도 친구에게는 폭력일 수 있어요.'],
  ['friend', '친구의 이름이나 생김새로 놀리지 않아요.'],
  ['friend', '고운 말을 쓰고, 기분 나쁜 말은 한 번 더 생각해요.'],
  ['friend', '친구 물건은 허락받고 빌려요.'],
  ['friend', '"쟤랑 놀지 마" 같은 말로 친구를 따돌리지 않아요.'],
  ['friend', '친구의 사진은 허락 없이 찍거나 올리지 않아요.'],
  ['friend', '실수한 친구에게 비난 대신 격려를 건네요.'],
  ['friend', '친구끼리 돈이나 물건을 사 달라고 하지 않아요.'],
  ['friend', '친구를 껴안거나 잡아당기는 장난을 하지 않아요.'],
  ['friend', '친구를 갑자기 놀래키거나 몸에 손대지 않아요.'],
  ['friend', '힘든 일이 있으면 혼자 참지 말고 선생님·가족께 말해요.'],
  ['traffic', '횡단보도는 초록불이 켜져도 좌우를 살피고 건너요.'],
  ['traffic', '길을 건널 때는 휴대폰을 보지 않아요.'],
  ['traffic', '골목길에서는 일단 멈추고 차와 자전거를 살펴요.'],
  ['traffic', '자전거·킥보드를 탈 때는 헬멧을 꼭 써요.'],
  ['traffic', '횡단보도에서는 자전거에서 내려 끌고 건너요.'],
  ['traffic', '차에 타면 뒷자리에서도 안전띠를 매요.'],
  ['traffic', '도로 근처에서는 공놀이를 하지 않아요.'],
  ['traffic', '전기차는 소리가 작으니 뒤에서 오는 차도 살펴요.'],
  ['traffic', '비 오는 날에는 앞이 보이게 우산을 들고 걸어요.'],
  ['traffic', '학교가 끝나면 한곳에 머무르지 말고 바로 집에 가요.'],
  ['life', '창문 밖으로 몸을 내밀거나 물건을 던지지 않아요.'],
  ['life', '엘리베이터와 에스컬레이터에서는 장난치지 않아요.'],
  ['life', '젖은 손으로 콘센트나 전기 제품을 만지지 않아요.'],
  ['life', '가스레인지나 다리미는 어른과 함께 사용해요.'],
  ['life', '뜨거운 음식과 음료는 식혀서 조심히 먹어요.'],
  ['life', '꼬치 음식은 돌아다니지 말고 앉아서 먹어요.'],
  ['life', '구슬·동전 같은 작은 물건을 입에 넣지 않아요.'],
  ['life', '약은 어른이 주시는 만큼만 먹어요.'],
  ['life', '어디서든 안전 표지판을 읽고 지켜요.'],
  ['life', '집에 혼자 있을 때는 누가 와도 문을 열어 주지 않아요.'],
  ['health', '밥 먹기 전, 화장실 다녀온 뒤에는 비누로 손을 씻어요.'],
  ['health', '기침할 때는 옷소매로 입과 코를 가려요.'],
  ['health', '열이 나거나 아프면 무리하지 말고 쉬어요.'],
  ['health', '물을 자주 마시고 충분히 자요.'],
  ['health', '아침에 이를 닦고 와요.'],
  ['health', '감기 기운이 있으면 마스크를 써요.'],
  ['health', '눈이 가려워도 손으로 비비지 않아요.'],
  ['health', '음식은 냄새를 맡아 보고 이상하면 먹지 않아요.'],
  ['season', '더운 날에는 그늘에서 쉬고 물을 많이 마셔요.', [6, 7, 8]],
  ['season', '폭염 때는 한낮 바깥 활동을 줄여요.', [6, 7, 8]],
  ['season', '비 오는 날에는 미끄러운 바닥을 조심해요.', [6, 7, 8, 9]],
  ['season', '모기가 많은 곳에서는 긴 옷을 입고 기피제를 뿌려요.', [6, 7, 8, 9]],
  ['season', '아침저녁으로 쌀쌀하니 겉옷을 챙겨요.', [3, 4, 9, 10, 11]],
  ['season', '미세먼지가 나쁜 날에는 마스크를 쓰고 바깥 놀이를 줄여요.', [3, 4, 5, 11, 12, 1, 2]],
  ['season', '날씨가 추우니 따뜻하게 입고 다녀요.', [11, 12, 1, 2]],
  ['season', '공기가 건조하니 불조심해요.', [11, 12, 1, 2, 3]],
  ['season', '목도리가 차 문이나 엘리베이터에 끼지 않게 조심해요.', [11, 12, 1, 2]],
  ['season', '얼음이 언 길에서는 주머니에서 손을 빼고 천천히 걸어요.', [12, 1, 2]],
  ['season', '핫팩은 맨살에 바로 붙이지 않아요.', [11, 12, 1, 2]],
  ['season', '고드름 아래로는 지나가지 않아요.', [12, 1, 2]],
  ['media', '나이에 맞는 영상과 게임만 봐요.', null],
  ['media', '영상에서 본 위험한 장난을 따라 하지 않아요.'],
  ['media', '모르는 사람이 보낸 메시지에는 답하지 말고 가족께 알려요.'],
  ['media', '내 이름·학교·사는 곳을 인터넷에 올리지 않아요.'],
  ['media', '친구끼리 단체 채팅방에서 나쁜 말을 하지 않아요.'],
  ['media', '친구를 놀리는 글이나 사진을 퍼뜨리지 않아요.'],
  ['media', 'AI 서비스는 나이 기준을 지키고 어른과 함께 써요.'],
  ['media', '게임 아이템을 사려고 돈을 쓰거나 빌리지 않아요.'],
  ['stranger', '낯선 사람이 같이 가자고 하면 "싫어요" 하고 그 자리를 떠나요.'],
  ['stranger', '아는 사람이라도 가족 허락 없이 따라가지 않아요.'],
  ['stranger', '모르는 어른이 도와 달라고 하면 다른 어른께 부탁하라고 말해요.'],
  ['stranger', '모르는 차에는 가까이 가지 않고, 타지 않아요.'],
  ['stranger', '길을 잃으면 그 자리에서 멈추고 경찰이나 직원에게 도움을 청해요.'],
  ['stranger', '가족 전화번호를 외워 두어요.'],
  ['stranger', '아동안전지킴이집이 어디 있는지 알아 둬요.'],
  ['vacation', '물놀이할 때는 구명조끼를 입고 깊은 곳에 가지 않아요.', [7, 8]],
  ['vacation', '친구가 물에 빠지면 직접 들어가지 말고 어른을 불러요.', [7, 8]],
  ['vacation', '음식은 냉장고에 보관하고, 상한 것 같으면 먹지 않아요.', [7, 8]],
  ['vacation', '외출할 때는 누구와 어디에 가는지 가족께 말해요.', [7, 8, 12, 1, 2]],
  ['vacation', '가족 허락 없이 친구 집에 가거나 친구를 데려오지 않아요.', [7, 8, 12, 1, 2]],
  ['vacation', '방학에도 일찍 자고 일찍 일어나요.', [7, 8, 12, 1, 2]],
  ['vacation', '눈썰매·스케이트를 탈 때는 보호 장비를 해요.', [12, 1, 2]],
  ['vacation', '전기장판·난로를 켜 둔 채 외출하지 않아요.', [12, 1, 2]]
];
const NT_REC = {1:['vacation', 'season'], 2:['vacation', 'season', 'school'], 3:['school', 'friend', 'traffic'], 4:['traffic', 'friend', 'media'], 5:['traffic', 'life', 'health'],
  6:['season', 'health', 'life'], 7:['vacation', 'season', 'health'], 8:['vacation', 'season'], 9:['school', 'friend', 'health'], 10:['friend', 'life', 'traffic'],
  11:['season', 'school', 'friend'], 12:['vacation', 'season', 'stranger']};
const NT = {cat:'rec', tag:'auto', pick:null, draft:{}, bank:{items:[], used:{}}, loaded:false, sub:null};
function ntLoad(){
  if (NT.sub || !S.uid || !S.db) return;
  NT.sub = S.db.doc(NOTEP()).onSnapshot(snap => {
    if (busy(NOTEP())) return;
    const localDrafts = (NT.bank && NT.bank.drafts) || {};
    NT.bank = snap.exists ? JSON.parse(JSON.stringify(snap.data())) : {items:[], used:{}};
    NT.bank.drafts = Object.assign({}, NT.bank.drafts || {});
    Object.keys(NT.draftTs || {}).forEach(x => { if (Date.now() - NT.draftTs[x] < 15000 && localDrafts[x] != null) NT.bank.drafts[x] = localDrafts[x]; });
    if (NT.pickFor && Date.now() - (NT.pickTs || 0) < 15000) NT.bank.picks = Object.assign({}, NT.bank.picks, {[NT.pickFor]:NT.pick ? NT.pick.t : ''});
    else if (NT.pickFor && NT.bank.picks && NT.bank.picks[NT.pickFor] != null && (!NT.pick || NT.bank.picks[NT.pickFor] !== NT.pick.t)) NT.pickFor = null;
    if (!Array.isArray(NT.bank.items)) NT.bank.items = []; if (!NT.bank.used) NT.bank.used = {}; if (!NT.bank.drafts) NT.bank.drafts = {};
    const k = ntTarget(), saved = NT.bank.drafts[k];
    if (saved != null && document.activeElement !== $('#nt-text') && !(NT.draftTs && Date.now() - (NT.draftTs[k] || 0) < 15000)) NT.draft[k] = saved;
    NT.loaded = true; if (T.tool === 'note' && !$('#tools').hidden) renderNoteTool();
  }, () => {});
}
const ntSave = () => queueSet(NOTEP(), () => ({items:NT.bank.items, used:NT.bank.used, drafts:NT.bank.drafts || {}, picks:NT.bank.picks || {}, sbUrl:NT.bank.sbUrl || '', updatedAt:Date.now()}), false);
/* 쓰던 알림장은 날짜별로 저장해 두어요 (최근 3주) */
let ntDraftTimer;
function ntKeepDraft(k, v){
  if (!S.uid) return;
  NT.draftTs = NT.draftTs || {}; NT.draftTs[k] = Date.now();
  const d = Object.assign({}, NT.bank.drafts || {}); d[k] = v;
  const lim = ymd(addDays(today(), -21)); Object.keys(d).forEach(x => { if (x < lim) delete d[x]; });
  NT.bank.drafts = d;
  clearTimeout(ntDraftTimer); ntDraftTimer = setTimeout(ntSave, 800);
}
function ntAll(){
  const mine = (NT.bank.items || []).map(x => ({c:'mine', t:x.t, sub:x.c || ''}));
  return NT_BANK.map(([c, t, s]) => ({c, t, s})).concat(mine);
}
function ntList(cat){
  const m = today().getMonth() + 1;
  const fits = x => !x.s || x.s.includes(m);
  const all = ntAll();
  if (cat === 'rec'){ const cs = NT_REC[m] || []; return all.filter(x => (cs.includes(x.c) || x.c === 'mine') && fits(x)); }
  if (cat === 'mine') return all.filter(x => x.c === 'mine');
  return all.filter(x => x.c === cat).sort((a, b) => (fits(b) ? 1 : 0) - (fits(a) ? 1 : 0));
}
function ntFresh(list){
  const used = NT.bank.used || {}, lim = ymd(addDays(today(), -45));
  const fresh = list.filter(x => !(used[x.t] && used[x.t] >= lim));
  return fresh.length ? fresh : list;
}
function ntTarget(){ return nextSchoolDay(ymd(today())); }
function ntAbbr(s){ s = String(s || '').trim(); if (!s) return ''; const m = {'창체':'창', '자율':'자', '동아리':'동', '학교자율':'학', '융':'학', '진로':'진'}; return m[s] || s[0]; }
async function ntCompose(force){
  const k = ntTarget();
  if (!force && !NT.loaded) for (let i = 0; i < 30 && !NT.loaded; i++) await new Promise(r => setTimeout(r, 100));
  if (!force && NT.draft[k] == null && NT.bank.drafts && NT.bank.drafts[k] != null) NT.draft[k] = NT.bank.drafts[k];
  if (!force && NT.draft[k] != null) return NT.draft[k];
  const sj = subjFor(k);
  let plan = [];
  try { const sn = await S.db.doc(DAYPATH(k)).get(); plan = (sn.exists && sn.data().plan) || []; } catch (e){}
  const subs = (sj.s || []).map((x, i) => (plan[i] && plan[i].s) || x).filter(Boolean);
  const lines = [];
  if (subs.length) lines.push(subs.map(ntAbbr).join(''));
  const prep = plan.map(p => (p && p.p || '').trim()).filter(Boolean);
  if (prep.length) lines.push('준비물: ' + [...new Set(prep)].join(', '));
  schoolEvents(k).filter(Boolean).slice(0, 2).forEach(t => lines.push(t));
  if (NT.pick) lines.push(ntTagFor(NT.pick) + NT.pick.t);
  NT.draft[k] = lines.map((l, i) => `${i + 1}.${l}`).join('\n');
  ntKeepDraft(k, NT.draft[k]);
  return NT.draft[k];
}
function ntTagFor(x){ if (NT.tag === 'none') return ''; if (NT.tag !== 'auto') return NT.tag; return NT_TAG[x.c] || '[안전교육]'; }
function ntRandom(){
  const list = ntFresh(ntList(NT.cat === 'mine' && !ntList('mine').length ? 'rec' : NT.cat));
  NT.pick = list[Math.floor(Math.random() * list.length)] || null;
  ntRememberPick();
}
/* 그날 고른 안전 문구는 저장해 두고, 다시 열어도 바뀌지 않게 해요 */
function ntRememberPick(){
  if (!S.uid) return;
  const k = ntTarget(); NT.pickFor = k; NT.pickTs = Date.now();
  const p = Object.assign({}, NT.bank.picks || {}); p[k] = NT.pick ? NT.pick.t : '';
  const lim = ymd(addDays(today(), -21)); Object.keys(p).forEach(x => { if (x < lim) delete p[x]; });
  NT.bank.picks = p; clearTimeout(ntDraftTimer); ntDraftTimer = setTimeout(ntSave, 800);
}
function ntRestorePick(k){
  const all = ntAll(), saved = (NT.bank.picks || {})[k];
  if (saved != null) return saved ? (all.find(x => x.t === saved) || {c:'mine', t:saved}) : null;
  const d = (NT.bank.drafts || {})[k];
  if (d) return all.filter(x => d.includes(x.t)).sort((a, b) => b.t.length - a.t.length)[0] || null;
  return undefined;
}
function ntApplyPick(){
  const k = ntTarget(); const cur = $('#nt-text').value;
  const lines = cur.split('\n').filter(l => l.trim());
  const bare = l => l.replace(/^\d+\.\s*/, ''); const isSafe = l => /^\d+\.\s*\[[^\]]*\]/.test(l) || (NT.lastPickLine && bare(l) === bare(NT.lastPickLine));
  const kept = lines.filter(l => !isSafe(l)).map(l => l.replace(/^\d+\.\s*/, ''));
  if (NT.pick) kept.push(ntTagFor(NT.pick) + NT.pick.t);
  NT.draft[k] = kept.map((l, i) => `${i + 1}.${l}`).join('\n');
  NT.lastPickLine = NT.pick ? `${kept.length}.${ntTagFor(NT.pick) + NT.pick.t}` : null;
  $('#nt-text').value = NT.draft[k];
  ntKeepDraft(k, NT.draft[k]);
}
async function renderNoteTool(){
  ntLoad();
  const k = ntTarget(), d = fromYmd(k), t0 = today();
  /* 알림장 날짜는 쓰는 날(오늘), 내용은 다음 등교일 준비 */
  NT.title = `${t0.getMonth() + 1}월 ${t0.getDate()}일 ${WD[t0.getDay()]}요일 알림장`;
  $('#nt-for').innerHTML = `${esc(NT.title)} <small style="font-weight:400;color:var(--muted)">· ${d.getMonth() + 1}/${d.getDate()}(${WD[d.getDay()]}) 준비</small>`;
  if (!S.uid){ $('#nt-text').value = ''; $('#nt-text').placeholder = '로그인한 상태로 열어야 쓸 수 있어요.'; return; }
  if (!NT.loaded) for (let i = 0; i < 80 && !NT.loaded; i++) await new Promise(r => setTimeout(r, 100));
  if (!NT.loaded){ $('#nt-text').placeholder = '쓰던 알림장을 불러오는 중이에요…'; return; }
  if (NT.pickFor !== k){ const r = ntRestorePick(k); if (r === undefined){ NT.pick = null; ntRandom(); } else { NT.pick = r; NT.pickFor = k; } }
  if (document.activeElement !== $('#nt-text')){ $('#nt-text').value = await ntCompose(false); NT.lastPickLine = NT.pick ? $('#nt-text').value.split('\n').slice(-1)[0] : null; }
  $('#nt-cats').innerHTML = NT_CATS.map(([c, n]) => `<button type="button" class="stab" data-ntc="${c}" ${NT.cat === c ? 'aria-current="page"' : ''}>${n}${c === 'mine' ? ` <small>${(NT.bank.items || []).length}</small>` : ''}</button>`).join('');
  $('#nt-tag').value = NT.tag;
  if (document.activeElement !== $('#nt-sb-url')) $('#nt-sb-url').value = NT.bank.sbUrl || '';
  const list = ntList(NT.cat), used = NT.bank.used || {};
  $('#nt-list').innerHTML = list.length ? list.map(x => `<li class="${NT.pick && NT.pick.t === x.t ? 'on' : ''}"><button type="button" class="nt-p" data-ntp="${esc(x.t)}"><span class="t">${esc(x.t)}</span>${used[x.t] ? `<span class="u">${fmtMD(used[x.t])} 씀</span>` : ''}</button>${x.c === 'mine' ? `<button type="button" class="x" data-ntdel="${esc(x.t)}" aria-label="내 문구에서 빼기">×</button>` : ''}</li>`).join('')
    : `<li class="hint">${NT.cat === 'mine' ? '아래 "내 문구 넣기"에 지난 알림장 안전 문구를 붙여 넣어 두면 여기서 골라 쓸 수 있어요.' : '이 분류에는 문구가 없어요.'}</li>`;
}
async function ntCopy(){
  const v = $('#nt-text').value;
  try { await navigator.clipboard.writeText(v); toast('알림장을 복사했어요. 학교종이에 붙여 넣으면 돼요.'); }
  catch (e){ $('#nt-text').select(); toast('글을 골라 두었어요. Ctrl+C로 복사해 주세요.'); }
  if (NT.pick && S.uid){ NT.bank.used = Object.assign({}, NT.bank.used, {[NT.pick.t]:ymd(today())}); const ks = Object.keys(NT.bank.used); if (ks.length > 400) ks.sort((a, b) => NT.bank.used[a] < NT.bank.used[b] ? -1 : 1).slice(0, ks.length - 400).forEach(x => delete NT.bank.used[x]); ntSave(); }
}
$('#nt-copy').onclick = ntCopy;
$('#nt-send').onclick = async () => {
  const u = NT.bank.sbUrl || '';
  if (!/^https:[/][/]([a-z0-9-]+\.)*schoolbell-e\.com[/]/i.test(u)){ $('#nt-sb').open = true; $('#nt-sb-url').focus(); toast('먼저 아래 "학교종이 알림장 주소"를 한 번만 넣어 주세요.'); return; }
  let w = null; try { w = window.open(u, '_blank'); if (w) w.opener = null; } catch (e){}
  await ntCopy();
  if (!w) toast('복사했어요. 학교종이를 열어 알림장 "작성하기"에 붙여 넣어 주세요.');
  else toast('복사했어요. 열린 학교종이에서 "작성하기"를 누르고 Ctrl+V 하세요.');
};
$('#nt-sb-form').addEventListener('submit', e => {
  e.preventDefault(); const u = $('#nt-sb-url').value.trim();
  if (!/^https:[/][/]([a-z0-9-]+\.)*schoolbell-e\.com[/]/i.test(u)){ toast('학교종이(schoolbell-e.com) 주소를 넣어 주세요.'); return; }
  NT.bank.sbUrl = u; ntSave(); $('#nt-sb').open = false; toast('학교종이 알림장 주소를 저장했어요.');
});
$('#big-body').addEventListener('input', () => {
  if (S.bigMode !== 'note') return;
  const v = $('#big-body').innerText.replace(/\n{3,}/g, '\n\n').replace(/\s+$/, '');
  const k = ntTarget(); NT.draft[k] = v; $('#nt-text').value = v; ntKeepDraft(k, v);
});
$('#nt-big').onclick = async () => {
  $('#big-title').textContent = NT.title || $('#nt-for').textContent;
  $('#big-body').textContent = $('#nt-text').value || '아직 알림장이 비어 있어요.';
  $('#big-imgs').innerHTML = '';
  $('#big').hidden = false;
  S.bigMode = 'note'; $('#big-hint').textContent = '글을 눌러 고쳐 쓰면 알림장에 바로 저장돼요';
};
$('#nt-redo').onclick = async () => { $('#nt-text').value = await ntCompose(true); NT.lastPickLine = NT.pick ? $('#nt-text').value.split('\n').slice(-1)[0] : null; toast('내일 시간표로 다시 만들었어요.'); };
$('#nt-dice').onclick = () => { ntRandom(); ntApplyPick(); renderNoteTool(); };
$('#nt-tag').addEventListener('change', e => { NT.tag = e.target.value; ntApplyPick(); });
/* 줄 중간에서 엔터를 치면 새 줄에 번호를 붙이고, 아래 줄 번호(안전 문구 포함)를 하나씩 밀어요 */
function ntRenumber(ta){
  const pos = ta.selectionStart, v = ta.value;
  const before = v.slice(0, pos), after = v.slice(pos);
  const lines = before.split('\n'), cur = lines[lines.length - 1], prev = lines[lines.length - 2];
  let ins = '';
  if (prev != null && /^\d+\./.test(prev) && cur === '' && !/^\d+\./.test(after)) ins = '0.';
  const all = (before + ins + after).split('\n');
  let n = 0; const caretLine = lines.length - 1;
  const out = all.map(l => { const m = l.match(/^(\d+)\.(.*)$/); if (!m) return l; n++; return n + '.' + m[2]; });
  const lenBefore = out.slice(0, caretLine).join('\n').length + (caretLine ? 1 : 0);
  const caretLineNew = out[caretLine], caretCol = cur.length;
  const oldPrefix = (cur.match(/^\d+\./) || [''])[0], newPrefix = ((caretLineNew || '').match(/^\d+\./) || [''])[0];
  const col = ins ? newPrefix.length : (oldPrefix && caretCol >= oldPrefix.length ? caretCol + (newPrefix.length - oldPrefix.length) : caretCol);
  ta.value = out.join('\n');
  ta.selectionStart = ta.selectionEnd = lenBefore + Math.max(0, col);
}
$('#nt-text').addEventListener('input', e => { if (e.inputType === 'insertLineBreak' || e.inputType === 'insertParagraph' || e.inputType === 'insertText' && e.data === '\n') ntRenumber(e.target); });
$('#nt-text').addEventListener('input', e => { const k = ntTarget(); NT.draft[k] = e.target.value; ntKeepDraft(k, e.target.value); });
$('#nt-cats').addEventListener('click', e => { const b = e.target.closest('[data-ntc]'); if (!b) return; NT.cat = b.dataset.ntc; renderNoteTool(); });
$('#nt-list').addEventListener('click', e => {
  const del = e.target.closest('[data-ntdel]');
  if (del){ NT.bank.items = (NT.bank.items || []).filter(x => x.t !== del.dataset.ntdel); ntSave(); renderNoteTool(); return; }
  const b = e.target.closest('[data-ntp]'); if (!b) return;
  NT.pick = ntAll().find(x => x.t === b.dataset.ntp) || null; ntRememberPick(); ntApplyPick(); renderNoteTool();
});
$('#nt-import').addEventListener('submit', e => {
  e.preventDefault(); if (!S.uid){ toast('로그인한 상태에서만 넣을 수 있어요.'); return; }
  const have = new Set((NT.bank.items || []).map(x => x.t).concat(NT_BANK.map(x => x[1])));
  let n = 0;
  $('#nt-paste').value.split('\n').forEach(l => {
    let t = l.trim().replace(/^[A-Z]?\d+\s*[|.)\t]\s*/, '').replace(/^\d+월\s*\d+일\s*[|\t]\s*/, '').replace(/^\[[^\]]*\]\s*/, '').trim();
    if (t.length < 4 || t.length > 120 || have.has(t)) return;
    have.add(t); NT.bank.items.push({t, c:'', at:Date.now()}); n++;
  });
  if (NT.bank.items.length > 800) NT.bank.items = NT.bank.items.slice(-800);
  $('#nt-paste').value = ''; ntSave(); NT.cat = 'mine'; renderNoteTool();
  toast(n ? `내 문구 ${n}개를 넣었어요.` : '새로 넣을 문구가 없어요. 이미 있거나 너무 짧아요.');
});

/* ---------- 특별 수업 일정 (반별 교시 배정 · 겹침 확인 · 빈 시간 찾기) ---------- */
const LS = {mon:null, view:'week', prog:'all', cls:'all', jd:{}, rows:[], editId:null, jdCls:'1반'};
const LS_PER = 6;
const lsClasses = () => Array.from({length:Math.max(1, Math.min(20, +S.settings.classCount || 4))}, (_, i) => (i + 1) + '반');
const lsOverlap = (a, b) => (a || []).some(x => (b || []).includes(x));
function lsJd(cls, k){ const wd = fromYmd(k).getDay(); const row = ((LS.jd[cls] || {})[wd]) || []; return row; }
function lsConflicts(k, pers, cls, ignoreId, prog, extra){
  const out = [];
  if (!k || !pers || !pers.length || !cls) return out;
  const d = fromYmd(k), wd = d.getDay();
  if (wd === 0 || wd === 6 || HOLIDAYS[k]) out.push(HOLIDAYS[k] || '주말');
  const jd = lsJd(cls, k);
  pers.forEach(p => { if (jd[p - 1]) out.push(`${p}교시 ${jd[p - 1]}`); });
  (S.lessons || []).concat(extra || []).forEach(l => {
    if (l.id && l.id === ignoreId) return;
    if (l.date !== k || !lsOverlap(l.pers, pers)) return;
    if (l.cls === cls) out.push(l.prog || '다른 수업');
  });
  return [...new Set(out)];
}
const lsPerLabel = p => (p || []).length > 1 ? `${p[0]}~${p[p.length - 1]}교시` : `${(p || [])[0] || '?'}교시`;
function lsYear(m, d){
  const t = today(), y = t.getFullYear();
  const cands = [y - 1, y, y + 1].map(yy => new Date(yy, m - 1, d));
  cands.sort((a, b) => Math.abs(a - t - 60 * 864e5) - Math.abs(b - t - 60 * 864e5));
  return ymd(cands[0]);
}
/* 붙여 넣은 표·글에서 날짜·교시·반을 찾아요 */
function lsParse(text){
  const names = lsClasses().map(c => ({c, keys:[clsLabel(c), clsLabel(c).replace(/반$/, '')].filter((x, i, a) => x && x.length > 1 && a.indexOf(x) === i)}));
  const out = [];
  text.split(/\n/).forEach(line => {
    if (!line.trim()) return;
    const toks = [];
    line.replace(/(\d{1,2})\s*[.\/월]\s*(\d{1,2})\s*[.일]?/g, (m, a, b, i) => { if (+a >= 1 && +a <= 12 && +b >= 1 && +b <= 31) toks.push({t:'d', i, v:lsYear(+a, +b)}); return m; });
    line.replace(/(\d)\s*(?:[~∼～-]\s*(\d)\s*)?교시/g, (m, a, b, i) => { const s = +a, e = b ? +b : s; const v = []; for (let p = s; p <= e && p <= 8; p++) v.push(p); toks.push({t:'p', i, v}); return m; });
    names.forEach(({c, keys}) => keys.forEach(kw => { let i = line.indexOf(kw); while (i >= 0){ toks.push({t:'c', i, v:c}); i = line.indexOf(kw, i + kw.length); } }));
    line.replace(/(?:^|[^\d])(\d{1,2})\s*반/g, (m, a, i) => { if (+a >= 1 && +a <= 20) toks.push({t:'c', i, v:(+a) + '반'}); return m; });
    line.replace(/\b\d\s*-\s*(\d{1,2})\b(?!\s*교시)/g, (m, a, i) => { if (+a <= 20) toks.push({t:'c', i, v:(+a) + '반'}); return m; });
    const cs = toks.filter(x => x.t === 'c'), ds = toks.filter(x => x.t === 'd'), ps = toks.filter(x => x.t === 'p');
    if (!ds.length && !cs.length) return;
    const near = (arr, i) => arr.reduce((b, x) => !b || Math.abs(x.i - i) < Math.abs(b.i - i) ? x : b, null);
    const seen = new Set();
    (cs.length ? cs : [{v:'', i:(ds[0] || {}).i || 0}]).forEach(c => {
      const d = near(ds, c.i), p = near(ps, c.i);
      const row = {date:d ? d.v : '', pers:p ? p.v : [], cls:c.v};
      const key = row.date + row.pers.join() + row.cls;
      if (seen.has(key)) return; seen.add(key); out.push(row);
    });
  });
  return out;
}
/* 빈 시간 찾기: 반 순서대로, 기간 안에서 겹치지 않는 가장 이른 자리를 골라요 */
function lsAuto(o){
  const res = [], taken = [];
  let cur = o.from;
  const days = []; for (let d = fromYmd(o.from); ymd(d) <= o.to; d = addDays(d, 1)) days.push(ymd(d));
  const ok = (k, pers, cls) => {
    const wd = fromYmd(k).getDay();
    if (!o.wds.includes(wd)) return false;
    if (!pers.every(p => o.pers.includes(p))) return false;
    if (lsConflicts(k, pers, cls, null, o.prog, taken).length) return false;
    if (o.oneAtATime && (S.lessons || []).concat(taken).some(l => l.prog === o.prog && l.date === k && lsOverlap(l.pers, pers))) return false;
    if (o.onePerDay && taken.some(l => l.date === k && l.cls !== cls)) return false;
    return true;
  };
  for (let r = 0; r < o.times; r++){
    for (const cls of o.order){
      let found = null;
      for (const k of days){
        if (o.keepOrder && k < cur) continue;
        for (let p = 1; p + o.len - 1 <= LS_PER; p++){
          const pers = Array.from({length:o.len}, (_, i) => p + i);
          if (ok(k, pers, cls)){ found = {date:k, pers, cls}; break; }
        }
        if (found) break;
      }
      if (found){ taken.push(Object.assign({prog:o.prog}, found)); res.push(Object.assign({ok:true}, found)); if (o.keepOrder) cur = found.date; }
      else res.push({date:'', pers:[], cls, ok:false});
    }
  }
  return res;
}
function lsWeekStart(){ if (!LS.mon) LS.mon = mondayOf(ymd(today())); return LS.mon; }
function renderLessons(){
  if (S.page !== 'lessons' || S.space !== 'grade') return;
  const mon = lsWeekStart(), days = [0, 1, 2, 3, 4].map(i => ymd(addDays(fromYmd(mon), i)));
  const all = (S.lessons || []).slice().sort((a, b) => a.date < b.date ? -1 : a.date > b.date ? 1 : (a.pers[0] || 0) - (b.pers[0] || 0));
  const progs = [...new Set(all.map(l => l.prog).filter(Boolean))];
  if (LS.prog !== 'all' && !progs.includes(LS.prog)) LS.prog = 'all';
  $('#ls-prog').innerHTML = `<option value="all">모든 수업</option>` + progs.map(p => `<option ${LS.prog === p ? 'selected' : ''}>${esc(p)}</option>`).join('');
  $('#ls-cls').innerHTML = `<option value="all">모든 반</option>` + lsClasses().map(c => `<option value="${c}" ${LS.cls === c ? 'selected' : ''}>${esc(clsLabel(c))}</option>`).join('');
  $$('#ls-view button').forEach(b => b.setAttribute('aria-pressed', b.dataset.v === LS.view));
  const pick = l => (LS.prog === 'all' || l.prog === LS.prog) && (LS.cls === 'all' || l.cls === LS.cls);
  const s = fromYmd(mon), e = addDays(s, 4);
  if (!LS.month){ const t = today(); LS.month = new Date(t.getFullYear(), t.getMonth(), 1); }
  $('#ls-label').textContent = LS.view === 'month' ? `${LS.month.getFullYear()}. ${LS.month.getMonth() + 1}월` : `${s.getMonth() + 1}.${s.getDate()} ~ ${e.getMonth() + 1}.${e.getDate()}`;
  $('#ls-today').textContent = LS.view === 'month' ? '이번 달' : '이번 주';
  $('#ls-weeknav').hidden = LS.view === 'list';
  $('#ls-week').hidden = LS.view !== 'week'; $('#ls-month').hidden = LS.view !== 'month'; $('#ls-list').hidden = LS.view !== 'list';
  if (LS.view === 'month'){
    const m = LS.month, first = fromYmd(mondayOf(ymd(m)));
    let h = '<table class="ls-mt"><thead><tr>' + ['월', '화', '수', '목', '금'].map(w => `<th>${w}</th>`).join('') + '</tr></thead><tbody>';
    for (let w = 0; w < 6; w++){
      const mon = addDays(first, w * 7);
      if (w > 0 && mon.getMonth() !== m.getMonth() && mon > m) break;
      h += '<tr>' + [0, 1, 2, 3, 4].map(i => {
        const d = addDays(mon, i), k = ymd(d), out = d.getMonth() !== m.getMonth();
        const ls = all.filter(l => l.date === k && pick(l));
        return `<td class="${out ? 'out' : ''} ${k === ymd(today()) ? 'today' : ''}"><div class="ls-md"><b>${d.getDate()}</b>${HOLIDAYS[k] ? ` <small class="hol">${esc(HOLIDAYS[k])}</small>` : ''}</div>${ls.map(l => { const bad = lsConflicts(l.date, l.pers, l.cls, l.id).length; return `<button type="button" class="ls-chip sm ${bad ? 'bad' : ''}" data-ls="${l.id}" title="${esc(l.prog + (l.teacher ? ' · ' + l.teacher : '') + (l.place ? ' · ' + l.place : ''))}"><span class="p">${lsPerLabel(l.pers)}</span> ${esc(clsLabel(l.cls))}<small>(${esc(l.prog)})</small></button>`; }).join('')}</td>`;
      }).join('') + '</tr>';
    }
    $('#ls-month').innerHTML = `<div class="tablewrap">${h}</tbody></table></div>`;
  }
  if (LS.view === 'week'){
    const evRow = days.map(k => { const t = (S.events || []).filter(x => x.date === k && (!x.who || x.who === '전체')).map(x => x.title).concat(schoolEvents(k)); return `<td class="ls-ev">${HOLIDAYS[k] ? `<b>${esc(HOLIDAYS[k])}</b> ` : ''}${t.slice(0, 3).map(esc).join('<br>')}</td>`; }).join('');
    let h = `<table class="ls-tt"><thead><tr><th></th>${days.map(k => { const d = fromYmd(k); return `<th class="${k === ymd(today()) ? 'today' : ''}">${d.getMonth() + 1}월 ${d.getDate()}일 <small>${WD[d.getDay()]}</small></th>`; }).join('')}</tr></thead><tbody><tr><th class="ls-evh">학사일정</th>${evRow}</tr>`;
    for (let p = 1; p <= LS_PER; p++){
      h += `<tr><th>${p}</th>` + days.map(k => {
        const ls = all.filter(l => l.date === k && (l.pers || []).includes(p) && pick(l));
        const jd = LS.cls !== 'all' ? (lsJd(LS.cls, k)[p - 1] || '') : '';
        return `<td>${jd ? `<span class="ls-jd">${esc(jd)}</span>` : ''}${ls.map(l => { const bad = lsConflicts(l.date, l.pers, l.cls, l.id).length; return `<button type="button" class="ls-chip ${bad ? 'bad' : ''}" data-ls="${l.id}" title="${esc(l.prog + ' · ' + clsLabel(l.cls) + ' ' + lsPerLabel(l.pers) + (l.teacher ? ' · ' + l.teacher : '') + (l.place ? ' · ' + l.place : ''))}">${esc(clsLabel(l.cls))}<small>(${esc(l.prog)})</small></button>`; }).join('')}</td>`;
      }).join('') + '</tr>';
    }
    $('#ls-week').innerHTML = `<div class="tablewrap">${h}</tbody></table></div>`;
  } else {
    const list = all.filter(pick);
    const groups = {}; list.forEach(l => { (groups[l.prog || '이름 없음'] = groups[l.prog || '이름 없음'] || []).push(l); });
    $('#ls-list').innerHTML = Object.keys(groups).length ? Object.entries(groups).map(([g, ls]) => `<section class="ls-g"><h3>${esc(g)} <small>${ls.length}번</small></h3><div class="tablewrap"><table class="ls-lt"><thead><tr><th>날짜</th><th>교시</th><th>반</th><th>담당·장소</th><th></th></tr></thead><tbody>${ls.map(l => { const bad = lsConflicts(l.date, l.pers, l.cls, l.id); return `<tr class="${bad.length ? 'bad' : ''}"><td>${fmtMD(l.date)}</td><td>${lsPerLabel(l.pers)}</td><td>${esc(clsLabel(l.cls))}</td><td>${esc([l.teacher, l.place].filter(Boolean).join(' · '))}${bad.length ? ` <span class="ls-warn">겹침: ${esc(bad.join(', '))}</span>` : ''}</td><td>${S.canWrite ? `<button type="button" class="btn small" data-ls="${l.id}">고치기</button>` : ''}</td></tr>`; }).join('')}</tbody></table></div></section>`).join('')
      : '<p class="empty">아직 넣은 특별 수업이 없어요. "+ 일정 넣기"에서 모집 표를 그대로 붙여 넣거나, "빈 시간 찾아 정하기"로 반별 시간을 정해 보세요.</p>';
  }
}
/* 미리 보기 표 (붙여 넣기 · 빈 시간 찾기 공용) */
function lsRowsHtml(){
  const opts = c => lsClasses().map(x => `<option value="${x}" ${x === c ? 'selected' : ''}>${esc(clsLabel(x))}</option>`).join('');
  const per = p => [1, 2, 3, 4, 5, 6].map(x => `<label class="ls-pc"><input type="checkbox" data-lsp="${x}" ${(p || []).includes(x) ? 'checked' : ''}>${x}</label>`).join('');
  const prog = $('#lsf-prog').value.trim();
  return LS.rows.length ? `<table class="ls-pv"><thead><tr><th></th><th>날짜</th><th>교시</th><th>반</th><th>확인</th></tr></thead><tbody>${LS.rows.map((r, i) => {
    const bad = r.date && r.pers.length && r.cls ? lsConflicts(r.date, r.pers, r.cls, null, prog, LS.rows.filter((x, j) => j !== i && x.on)) : ['날짜·교시·반을 채워 주세요'];
    return `<tr data-lsr="${i}" class="${bad.length ? 'bad' : ''}"><td><input type="checkbox" data-lsf="on" ${r.on ? 'checked' : ''} aria-label="넣기"></td><td><input type="date" data-lsf="date" value="${r.date}"></td><td class="ls-pcs">${per(r.pers)}</td><td><select data-lsf="cls"><option value="">반</option>${opts(r.cls)}</select></td><td>${bad.length ? `<span class="ls-warn">${esc(bad.join(', '))}</span>` : '<span class="ls-ok">비어 있어요</span>'}</td></tr>`;
  }).join('')}</tbody></table>` : '<p class="hint" style="margin:0">아직 고른 시간이 없어요.</p>';
}
function lsRenderRows(){ $('#lsf-rows').innerHTML = lsRowsHtml(); $('#lsf-n').textContent = LS.rows.filter(r => r.on).length; $('#lsf-bulk').hidden = false; }
$('#lsb-date-go').onclick = () => { const v = $('#lsb-date').value; if (!v){ toast('맞출 날짜를 골라 주세요.'); return; } LS.rows.forEach(r => { if (r.on) r.date = v; }); lsRenderRows(); };
$('#lsb-per-go').onclick = () => { const ps = $$('#lsb-pers input:checked').map(x => +x.value); if (!ps.length){ toast('맞출 교시를 골라 주세요.'); return; } LS.rows.forEach(r => { if (r.on) r.pers = ps.slice(); }); lsRenderRows(); };
$('#lsb-all').onclick = () => {
  const v = $('#lsb-date').value || ymd(today()), ps = $$('#lsb-pers input:checked').map(x => +x.value);
  const have = new Set(LS.rows.map(r => r.cls));
  lsClasses().forEach(c => { if (!have.has(c)) LS.rows.push({on:true, date:v, pers:ps.slice(), cls:c}); });
  lsRenderRows();
};
function lsOpenAdd(){
  if (!S.canWrite){ toast('학년 공간을 고칠 권한이 없어요.'); return; }
  LS.rows = []; $('#lsf-paste').value = ''; $('#lsf-prog').value = LS.prog !== 'all' ? LS.prog : ''; $('#lsf-teacher').value = ''; $('#lsf-place').value = '';
  $('#lsf-progs').innerHTML = [...new Set((S.lessons || []).map(l => l.prog).filter(Boolean))].map(p => `<option value="${esc(p)}">`).join('');
  const t = ymd(today()); $('#lsa-from').value = t; $('#lsa-to').value = ymd(addDays(today(), 28));
  lsRenderRows(); lsTab('paste'); closeDlgs(); openDlg('#dlg-ls');
}
function lsTab(t){ $$('#lsf-tabs button').forEach(b => b.setAttribute('aria-pressed', b.dataset.t === t)); $('#lsf-pastebox').hidden = t !== 'paste'; $('#lsf-autobox').hidden = t !== 'auto'; }
$('#ls-add').onclick = () => { lsOpenAdd(); };
$('#ls-auto').onclick = () => { lsOpenAdd(); lsTab('auto'); };
$('#lsf-tabs').addEventListener('click', e => { const b = e.target.closest('button[data-t]'); if (b) lsTab(b.dataset.t); });
$('#lsf-parse').onclick = () => {
  const rows = lsParse($('#lsf-paste').value);
  if (!rows.length){ toast('날짜·교시·반을 찾지 못했어요. "11/18 2교시 1반"처럼 한 줄에 하나씩 적어도 돼요.'); return; }
  LS.rows = LS.rows.concat(rows.map(r => Object.assign({on:true}, r))); lsRenderRows();
};
$('#lsf-one').onclick = () => { LS.rows.push({on:true, date:ymd(today()), pers:[], cls:''}); lsRenderRows(); };
$('#lsf-find').onclick = () => {
  const prog = $('#lsf-prog').value.trim() || '특별 수업';
  const order = lsClasses().slice(); if ($('#lsa-rev').checked) order.reverse();
  const o = {prog, from:$('#lsa-from').value, to:$('#lsa-to').value, times:Math.max(1, Math.min(10, +$('#lsa-times').value || 1)), len:Math.max(1, Math.min(3, +$('#lsa-len').value || 1)),
    wds:$$('#lsa-wds input:checked').map(x => +x.value), pers:$$('#lsa-pers input:checked').map(x => +x.value), order, oneAtATime:$('#lsa-one').checked, onePerDay:$('#lsa-day').checked, keepOrder:$('#lsa-keep').checked};
  if (!o.from || !o.to || o.to < o.from){ toast('기간을 확인해 주세요.'); return; }
  if (!o.wds.length || !o.pers.length){ toast('요일과 교시를 하나 이상 골라 주세요.'); return; }
  const res = lsAuto(o);
  LS.rows = res.map(r => ({on:r.ok, date:r.date, pers:r.pers, cls:r.cls}));
  lsRenderRows();
  const miss = res.filter(r => !r.ok).length;
  toast(miss ? `${res.length - miss}개는 정했고, ${miss}개는 기간 안에서 빈 시간을 못 찾았어요. 기간·요일·교시를 넓혀 보세요.` : `${res.length}개 모두 겹치지 않게 정했어요. 확인하고 저장해 주세요.`);
};
$('#lsf-rows').addEventListener('change', e => {
  const tr = e.target.closest('[data-lsr]'); if (!tr) return; const r = LS.rows[+tr.dataset.lsr];
  const f = e.target.dataset.lsf, p = e.target.dataset.lsp;
  if (f === 'on') r.on = e.target.checked; else if (f === 'date') r.date = e.target.value; else if (f === 'cls') r.cls = e.target.value;
  else if (p){ const n = +p; r.pers = e.target.checked ? [...new Set(r.pers.concat(n))].sort((a, b) => a - b) : r.pers.filter(x => x !== n); }
  lsRenderRows();
});
$('#lsf-save').onclick = async () => {
  const prog = $('#lsf-prog').value.trim(); if (!prog){ toast('수업 이름을 적어 주세요.'); $('#lsf-prog').focus(); return; }
  const rows = LS.rows.filter(r => r.on && r.date && r.pers.length && r.cls);
  if (!rows.length){ toast('넣을 시간이 없어요.'); return; }
  const bad = rows.filter((r, i) => lsConflicts(r.date, r.pers, r.cls, null, prog, rows.filter((x, j) => j !== i)).length);
  const b = $('#lsf-save');
  if (bad.length && !twoStep(b, `${bad.length}개가 겹쳐요. 그래도 저장`)) return;
  b.disabled = true;
  try {
    for (const r of rows) await S.db.collection('lessons').add({prog, date:r.date, pers:r.pers, cls:r.cls, teacher:$('#lsf-teacher').value.trim(), place:$('#lsf-place').value.trim(), createdBy:S.uid, createdAt:Date.now()});
    LS.prog = prog; LS.mon = mondayOf(rows[0].date); { const d0 = fromYmd(rows[0].date); LS.month = new Date(d0.getFullYear(), d0.getMonth(), 1); } closeDlgs(); toast(`${prog} ${rows.length}개를 넣었어요.`); renderLessons(); renderCal();
  } catch (er){ wErr(er, true); }
  b.disabled = false;
};
/* 한 칸 고치기 */
function lsOpenEdit(id){
  const l = (S.lessons || []).find(x => x.id === id); if (!l) return;
  LS.editId = id;
  $('#lse-title').textContent = `${l.prog} · ${clsLabel(l.cls)}`;
  $('#lse-date').value = l.date; $('#lse-prog').value = l.prog || ''; $('#lse-teacher').value = l.teacher || ''; $('#lse-place').value = l.place || '';
  $('#lse-cls').innerHTML = lsClasses().map(x => `<option value="${x}" ${x === l.cls ? 'selected' : ''}>${esc(clsLabel(x))}</option>`).join('');
  $$('#lse-pers input').forEach(x => { x.checked = (l.pers || []).includes(+x.value); });
  $$('#dlg-lse input, #dlg-lse select').forEach(x => { x.disabled = !S.canWrite; }); $('#lse-save').hidden = $('#lse-del').hidden = !S.canWrite;
  lseCheck(); closeDlgs(); openDlg('#dlg-lse');
}
function lseCheck(){
  const pers = $$('#lse-pers input:checked').map(x => +x.value);
  const bad = lsConflicts($('#lse-date').value, pers, $('#lse-cls').value, LS.editId);
  $('#lse-warn').innerHTML = bad.length ? `<span class="ls-warn">겹침: ${esc(bad.join(', '))}</span>` : '<span class="ls-ok">겹치는 수업이 없어요.</span>';
}
$('#dlg-lse').addEventListener('change', lseCheck);
$('#lse-save').onclick = async () => {
  const pers = $$('#lse-pers input:checked').map(x => +x.value);
  if (!$('#lse-date').value || !pers.length){ toast('날짜와 교시를 골라 주세요.'); return; }
  try { await S.db.doc('lessons/' + LS.editId).update({date:$('#lse-date').value, pers, cls:$('#lse-cls').value, prog:$('#lse-prog').value.trim(), teacher:$('#lse-teacher').value.trim(), place:$('#lse-place').value.trim(), updatedAt:Date.now()}); closeDlgs(); toast('고쳤어요.'); }
  catch (er){ wErr(er, true); }
};
$('#lse-del').onclick = async () => { const b = $('#lse-del'); if (!twoStep(b, '지울까요?')) return; try { await S.db.doc('lessons/' + LS.editId).delete(); closeDlgs(); toast('지웠어요.'); } catch (er){ wErr(er, true); } };
$('#pg-lessons-body').addEventListener('click', e => { const b = e.target.closest('[data-ls]'); if (b) lsOpenEdit(b.dataset.ls); });
$('#ls-prev').onclick = () => { if (LS.view === 'month') LS.month = new Date(LS.month.getFullYear(), LS.month.getMonth() - 1, 1); else LS.mon = ymd(addDays(fromYmd(lsWeekStart()), -7)); renderLessons(); };
$('#ls-next').onclick = () => { if (LS.view === 'month') LS.month = new Date(LS.month.getFullYear(), LS.month.getMonth() + 1, 1); else LS.mon = ymd(addDays(fromYmd(lsWeekStart()), 7)); renderLessons(); };
$('#ls-today').onclick = () => { const t = today(); LS.mon = mondayOf(ymd(t)); LS.month = new Date(t.getFullYear(), t.getMonth(), 1); renderLessons(); };
$('#ls-view').addEventListener('click', e => { const b = e.target.closest('button[data-v]'); if (!b) return; LS.view = b.dataset.v; renderLessons(); });
$('#ls-prog').addEventListener('change', e => { LS.prog = e.target.value; renderLessons(); });
$('#ls-cls').addEventListener('change', e => { LS.cls = e.target.value; renderLessons(); });
/* 전담 시간표 */
function lsJdRender(){
  const c = LS.jdCls, m = LS.jd[c] || {};
  $('#jd-cls').innerHTML = lsClasses().map(x => `<button type="button" class="stab" data-jdc="${x}" ${x === c ? 'aria-current="page"' : ''}>${esc(clsLabel(x))}</button>`).join('');
  let h = '<table class="ls-jdt"><thead><tr><th></th>' + ['월', '화', '수', '목', '금'].map(w => `<th>${w}</th>`).join('') + '</tr></thead><tbody>';
  for (let p = 1; p <= LS_PER; p++) h += `<tr><th>${p}</th>` + [1, 2, 3, 4, 5].map(wd => `<td><input type="text" data-jd="${wd}-${p}" value="${esc(((m[wd] || [])[p - 1]) || '')}" placeholder="" aria-label="${'월화수목금'[wd - 1]} ${p}교시 전담"></td>`).join('') + '</tr>';
  $('#jd-grid').innerHTML = h + '</tbody></table>';
}
/* 담임 연간 시간표(나의 공간)에서 요일·교시마다 가장 자주 나온 과목을 뽑아요 */
function lsMyWeekly(){
  const cnt = {};
  const add = (wd, p, sub) => { sub = String(sub || '').trim(); if (!sub) return; const k = wd + '-' + p; (cnt[k] = cnt[k] || {}); cnt[k][sub] = (cnt[k][sub] || 0) + 1; };
  ((S.ttplan && S.ttplan.terms) || []).forEach(t => (t.weeks || []).forEach(w => (w.days || []).forEach((d, i) => { if (d && !d.off) (d.s || []).forEach((x, p) => add(i + 1, p + 1, x)); })));
  const base = S.profile.timetable || {};
  [1, 2, 3, 4, 5].forEach(wd => (base[wd] || []).forEach((x, p) => add(wd, p + 1, x)));
  const out = {};
  Object.entries(cnt).forEach(([k, m]) => { const [wd, p] = k.split('-').map(Number); const top = Object.entries(m).sort((a, b) => b[1] - a[1])[0]; (out[wd] = out[wd] || ['', '', '', '', '', ''])[p - 1] = top ? top[0] : ''; });
  return out;
}
const JD_GUESS = /^(영어?|과학?|체육?|음악?|미술?|도덕?|실과?|원어민|코딩|정보)$/;
function lsJdMine(){
  const mine = clsCanon(S.profile.myClass || ''), wk = lsMyWeekly();
  const subs = [...new Set(Object.values(wk).flat().filter(Boolean))];
  $('#jd-mine').hidden = !(S.uid && mine && subs.length);
  if ($('#jd-mine').hidden) return;
  const saved = S.settings.jdSubjects || [];
  $('#jd-subs').innerHTML = subs.map(x => `<label class="ls-pc"><input type="checkbox" value="${esc(x)}" ${(saved.length ? saved.includes(x) : JD_GUESS.test(x)) ? 'checked' : ''}>${esc(x)}</label>`).join('');
}
$('#jd-take').onclick = () => {
  const mine = clsCanon(S.profile.myClass || ''); const pick = $$('#jd-subs input:checked').map(x => x.value);
  if (!pick.length){ toast('전담 과목을 하나 이상 골라 주세요.'); return; }
  const wk = lsMyWeekly(), m = {};
  [1, 2, 3, 4, 5].forEach(wd => { m[wd] = ((wk[wd]) || ['', '', '', '', '', '']).map(x => pick.includes(x) ? x : ''); });
  LS.jd = Object.assign({}, LS.jd, {[mine]:m}); LS.jdCls = mine; lsJdRender();
  if (S.canWrite) S.db.doc('grade/settings').update({jdSubjects:pick}).catch(() => {});
  toast(`${clsLabel(mine)} 전담 시간을 채웠어요. 확인하고 저장해 주세요.`);
};
$('#ls-jd').onclick = () => { LS.jdCls = LS.cls !== 'all' ? LS.cls : (clsCanon(S.profile.myClass || '') || lsClasses()[0]); lsJdRender(); lsJdMine(); $$('#jd-grid input').forEach(x => { x.disabled = !S.canWrite; }); closeDlgs(); openDlg('#dlg-jd'); };
$('#jd-cls').addEventListener('click', e => { const b = e.target.closest('[data-jdc]'); if (!b) return; lsJdCollect(); LS.jdCls = b.dataset.jdc; lsJdRender(); });
function lsJdCollect(){
  const c = LS.jdCls, m = {};
  $$('#jd-grid input').forEach(x => { const [wd, p] = x.dataset.jd.split('-').map(Number); (m[wd] = m[wd] || ['', '', '', '', '', ''])[p - 1] = x.value.trim(); });
  LS.jd = Object.assign({}, LS.jd, {[c]:m});
}
$('#jd-save').onclick = async () => {
  lsJdCollect();
  try { await S.db.doc('grade/jdtt').set({map:LS.jd, updatedBy:S.uid, updatedAt:Date.now()}); closeDlgs(); toast('전담 시간표를 저장했어요. 이제 이 시간과 겹치면 알려 드려요.'); renderLessons(); }
  catch (er){ wErr(er, true); }
};
$('#jd-paste').addEventListener('paste', e => {
  const t = (e.clipboardData || window.clipboardData).getData('text'); if (!t || !/\t/.test(t)) return;
  e.preventDefault();
  const rows = t.replace(/\r/g, '').split('\n').filter(x => x.trim()).map(r => r.split('\t'));
  const body = rows.filter(r => r.length >= 5).slice(-LS_PER);
  const m = {}; body.forEach((r, i) => { const cells = r.length >= 6 ? r.slice(-5) : r.slice(0, 5); cells.forEach((v, j) => { (m[j + 1] = m[j + 1] || ['', '', '', '', '', ''])[i] = v.trim(); }); });
  LS.jd = Object.assign({}, LS.jd, {[LS.jdCls]:m}); lsJdRender(); toast('붙여 넣었어요. 전담이 아닌 과목은 지우고 저장해 주세요.');
});
/* 달력·나의 공간에 보이기 */
function lsOn(k, cls){ return (S.lessons || []).filter(l => l.date === k && (!cls || l.cls === cls)).sort((a, b) => (a.pers[0] || 0) - (b.pers[0] || 0)); }

/* ---------- 새 학년도 · 지난 학년도 보관함 ---------- */
const ARC_KEYS = {
  settings:() => 'grade/settings', events:() => 'events', lessons:() => 'lessons', jdtt:() => 'grade/jdtt', tasks:() => 'tasks', notices:() => 'notices', links:() => 'links', ops:() => 'ops', phrases:() => 'phrases',
  gmemo:() => 'grade/memo', budget:() => 'budget', roster:() => 'roster', tabs:() => 'tabs',
  profile:() => PROFILE(), stunotes:() => STUNOTES(), mphrases:() => PROFILE() + '/phrases', mbudget:() => PROFILE() + '/budget', mops:() => PROFILE() + '/ops', journal:() => PROFILE() + '/journal',
  notes:() => NOTES(), ttplan:() => TTPLAN(), sheet:() => SHEET()
};
const NY_G = [
  ['events', '학년 일정', '새 학년도 첫날보다 앞선 날짜만', true],
  ['tasks', '학년 할 일', '끝낸 것과 기한이 지난 것', true],
  ['notices', '협의·공지', '댓글·투표까지', true],
  ['lessons', '특별 수업 일정', '새 학년도 첫날보다 앞선 것만', true],
  ['budget', '학년 예산', '', true],
  ['roster', '학년 명부', '', true],
  ['tabs', '새로 만든 탭', '탭과 표 내용까지', false],
  ['links', '수업자료 링크', '', false],
  ['ops', '운영자료', '', false],
  ['phrases', '자주 쓰는 문구 (학년)', '', false],
  ['memo', '학년 참고사항', '', false]
];
const NY_M = [
  ['journal', '학급일지 기록', '상담·출결·행발·할 일 기록', true],
  ['days', '날짜별 학급일지 칸', '그날 계획·메모 칸', true],
  ['students', '우리 반 학생', '명부·학생별 행발 모음·명렬표·자리', true],
  ['tt', '시간표·수업 계획', '', true],
  ['mbudget', '학급 예산', '', true],
  ['notes', '메모', '', false],
  ['mphrases', '자주 쓰는 문구 (나만)', '', false]
];
const ARCS = () => `data/users/${S.uid}/arcs`;
const ARC_PART = 80000;
const nyYear = () => { const d = today(); return d.getMonth() < 3 ? d.getFullYear() - 1 : d.getFullYear(); };
function arcRel(p){ const pre = `data/users/${S.uid}/`; return S.uid && p.startsWith(pre) ? '~/' + p.slice(pre.length) : p; }
function arcSnapOf(p){
  const docsObj = (S.arc && S.arc.docs) || {};
  const rel = arcRel(p);
  const one = (r, abs) => { const d = docsObj[r]; return {id:abs.split('/').pop(), exists:!!d, data:() => d ? JSON.parse(JSON.stringify(d)) : undefined, metadata:{fromCache:false, hasPendingWrites:false}}; };
  if (p.split('/').length % 2 === 0) return one(rel, p);
  const pre = rel + '/';
  const ds = Object.keys(docsObj).filter(k => k.startsWith(pre) && !k.slice(pre.length).includes('/')).sort().map(k => one(k, p + '/' + k.slice(pre.length)));
  return {docs:ds, size:ds.length, empty:!ds.length, docChanges:() => [], metadata:{fromCache:false, hasPendingWrites:false}};
}
function arcDb(){
  const deny = async () => { throw {code:'read_only', message:'지난 학년도 기록은 볼 수만 있어요.'}; };
  const sub = p => n => { setTimeout(() => { if (S.arc) n(arcSnapOf(p)); }, 0); return () => {}; };
  const doc = p => ({id:p.split('/').pop(), path:p, get:async () => arcSnapOf(p), set:deny, update:deny, delete:deny, acquire:async () => ({acquired:false}), onSnapshot:sub(p), collection:x => col(p + '/' + x)});
  const col = p => { const q = {path:p, doc:id => doc(p + '/' + (id || rid())), add:deny, where:() => q, orderBy:() => q, limit:() => q, get:async () => arcSnapOf(p), onSnapshot:sub(p)}; return q; };
  return {doc, collection:col};
}
function enterArc(label, docsObj, has, cut){
  if (!S.arc){ S.liveDb = S.db; S.arcPrevCW = S.canWrite; }
  S.arc = {label, docs:docsObj, has, cut:cut || ''};
  S.db = arcDb(); S.canWrite = false;
  document.body.classList.add('ro', 'arc');
  $('#arcbar').hidden = false;
  $('#arc-what').textContent = `${label} 보관함을 보는 중` + (has.g && !has.m ? ' (학년 공간만 보관됨)' : !has.g && has.m ? ' (나의 공간만 보관됨)' : '');
  // 그해 마지막 기록이 있는 달로 달력을 옮겨요
  let last = '';
  Object.keys(docsObj).forEach(k => { const d = docsObj[k]; const v = /^events\//.test(k) ? d.date : /^~\/profile\/journal\//.test(k) ? d.date : ''; if (v && v > last && v < (S.arc.cut || '9999')) last = v; });
  if (last){ const d = fromYmd(last); S.month = new Date(d.getFullYear(), d.getMonth(), 1); S.selDate = last; S.jDate = last; }
  Object.keys(S.reg || {}).forEach(k => { if (ARC_KEYS[k]) try { S.reg[k](arcSnapOf(ARC_KEYS[k]())); } catch (e){ console.error(e); } });
  listenRows(); listenDaily(); if (S.uid) listenDay();
  closeDlgs(); renderStrip(); renderAll(); window.scrollTo(0, 0);
}
function exitArc(){
  if (!S.arc) return;
  S.arc = null; S.db = S.liveDb; S.canWrite = S.arcPrevCW;
  document.body.classList.remove('arc'); if (S.canWrite) document.body.classList.remove('ro');
  $('#arcbar').hidden = true;
  const d = today(); S.month = new Date(d.getFullYear(), d.getMonth(), 1); S.selDate = ymd(d); S.jDate = ymd(d);
  Object.keys(S.reg || {}).forEach(k => { if (ARC_KEYS[k] && S.liveSnap[k]) try { S.reg[k](S.liveSnap[k]); } catch (e){ console.error(e); } });
  listenRows(); listenDaily(); if (S.uid) listenDay();
  renderStrip(); renderAll(); window.scrollTo(0, 0);
  toast('지금 학년도로 돌아왔어요.');
}
$('#arc-exit').onclick = exitArc;
document.addEventListener('beforeinput', e => {
  if (!S.arc || !e.target.closest || !e.target.closest('main')) return;
  e.preventDefault(); toast('지난 학년도 기록은 볼 수만 있어요.');
}, true);

/* 보관함 목록 */
async function arcList(){
  const db = S.liveDb && S.arc ? S.liveDb : S.db; if (!db) return [];
  const by = {};
  try { const snap = await db.collection('archive').get(); snap.docs.forEach(d => { const m = d.data(); if (m && m.label) (by[m.label] = by[m.label] || {label:m.label}).g = Object.assign({key:d.id}, m); }); } catch (e){}
  if (S.uid) try { const s = await db.doc(ARCS()).get(); ((s.exists && s.data().list) || []).forEach(m => { if (m && m.label) (by[m.label] = by[m.label] || {label:m.label}).m = m; }); } catch (e){}
  return Object.values(by).sort((a, b) => ((b.g || b.m).at || 0) - ((a.g || a.m).at || 0));
}
async function renderArcList(){
  const box = $('#arc-list'); if (!box) return;
  box.innerHTML = '<p class="hint" style="margin:0">보관함을 찾는 중…</p>';
  const list = await arcList(); ARC.list = list;
  box.innerHTML = list.length ? list.map((a, i) => {
    const m = a.g || a.m; const when = m.at ? fmtMD(ymd(new Date(m.at))) : '';
    const what = [a.g ? '학년 공간' : '', a.m ? '나의 공간' : ''].filter(Boolean).join(' · ');
    const cur = S.arc && S.arc.label === a.label;
    return `<div class="arc-it"><b>${esc(a.label)}</b><span class="hint">${what}${when ? ' · ' + when + ' 보관' : ''}</span>${cur ? '<span class="chip">보는 중</span>' : `<button type="button" class="btn small" data-arc-open="${i}">열어 보기</button>`}</div>`;
  }).join('') : '<p class="hint" style="margin:0">아직 보관한 학년도가 없어요.</p>';
}
const ARC = {list:[]};
$('#arc-list').addEventListener('click', async e => {
  const b = e.target.closest('[data-arc-open]'); if (!b) return;
  const a = ARC.list[+b.dataset.arcOpen]; if (!a) return;
  b.disabled = true; b.textContent = '여는 중…';
  try {
    const db = S.arc ? S.liveDb : S.db;
    const docsObj = {}; let cut = '';
    const load = async (base, n) => { let j = ''; for (let i = 0; i < n; i++){ const sn = await db.doc(`${base}/${i}`).get(); if (!sn.exists) throw {code:'missing'}; j += sn.data().d || ''; } return JSON.parse(j); };
    if (a.g){ const o = await load(`archive/${a.g.key}/p`, a.g.parts); Object.assign(docsObj, o.docs || {}); cut = a.g.cut || cut; }
    if (a.m){ const o = await load(`${ARCS()}/${a.m.key}`, a.m.parts); Object.assign(docsObj, o.docs || {}); cut = cut || a.m.cut || ''; }
    enterArc(a.label, docsObj, {g:!!a.g, m:!!a.m}, cut);
    toast(`${a.label} 기록을 열었어요. 위 막대에서 지금으로 돌아갈 수 있어요.`);
  } catch (er){ b.disabled = false; b.textContent = '열어 보기'; toast('보관함을 열지 못했어요. 잠시 뒤 다시 눌러 주세요.'); }
});
$('#open-settings').addEventListener('click', () => { renderArcList(); });

/* 새 학년도 시작하기 */
$('#ny-open').onclick = () => {
  if (S.arc){ toast('지금 학년도로 돌아온 뒤에 시작할 수 있어요.'); return; }
  if (!S.db || !S.uid){ toast('로그인한 상태에서만 할 수 있어요.'); return; }
  const y = nyYear();
  $('#ny-label').value = `${y}학년도`; $('#ny-cut').value = `${y + 1}-03-01`;
  const gOk = !!(S.isOwner && S.canWrite);
  const box = (list, on) => list.map(([k, n, h, def]) => `<label for="ny-${k}"><input type="checkbox" id="ny-${k}" data-ny="${k}" ${def && on ? 'checked' : ''} ${on ? '' : 'disabled'}><span>${n}${h ? `<small>${h}</small>` : ''}</span></label>`).join('');
  $('#ny-g-checks').innerHTML = box(NY_G, gOk); $('#ny-g-note').hidden = gOk;
  $('#ny-m-checks').innerHTML = box(NY_M, true);
  $('#ny-prog').textContent = '체크한 것만 비워요. 체크하지 않은 것은 새 학년도에도 그대로 남아요.';
  $('#ny-go').disabled = false; $('#ny-go').textContent = '보관하고 비우기';
  closeDlgs(); openDlg('#dlg-newyear');
};
async function colAll(path){
  const db = S.db;
  if (db.listPaths){ const ps = await db.listPaths(path); const out = []; for (const p of ps){ const sn = await db.doc(p).get(); if (sn.exists) out.push([p, sn.data()]); } return out; }
  const snap = await db.collection(path).get(); return snap.docs.map(d => [path + '/' + d.id, d.data()]);
}
async function delMany(paths, prog){
  let done = 0; const total = paths.length; if (!total) return;
  const db = S.db;
  if (db.bulkDelete){
    try { for (let i = 0; i < paths.length; i += 120){ await db.bulkDelete(paths.slice(i, i + 120)); done = Math.min(total, i + 120); prog(done, total); } return; }
    catch (e){ if (!/bulkDelete|찾을 수 없|not found/i.test(String((e && e.message) || e))) throw e; }
  }
  let k = 0;
  const worker = async () => { while (k < paths.length){ const p = paths[k++]; try { await db.doc(p).delete(); } catch (e){ if (!e || e.code !== 'not_found') throw e; } done++; prog(done, total); } };
  await Promise.all([worker(), worker(), worker(), worker()]);
}
async function arcSave(base, docsObj, prog){
  const json = JSON.stringify({v:1, docs:docsObj});
  const n = Math.max(1, Math.ceil(json.length / ARC_PART));
  for (let i = 0; i < n; i++){ await S.db.doc(`${base}/${i}`).set({d:json.slice(i * ARC_PART, (i + 1) * ARC_PART)}); prog(i + 1, n); }
  return {parts:n, size:json.length};
}
$('#ny-form').addEventListener('submit', async ev => {
  ev.preventDefault();
  const go = $('#ny-go'); if (go.disabled) return;
  const label = $('#ny-label').value.trim().replace(/\s+/g, ' ') || `${nyYear()}학년도`;
  const cut = $('#ny-cut').value || `${nyYear() + 1}-03-01`;
  const cutTs = fromYmd(cut).getTime();
  const pick = new Set($$('#ny-form [data-ny]').filter(x => x.checked && !x.disabled).map(x => x.dataset.ny));
  const gOk = !!(S.isOwner && S.canWrite);
  if (!twoStep(go, '정말 할까요? 한 번 더 눌러요')) return;
  go.disabled = true; $$('#ny-form input').forEach(x => { x.disabled = true; });
  const P = $('#ny-prog'); const say = t => { P.textContent = t; };
  const key = 'y' + (label.match(/\d{4}/) || [''])[0] + '-' + rid();
  try {
    /* 1. 학년 공간 모으기 */
    let gDocs = null;
    if (gOk){
      say('학년 공간 기록을 모으는 중…'); gDocs = {};
      for (const c of ['events', 'tasks', 'notices', 'links', 'ops', 'phrases', 'budget', 'roster', 'tabs', 'daily', 'lessons']) (await colAll(c)).forEach(([p, d]) => { gDocs[p] = d; });
      for (const p of Object.keys(gDocs).filter(p => /^tabs\/[^/]+$/.test(p))) (await colAll(p + '/rows')).forEach(([q, d]) => { gDocs[q] = d; });
      for (const p of ['grade/settings', 'grade/memo', 'grade/jdtt']){ const sn = await S.db.doc(p).get(); if (sn.exists) gDocs[p] = sn.data(); }
    }
    /* 2. 나의 공간 모으기 */
    say('나의 공간 기록을 모으는 중…');
    const mDocs = {}; const pre = `data/users/${S.uid}`;
    let top = [];
    try { top = await colAll(pre); } catch (e){ top = []; }
    if (!top.length){ for (const p of [PROFILE(), NOTES(), SHEET(), STUNOTES(), TTPLAN(), ROUTINE(), SEATDOC()]){ try { const sn = await S.db.doc(p).get(); if (sn.exists) top.push([p, sn.data()]); } catch (e){} } }
    top.forEach(([p, d]) => { if (!/\/(arcs|gcal)$/.test(p) && !/\/of_[^/]+$/.test(p)) mDocs[arcRel(p)] = d; });
    if (!top.some(([p]) => /\/d-\d{4}-\d{2}-\d{2}$/.test(p))){
      // 날짜 칸 목록을 못 받으면 지난 한 해를 하루씩 찾아봐요
      const ds = []; for (let d = addDays(fromYmd(cut), -400); d < fromYmd(cut); d = addDays(d, 1)) ds.push(ymd(d));
      let i = 0; const w = async () => { while (i < ds.length){ const k = ds[i++]; try { const sn = await S.db.doc(DAYPATH(k)).get(); if (sn.exists) mDocs[arcRel(DAYPATH(k))] = sn.data(); } catch (e){} } };
      await Promise.all([w(), w(), w(), w(), w(), w()]);
    }
    for (const c of ['journal', 'phrases', 'budget', 'ops']) (await colAll(PROFILE() + '/' + c)).forEach(([p, d]) => { mDocs[arcRel(p)] = d; });
    /* 3. 보관함에 넣기 */
    const at = Date.now();
    if (gDocs){
      const r = await arcSave(`archive/${key}/p`, gDocs, (i, n) => say(`학년 공간 보관함에 넣는 중… ${i}/${n}`));
      await S.db.doc(`archive/${key}`).set({label, at, by:S.uid, cut, parts:r.parts, size:r.size, count:Object.keys(gDocs).length});
    }
    const rm = await arcSave(`${ARCS()}/${key}`, mDocs, (i, n) => say(`나의 공간 보관함에 넣는 중… ${i}/${n}`));
    const old = await S.db.doc(ARCS()).get();
    const list = ((old.exists && old.data().list) || []).concat([{key, label, at, cut, parts:rm.parts, size:rm.size, count:Object.keys(mDocs).length}]);
    await S.db.doc(ARCS()).set({list});
    if (GAS && window.__gasCall){ say('구글 드라이브에 시트 백업본도 만드는 중…'); try { await window.__gasCall('backupCopy', label, !!gDocs); } catch (e){} }
    /* 4. 고른 것 비우기 */
    const del = [];
    if (gDocs){
      Object.keys(gDocs).forEach(p => {
        const d = gDocs[p] || {}; const c = p.split('/')[0];
        if (c === 'events' && pick.has('events') && (d.date ? d.date < cut : (d.createdAt || 0) < cutTs)) del.push(p);
        else if (c === 'daily' && pick.has('events') && p.split('/')[1] < cut) del.push(p);
        else if (c === 'tasks' && pick.has('tasks') && !(d.due && d.due >= cut && !d.done)) del.push(p);
        else if (c === 'notices' && pick.has('notices') && (d.createdAt || 0) < cutTs) del.push(p);
        else if (c === 'lessons' && pick.has('lessons') && (d.date || '') < cut) del.push(p);
        else if ((c === 'budget' || c === 'roster' || c === 'links' || c === 'ops' || c === 'phrases' || c === 'tabs') && pick.has(c)) del.push(p);
        else if (p === 'grade/memo' && pick.has('memo')) del.push(p);
      });
    }
    Object.keys(mDocs).forEach(r => {
      const d = mDocs[r] || {}; const p = `${pre}/${r.slice(2)}`;
      if (/^~\/profile\/journal\//.test(r) && pick.has('journal') && (d.date ? d.date < cut : (d.createdAt || 0) < cutTs)) del.push(p);
      else if (/^~\/d-(\d{4}-\d{2}-\d{2})$/.test(r) && pick.has('days') && r.slice(4) < cut) del.push(p);
      else if (/^~\/(stunotes|sheet|seat)$/.test(r) && pick.has('students')) del.push(p);
      else if (r === '~/ttplan' && pick.has('tt')) del.push(p);
      else if (/^~\/profile\/budget\//.test(r) && pick.has('mbudget')) del.push(p);
      else if (r === '~/notes' && pick.has('notes')) del.push(p);
      else if (/^~\/profile\/phrases\//.test(r) && pick.has('mphrases')) del.push(p);
    });
    await delMany(del, (i, n) => say(`고른 기록을 비우는 중… ${i}/${n}`));
    if (pick.has('students') || pick.has('tt')){
      if (pick.has('students')){ S.profile.roster = []; S.profile.rosterExtra = []; }
      if (pick.has('tt')) S.profile.timetable = {};
      saveProfile();
    }
    say(`끝났어요. "${label}" 보관함에 ${gDocs ? `학년 공간 ${Object.keys(gDocs).length}개, ` : ''}나의 공간 ${Object.keys(mDocs).length}개 기록을 넣고, ${del.length}개를 비웠어요. 설정의 "새 학년도 · 지난 학년도"에서 열어 볼 수 있어요.`);
    go.textContent = '끝났어요'; toast(`${label} 보관을 마쳤어요.`);
  } catch (e){
    console.error(e);
    say('중간에 멈췄어요. 보관함을 다 넣기 전이면 아무것도 지우지 않았어요. 잠시 뒤 다시 해 주세요. (' + String((e && (e.message || e.code)) || e).slice(0, 80) + ')');
    go.disabled = false; go.textContent = '다시 하기'; $$('#ny-form input').forEach(x => { x.disabled = x.dataset.ny && NY_G.some(g => g[0] === x.dataset.ny) && !gOk; });
  }
});

boot();
})();
