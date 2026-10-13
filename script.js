'use strict';
/* =====================================================================
   LUDO 2-6 JOGADORES  |  HTML + CSS + JS puro
   - Modo Local: jogadores no mesmo aparelho (com CPU opcional)
   - Modo Online: salas por código, comunicação P2P via PeerJS (WebRTC).
     Quem cria a sala é o "host" e controla as regras da partida.
   ===================================================================== */

/* ============================ CONSTANTES ============================ */
const COLORS = [
  { n: 'Azul',     main: '#2aa5ff', dark: '#0b5fb0', txt: '#04162b' },
  { n: 'Vermelho', main: '#ff4757', dark: '#a8182a', txt: '#fff' },
  { n: 'Verde',    main: '#3dff7a', dark: '#12a043', txt: '#03210f' },
  { n: 'Amarelo',  main: '#ffd93d', dark: '#b38a00', txt: '#2b1d00' },
  { n: 'Laranja',  main: '#ff9a2e', dark: '#b45a00', txt: '#2b1500' },
  { n: 'Roxo',     main: '#c46bff', dark: '#6a1fa8', txt: '#1c0430' }
];

// Quais cores (0..5) cada jogador usa conforme o número de jogadores (Jogador 1 = 1ª cor da lista, etc.)
const LAYOUT = { 2: [0, 3], 3: [0, 2, 4], 4: [0, 1, 3, 4], 5: [0, 1, 2, 3, 4], 6: [0, 1, 2, 3, 4, 5] };

const LOOP_LEN = 72;     // casas do circuito (6 braços x 12)
const LOOP_END = 68;     // última posição do circuito para uma peça
const GOAL = 74;         // posição final (centro)

/* ============================ GEOMETRIA ============================= */
const SQ3 = Math.sqrt(3);
const CC = SQ3;                  // distância do centro até a casa de canto
const UMAX = CC + 5;             // ponta do braço
const EDGE = UMAX + 0.5;
const BAR = 0.6;

const FR = [];                   // referencial de cada braço (0 = topo, sentido horário)
for (let k = 0; k < 6; k++) {
  const deg = -90 + 60 * k, r = deg * Math.PI / 180;
  FR.push({ deg, a: [Math.cos(r), Math.sin(r)], l: [-Math.sin(r), Math.cos(r)] });
}
const pt = (k, u, v) => {
  const f = FR[((k % 6) + 6) % 6];
  return [u * f.a[0] + v * f.l[0], u * f.a[1] + v * f.l[1]];
};
// casa i (0..11) de um braço: 0-5 faixa de ida, 6 ponta, 7-11 faixa de volta
const cellUV = i => (i <= 5 ? [CC + i, -1] : i === 6 ? [UMAX, 0] : [UMAX - (i - 7), 1]);

const LOOP = [];
for (let k = 0; k < 6; k++) for (let i = 0; i < 12; i++) {
  const [u, v] = cellUV(i); const [x, y] = pt(k, u, v);
  LOOP.push({ x, y });
}
const HOME = [];                 // corredor final de cada braço (5 casas)
for (let k = 0; k < 6; k++) HOME.push([0, 1, 2, 3, 4].map(h => { const [x, y] = pt(k, UMAX - 1 - h, 0); return { x, y }; }));

const armOf = ci => (3 + ci) % 6;               // Jogador 1 (azul) fica embaixo
const armCI = k => (k - 3 + 6) % 6;
const startG = ci => armOf(ci) * 12 + 10;       // casa de saída do jogador

const BASE_SLOT = [];            // posições das 4 peças na base (triângulo entre braços)
for (let ci = 0; ci < 6; ci++) {
  const psi = (-90 + 60 * armOf(ci) + 30) * Math.PI / 180;
  const c = Math.cos(psi), s = Math.sin(psi);
  BASE_SLOT.push([[5.45, -.72], [5.45, .72], [6.35, -.72], [6.35, .72]].map(([r, t]) => ({ x: r * c - t * s, y: r * s + t * c })));
}

const SAFE = new Set();          // casas seguras: saídas e estrelas
for (let k = 0; k < 6; k++) { SAFE.add(k * 12 + 10); SAFE.add(k * 12 + 3); }

const gcell = (ci, pos) => (pos >= 0 && pos <= LOOP_END ? (startG(ci) + pos) % LOOP_LEN : -1);
const rnd = n => 1 + Math.floor(Math.random() * n);

function optionsOf(s) {          // peças que podem se mover com o dado atual
  const p = s.players[s.turn], d = s.dice, out = [];
  p.tokens.forEach((pos, i) => {
    if (pos === -1) { if (d === 6) out.push(i); }
    else if (pos < GOAL && pos + d <= GOAL) out.push(i);
  });
  return out;
}

/* ============================== MOTOR =============================== */
class Game {
  constructor(seats, cb) {
    const lay = LAYOUT[seats.length];
    this.s = {
      players: seats.map((x, i) => ({ name: x.name, ci: lay[i], ai: !!x.ai, gone: false, tokens: [-1, -1, -1, -1] })),
      turn: 0, phase: 'roll', dice: 0, sixes: 0, winner: -1
    };
    this.cb = cb; this.seq = 0; this.dead = false; this.timers = [];
  }
  snapshot() { return JSON.parse(JSON.stringify(this.s)); }
  emit(ev, bump = true) { if (bump) this.seq++; this.cb(this.snapshot(), ev); }
  later(fn, ms) {
    const sq = this.seq;
    const id = setTimeout(() => { if (!this.dead && sq === this.seq) fn(); }, ms);
    this.timers.push(id);
  }
  dispose() { this.dead = true; this.timers.forEach(clearTimeout); }
  cur() { return this.s.players[this.s.turn]; }

  plan() {                       // agenda jogada automática quando for CPU / jogador que saiu
    if (this.dead || this.s.winner >= 0) return;
    if (this.s.phase === 'roll' && this.cur().ai) this.later(() => this.roll(), 900);
    else if (this.s.phase === 'move') this.autoPlan(optionsOf(this.s));
  }
  autoPlan(opts) {
    const p = this.cur();
    const distinct = new Set(opts.map(i => p.tokens[i]));
    if (p.ai) this.later(() => this.move(this.pick(opts)), 1100);
    else if (distinct.size === 1) this.later(() => this.move(opts[0]), 1000);   // só uma jogada possível
  }

  roll() {
    const s = this.s;
    if (s.phase !== 'roll' || s.winner >= 0) return;
    s.dice = rnd(6);
    s.sixes = s.dice === 6 ? s.sixes + 1 : 0;
    const ev = { type: 'roll', p: s.turn, dice: s.dice };
    if (s.sixes >= 3) {          // três 6 seguidos: perde a vez
      ev.penalty = true; s.sixes = 0; s.phase = 'anim';
      this.emit(ev); this.later(() => this.next(false), 1500); return;
    }
    const opts = optionsOf(s);
    if (!opts.length) {
      ev.none = true; s.phase = 'anim';
      this.emit(ev); this.later(() => this.next(s.dice === 6), 1500); return;
    }
    s.phase = 'move'; ev.opts = opts;
    this.emit(ev); this.autoPlan(opts);
  }

  move(i) {
    const s = this.s;
    if (s.phase !== 'move' || !optionsOf(s).includes(i)) return;
    const p = this.cur(), from = p.tokens[i], to = from === -1 ? 0 : from + s.dice;
    p.tokens[i] = to;
    const caps = [], g = gcell(p.ci, to);
    if (g >= 0 && !SAFE.has(g)) {
      s.players.forEach((q, qi) => {
        if (qi === s.turn) return;
        q.tokens.forEach((pos, ti) => { if (gcell(q.ci, pos) === g) { caps.push({ p: qi, t: ti }); q.tokens[ti] = -1; } });
      });
    }
    const extra = s.dice === 6 || caps.length > 0 || to === GOAL;
    const steps = from === -1 ? 1 : s.dice;
    const ev = { type: 'move', p: s.turn, t: i, from, to, caps, extra };
    s.phase = 'anim';
    if (p.tokens.every(x => x === GOAL)) {
      s.winner = s.turn; s.phase = 'over'; ev.won = true;
      this.emit(ev); return;
    }
    this.emit(ev);
    this.later(() => this.next(extra), steps * 170 + (caps.length ? 800 : 400));
  }

  next(extra) {
    const s = this.s;
    if (s.winner >= 0) return;
    if (!extra) { s.sixes = 0; s.turn = (s.turn + 1) % s.players.length; }
    s.phase = 'roll';
    this.emit({ type: 'turn', p: s.turn });
    this.plan();
  }

  markGone(idx) {                // jogador desconectado: a CPU assume
    const p = this.s.players[idx];
    if (!p || p.gone) return;
    p.gone = true; p.ai = true;
    this.emit({ type: 'info', msg: p.name + ' saiu. A CPU assumiu as peças.' }, false);
    if (this.s.turn === idx) this.plan();
  }

  markBack(idx) {                // jogador voltou (reconexão): devolve o controle a ele
    const p = this.s.players[idx];
    if (!p || !p.gone) return false;
    p.gone = false; p.ai = false;
    this.emit({ type: 'info', msg: p.name + ' voltou para a partida.' }, false);
    if (this.s.phase === 'roll' || this.s.phase === 'move') { this.seq++; this.plan(); }
    return true;
  }

  danger(g) {                    // quantas peças inimigas podem alcançar a casa g (1 a 6 casas atrás)
    if (g < 0 || SAFE.has(g)) return 0;
    let n = 0;
    this.s.players.forEach((q, qi) => {
      if (qi === this.s.turn) return;
      q.tokens.forEach(pos => {
        const h = gcell(q.ci, pos);
        if (h >= 0) { const d = (g - h + LOOP_LEN) % LOOP_LEN; if (d >= 1 && d <= 6) n++; }
      });
    });
    return n;
  }
  pick(opts) {                   // inteligência simples da CPU
    const s = this.s, p = this.cur(), d = s.dice;
    let best = opts[0], bs = -1e9;
    for (const i of opts) {
      const from = p.tokens[i], to = from === -1 ? 0 : from + d;
      const gt = gcell(p.ci, to), gf = gcell(p.ci, from);
      let sc = Math.random();
      if (to === GOAL) sc += 100;
      if (gt >= 0 && !SAFE.has(gt) && s.players.some((q, qi) => qi !== s.turn && q.tokens.some(x => gcell(q.ci, x) === gt))) sc += 80;
      if (from === -1) sc += 40;
      if (to > LOOP_END) sc += 30;
      if (gt >= 0 && SAFE.has(gt)) sc += 15;
      sc -= 20 * this.danger(gt);
      if (gf >= 0 && this.danger(gf) > 0 && this.danger(gt) === 0) sc += 25;
      sc += to * 0.2;
      if (sc > bs) { bs = sc; best = i; }
    }
    return best;
  }
}

/* ============================== UTILS =============================== */
const $ = s => document.querySelector(s);
function setVH() { document.documentElement.style.setProperty('--vh', window.innerHeight + 'px'); }
addEventListener('resize', setVH); addEventListener('orientationchange', setVH); setVH();
let wakeLock = null;
async function keepAwake() {   // evita a tela do celular apagar durante a partida
  try {
    if ('wakeLock' in navigator && !wakeLock) {
      wakeLock = await navigator.wakeLock.request('screen');
      wakeLock.addEventListener('release', () => { wakeLock = null; });
    }
  } catch (e) { /* sem suporte */ }
}
const wait = ms => new Promise(r => setTimeout(r, ms));
let curScreen = 'menu';
function show(id) {
  curScreen = id;
  document.querySelectorAll('.screen').forEach(s => s.classList.toggle('active', s.id === 'screen-' + id));
}
let toastT;
function toast(msg) {
  const t = $('#toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('show'), 2800);
}
function el(tag, cls, text) { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; }
const SVGNS = 'http://www.w3.org/2000/svg';
function S(tag, attrs, parent) {
  const e = document.createElementNS(SVGNS, tag);
  for (const k in attrs) e.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(e);
  return e;
}
// posições (em %) das bolinhas em cada face: [x, y]
const L = 27, M = 50, R = 73;
const PIPS = {
  0: [],
  1: [[M, M]],
  2: [[L, L], [R, R]],
  3: [[L, L], [M, M], [R, R]],
  4: [[L, L], [R, L], [L, R], [R, R]],
  5: [[L, L], [R, L], [M, M], [L, R], [R, R]],
  6: [[L, L], [R, L], [L, M], [R, M], [L, R], [R, R]]
};
function drawDice(node, n) {
  node.innerHTML = '';
  node.setAttribute('aria-label', n ? 'Dado: ' + n : 'Dado');
  for (const [x, y] of PIPS[n]) {
    const pip = el('i');
    pip.style.setProperty('--x', x);
    pip.style.setProperty('--y', y);
    node.appendChild(pip);
  }
}
async function copyText(txt) {
  try { await navigator.clipboard.writeText(txt); toast('Copiado!'); }
  catch (e) {
    const t = document.createElement('textarea'); t.value = txt; document.body.appendChild(t); t.select();
    try { document.execCommand('copy'); toast('Copiado!'); } catch (_) { toast('Não foi possível copiar.'); }
    t.remove();
  }
}

/* ======================= ESTADO DA INTERFACE ======================== */
let mode = null;                 // 'local' | 'online'
let game = null;                 // motor (local ou host)
let cur = null;                  // último estado exibido
let players = [];
let mySeat = -1;
let viewRot = 0;
let view = [];                   // posições exibidas (podem estar no meio de uma animação)
let tokEls = [], bars = [];
let queue = [], busy = false;
let localSeatsCfg = null;        // para "jogar novamente" no modo local
const svg = $('#board');
let tokLayer = null;

const nm = i => cur.players[i].name;
const isMine = () => {
  if (!cur || cur.winner >= 0) return false;
  return mode === 'local' ? !cur.players[cur.turn].ai : cur.turn === mySeat;
};

/* ========================= DESENHO DO TABULEIRO ===================== */
function buildBoard() {
  svg.innerHTML = '';
  const defs = S('defs', {}, svg);
  const flt = S('filter', { id: 'glow', x: '-40%', y: '-40%', width: '180%', height: '180%' }, defs);
  S('feGaussianBlur', { stdDeviation: .12, result: 'b' }, flt);
  const mg = S('feMerge', {}, flt);
  S('feMergeNode', { in: 'b' }, mg); S('feMergeNode', { in: 'SourceGraphic' }, mg);
  const world = S('g', { transform: `rotate(${viewRot})` }, svg);
  const active = new Map(players.map((p, i) => [p.ci, i]));

  // contorno
  const outline = [];
  for (let k = 0; k < 6; k++) outline.push(pt(k, EDGE, -1.5), pt(k, EDGE, 1.5));
  S('polygon', { points: outline.map(p => p.join(',')).join(' '), class: 'b-bg' }, world);

  // bases (triângulos entre os braços)
  for (let k = 0; k < 6; k++) {
    const ci = armCI(k), col = COLORS[ci];
    const psi = (-90 + 60 * k + 30) * Math.PI / 180;
    const A = [3 * Math.cos(psi), 3 * Math.sin(psi)], B = pt(k, EDGE, 1.5), C = pt(k + 1, EDGE, -1.5);
    const grp = S('g', { class: 'wedge' + (active.has(ci) ? '' : ' off') }, world);
    S('polygon', { points: [A, B, C].map(p => p.join(',')).join(' '), fill: col.main, 'fill-opacity': .24, stroke: col.main, 'stroke-width': .07, 'stroke-linejoin': 'round' }, grp);
    const G = [(A[0] + B[0] + C[0]) / 3, (A[1] + B[1] + C[1]) / 3];
    const sh = P => [G[0] + (P[0] - G[0]) * .9, G[1] + (P[1] - G[1]) * .9];
    S('polygon', { points: [A, B, C].map(sh).map(p => p.join(',')).join(' '), class: 'recess', 'stroke-linejoin': 'round' }, grp);
    BASE_SLOT[ci].forEach(s => S('circle', { cx: s.x, cy: s.y, r: .43, fill: col.main, 'fill-opacity': .14, stroke: col.main, 'stroke-opacity': .7, 'stroke-width': .05 }, grp));
  }

  // braços
  bars = [];
  for (let k = 0; k < 6; k++) {
    const ci = armCI(k), col = COLORS[ci];
    const g = S('g', { transform: `rotate(${FR[k].deg})` }, world);
    const idx = active.get(ci);
    const bar = S('rect', { x: EDGE, y: -1.5, width: BAR, height: 3, rx: .16, fill: col.main, class: 'bar', filter: 'url(#glow)' }, g);
    bars[k] = bar;
    const ang = (((FR[k].deg + 90 + viewRot) % 360) + 360) % 360;
    const flip = ang > 90 && ang < 270 ? 180 : 0;
    const label = S('text', { class: 'lbl', fill: col.txt, transform: `translate(${EDGE + BAR / 2},0) rotate(${90 + flip})`, opacity: idx == null ? .55 : 1 }, g);
    label.textContent = (idx == null ? 'VAGO' : players[idx].name).toUpperCase();

    for (let i = 0; i < 12; i++) {
      const [u, v] = cellUV(i), gi = k * 12 + i;
      const isStart = i === 10, isStar = i === 3;
      S('rect', { x: u - .41, y: v - .41, width: .82, height: .82, rx: .16, class: 'cell', fill: isStart ? col.main : '#0e1630', 'fill-opacity': isStart ? .85 : 1, stroke: isStart ? '#fff' : '#2a3a73' }, g);
      if (isStar) { const st = S('text', { x: u, y: v, class: 'star', fill: col.main }, g); st.textContent = '★'; }
      if (isStart) { const st = S('text', { x: u, y: v, class: 'star', fill: 'rgba(255,255,255,.9)', 'font-size': '.5px' }, g); st.textContent = '➤'; }
      void gi;
    }
    for (let h = 0; h < 5; h++) {
      S('rect', { x: UMAX - 1 - h - .41, y: -.41, width: .82, height: .82, rx: .16, class: 'cell home', fill: col.main, 'fill-opacity': .4, stroke: col.main }, g);
    }
  }

  // centro (chegada)
  const R = 1.4;
  for (let k = 0; k < 6; k++) {
    const a1 = (FR[k].deg - 30) * Math.PI / 180, a2 = (FR[k].deg + 30) * Math.PI / 180;
    S('polygon', { points: `0,0 ${R * Math.cos(a1)},${R * Math.sin(a1)} ${R * Math.cos(a2)},${R * Math.sin(a2)}`, fill: COLORS[armCI(k)].main, stroke: '#070c1e', 'stroke-width': .05, 'stroke-linejoin': 'round', 'fill-opacity': .95 }, world);
  }

  // peças
  tokLayer = S('g', {}, world);
  tokEls = players.map((p, pi) => [0, 1, 2, 3].map(ti => {
    const col = COLORS[p.ci];
    const g = S('g', { class: 'tk', filter: 'url(#glow)' }, tokLayer);
    g.dataset.p = pi; g.dataset.t = ti;
    S('circle', { r: .62, class: 'hit' }, g);
    const inn = S('g', { class: 'tk-in' }, g);
    S('circle', { r: .4, cy: .07, fill: 'rgba(0,0,0,.35)' }, inn);
    S('circle', { r: .36, fill: col.main, stroke: col.dark, 'stroke-width': .07 }, inn);
    S('circle', { r: .2, fill: 'none', stroke: 'rgba(255,255,255,.55)', 'stroke-width': .05 }, inn);
    S('circle', { cx: -.1, cy: -.12, r: .07, fill: 'rgba(255,255,255,.75)' }, inn);
    S('circle', { r: .47, class: 'halo' }, inn);
    return g;
  }));
}

function place(ci, ti, pos) {
  if (pos === -1) { const b = BASE_SLOT[ci][ti]; return { x: b.x, y: b.y, key: 'b' + ci + ti, solo: true, s: 1 }; }
  if (pos <= LOOP_END) { const g = (startG(ci) + pos) % LOOP_LEN; return { x: LOOP[g].x, y: LOOP[g].y, key: 'L' + g, s: 1 }; }
  if (pos < GOAL) { const h = pos - 69, c = HOME[armOf(ci)][h]; return { x: c.x, y: c.y, key: 'H' + ci + h, s: 1 }; }
  const [x, y] = pt(armOf(ci), 1.0, (ti - 1.5) * .3);
  return { x, y, key: 'G' + ci + ti, solo: true, s: .36 };
}

function renderTokens() {
  const groups = {};
  view.forEach((arr, pi) => arr.forEach((pos, ti) => {
    const info = place(players[pi].ci, ti, pos);
    (groups[info.key] = groups[info.key] || []).push({ pi, ti, info });
  }));
  for (const key in groups) {
    const g = groups[key], n = g.length;
    g.forEach((o, j) => {
      let { x, y, s } = o.info;
      if (n > 1 && !o.info.solo) {
        const ang = 2 * Math.PI * j / n - Math.PI / 2, rad = n === 2 ? .2 : .25;
        x += Math.cos(ang) * rad; y += Math.sin(ang) * rad; s = n >= 4 ? .6 : .74;
      }
      const e = tokEls[o.pi][o.ti];
      e.style.transform = `translate(${x}px, ${y}px)`;
      e.firstChild.style.transform = `scale(${s})`;
    });
  }
}

/* ====================== INÍCIO / ATUALIZAÇÃO DA TELA ================= */
function startView(snap, seat) {
  queue = []; busy = false;
  cur = snap; players = snap.players; mySeat = seat;
  viewRot = mode === 'online' && seat >= 0 ? (3 - armOf(players[seat].ci)) * 60 : 0;
  buildBoard();
  view = players.map(p => p.tokens.slice());
  renderTokens();
  drawDice($('#dice-big'), 0); drawDice($('#center-dice'), 0);
  $('#overlay').classList.remove('show');
  $('#msg').textContent = '';
  $('#room-badge').innerHTML = mode === 'online' ? 'Sala <b>' + NET.code + '</b>' : 'Modo local';
  show('game');
  keepAwake();
  refreshUI();
}

function refreshUI() {
  if (!cur) return;
  const s = cur;
  // lista de jogadores
  const list = $('#players-list'); list.innerHTML = '';
  s.players.forEach((p, i) => {
    const row = el('div', 'prow' + (i === s.turn && s.winner < 0 ? ' on' : ''));
    row.style.setProperty('--c', COLORS[p.ci].main);
    row.appendChild(el('span', 'dot'));
    row.appendChild(el('span', 'n', p.name + (mode === 'online' && i === mySeat ? ' (você)' : '') + (p.ai ? ' 🤖' : '')));
    row.appendChild(el('span', 'sc', '🏁 ' + p.tokens.filter(x => x === GOAL).length + '/4'));
    list.appendChild(row);
  });
  bars.forEach((b, k) => {
    const idx = players.findIndex(p => armOf(p.ci) === k);
    b.classList.toggle('turn', idx === s.turn && s.winner < 0);
  });

  // faixa da vez
  const cp = s.players[s.turn], banner = $('#turn-banner');
  banner.style.setProperty('--c', COLORS[cp.ci].main);
  banner.classList.toggle('dark', cp.ci === 3);
  banner.textContent = s.winner >= 0 ? 'Fim de jogo'
    : (mode === 'online' && s.turn === mySeat ? 'Sua vez!' : 'Vez de ' + cp.name);

  // interação
  const canRoll = isMine() && s.phase === 'roll' && !busy;
  $('#btn-roll').disabled = !canRoll;
  const opts = isMine() && s.phase === 'move' && !busy ? optionsOf(s) : [];
  tokEls.forEach((arr, pi) => arr.forEach((e, ti) => e.classList.toggle('movable', pi === s.turn && opts.includes(ti))));
  if (!busy && isMine()) {
    if (s.phase === 'roll') $('#msg').textContent = 'Role o dado.';
    else if (s.phase === 'move' && opts.length) $('#msg').textContent = 'Toque em uma peça brilhando para mover.';
  }
}

/* ========================= FILA DE EVENTOS ========================== */
function handle(snap, ev) { queue.push({ snap, ev }); pump(); }

async function pump() {
  if (busy) return;
  busy = true;
  while (queue.length) {
    const { snap, ev } = queue.shift();
    await present(snap, ev);
  }
  busy = false;
  refreshUI();
}

async function rollAnim(final) {
  const targets = [$('#dice-big'), $('#center-dice')];
  targets.forEach(t => t.classList.add('rolling'));
  const t0 = Date.now();
  while (Date.now() - t0 < 650) { targets.forEach(t => drawDice(t, rnd(6))); await wait(70); }
  targets.forEach(t => { t.classList.remove('rolling'); drawDice(t, final); });
}

async function animateMove(ev) {
  const e = tokEls[ev.p][ev.t];
  tokLayer.appendChild(e);       // traz a peça para frente
  if (ev.from === -1) { view[ev.p][ev.t] = 0; renderTokens(); await wait(380); }
  else for (let q = ev.from + 1; q <= ev.to; q++) { view[ev.p][ev.t] = q; renderTokens(); await wait(150); }
  if (ev.caps.length) {
    await wait(200);
    ev.caps.forEach(c => { view[c.p][c.t] = -1; });
    renderTokens(); await wait(500);
  }
}

async function present(snap, ev) {
  const msg = $('#msg');
  if (ev.type === 'roll') {
    cur = snap;
    refreshUI();
    await rollAnim(ev.dice);
    const who = nm(ev.p);
    if (ev.penalty) msg.textContent = who + ' tirou três 6 seguidos e perdeu a vez!';
    else if (ev.none) msg.textContent = who + ' tirou ' + ev.dice + ' e não tem jogada.';
    else msg.textContent = who + ' tirou ' + ev.dice + '.';
  } else if (ev.type === 'move') {
    const who = nm(ev.p);
    await animateMove(ev);
    cur = snap;
    view = snap.players.map(p => p.tokens.slice());
    renderTokens();
    if (ev.caps.length) msg.textContent = who + ' capturou ' + (ev.caps.length > 1 ? ev.caps.length + ' peças' : 'uma peça') + '! Joga de novo.';
    else if (ev.to === GOAL) msg.textContent = who + ' levou uma peça ao centro! Joga de novo.';
    else if (ev.extra) msg.textContent = who + ' tirou 6 e joga de novo.';
    if (ev.won) showWin(snap);
  } else {
    if (ev.type === 'turn' && cur && cur.turn !== snap.turn) { drawDice($('#dice-big'), 0); drawDice($('#center-dice'), 0); }
    cur = snap;
    if (ev.type === 'info') toast(ev.msg);
  }
  refreshUI();
}

function showWin(snap) {
  const p = snap.players[snap.winner];
  $('#win-title').textContent = p.name + ' venceu!';
  $('#win-title').parentNode.style.setProperty('--c', COLORS[p.ci].main);
  $('#win-sub').textContent = 'Parabéns! As 4 peças chegaram ao centro.';
  const again = $('#btn-again');
  if (mode === 'online' && !NET.isHost) { again.style.display = 'none'; $('#win-sub').textContent += ' Aguarde o host reabrir a sala.'; }
  else { again.style.display = ''; again.textContent = mode === 'online' ? 'Voltar para a sala' : 'Jogar novamente'; }
  $('#overlay').classList.add('show');
}

/* ============================== AÇÕES =============================== */
function act(kind, t) {
  if (mode === 'local' || NET.isHost) { if (!game) return; if (kind === 'roll') game.roll(); else game.move(t); }
  else if (NET.hostConn && NET.hostConn.open) NET.hostConn.send(kind === 'roll' ? { t: 'roll' } : { t: 'move', token: t });
}
function tryRoll() { if (cur && isMine() && cur.phase === 'roll' && !busy) act('roll'); }

$('#btn-roll').addEventListener('click', tryRoll);
$('#center-dice').addEventListener('click', tryRoll);
document.addEventListener('keydown', e => {
  if (curScreen === 'game' && (e.code === 'Space') && document.activeElement.tagName !== 'BUTTON') { e.preventDefault(); tryRoll(); }
});
svg.addEventListener('click', e => {
  const g = e.target.closest('.tk');
  if (!g || !cur || busy || !isMine() || cur.phase !== 'move') return;
  const p = +g.dataset.p, t = +g.dataset.t;
  if (p === cur.turn && optionsOf(cur).includes(t)) act('move', t);
});

/* ============================ MODO LOCAL ============================ */
let localN = 4;
const localCfg = Array.from({ length: 6 }, () => ({ name: '', ai: false }));

function renderLocal() {
  const cnt = $('#local-count'); cnt.innerHTML = '';
  for (let n = 2; n <= 6; n++) {
    const b = el('button', n === localN ? 'on' : '', String(n));
    b.addEventListener('click', () => { localN = n; renderLocal(); });
    cnt.appendChild(b);
  }
  const box = $('#local-seats'); box.innerHTML = '';
  for (let i = 0; i < localN; i++) {
    const ci = LAYOUT[localN][i], cfg = localCfg[i];
    const row = el('div', 'seat'); row.style.setProperty('--c', COLORS[ci].main);
    row.appendChild(el('span', 'sw'));
    const inp = el('input'); inp.type = 'text'; inp.maxLength = 12; inp.placeholder = 'Jogador ' + (i + 1); inp.value = cfg.name;
    inp.setAttribute('aria-label', 'Nome do jogador ' + (i + 1));
    inp.addEventListener('input', () => { cfg.name = inp.value; });
    row.appendChild(inp);
    const kind = el('button', 'btn small kind ' + (cfg.ai ? '' : 'blue'), cfg.ai ? '🤖 CPU' : '👤 Humano');
    kind.addEventListener('click', () => { cfg.ai = !cfg.ai; renderLocal(); });
    row.appendChild(kind);
    box.appendChild(row);
  }
}

function startLocal(seats) {
  if (game) game.dispose();
  mode = 'local'; NET.isHost = false;
  localSeatsCfg = seats;
  game = new Game(seats, (snap, ev) => handle(snap, ev));
  startView(game.snapshot(), -1);
  game.plan();
}

$('#btn-local-start').addEventListener('click', () => {
  const seats = localCfg.slice(0, localN).map((c, i) => ({ name: c.name.trim() || (c.ai ? 'CPU ' + (i + 1) : 'Jogador ' + (i + 1)), ai: c.ai }));
  startLocal(seats);
});

/* ============================ MODO ONLINE =========================== */
const NET = { peer: null, isHost: false, code: '', lobby: [], seatConns: [], hostConn: null, running: false, leaving: false };
const PEER_URLS = [
  'https://unpkg.com/peerjs@1.5.4/dist/peerjs.min.js',
  'https://cdn.jsdelivr.net/npm/peerjs@1.5.4/dist/peerjs.min.js'
];
const ID_PREFIX = 'ludo6-';
// STUN descobre o endereço público; TURN retransmite quando o celular (4G) e o PC não conseguem se ligar direto.
const PEER_OPTS = {
  debug: 0,
  config: {
    iceServers: [
      { urls: ['stun:stun.l.google.com:19302', 'stun:stun1.l.google.com:19302', 'stun:global.stun.twilio.com:3478'] },
      { urls: ['turn:openrelay.metered.ca:80', 'turn:openrelay.metered.ca:443', 'turn:openrelay.metered.ca:443?transport=tcp'], username: 'openrelayproject', credential: 'openrelayproject' }
    ],
    iceCandidatePoolSize: 4
  }
};
function remember(name, code) {
  try { if (name) localStorage.setItem('ludo-name', name); if (code) localStorage.setItem('ludo-code', code); } catch (e) { /* ignora */ }
}
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

function loadPeerJS() {
  if (window.Peer) return Promise.resolve();
  return new Promise((res, rej) => {
    let i = 0;
    const next = () => {
      if (i >= PEER_URLS.length) return rej(new Error('peerjs'));
      const s = document.createElement('script');
      s.src = PEER_URLS[i++];
      s.onload = () => (window.Peer ? res() : next());
      s.onerror = next;
      document.head.appendChild(s);
    };
    next();
  });
}
const genCode = () => Array.from({ length: 5 }, () => CODE_CHARS[Math.floor(Math.random() * CODE_CHARS.length)]).join('');
const setStatus = msg => { $('#online-status').textContent = msg || ''; };
const cleanName = v => (v || '').trim().slice(0, 12);

function cleanupNet() {
  NET.leaving = true;
  try { if (NET.peer) NET.peer.destroy(); } catch (e) { /* ignora */ }
  NET.peer = null; NET.hostConn = null; NET.lobby = []; NET.seatConns = []; NET.running = false; NET.isHost = false;
  setTimeout(() => { NET.leaving = false; }, 0);
}
function leaveAll(msg) {
  if (game) { game.dispose(); game = null; }
  cleanupNet();
  queue = []; busy = false; cur = null; mode = null;
  $('#overlay').classList.remove('show');
  show('menu');
  if (msg) toast(msg);
}

/* ---------- criar sala (host) ---------- */
async function createRoom() {
  const name = cleanName($('#online-name').value) || 'Jogador 1';
  remember(name);
  setStatus('Criando sala...');
  try { await loadPeerJS(); } catch (e) { setStatus('Não foi possível carregar o PeerJS. Verifique sua conexão com a internet.'); return; }
  const tryCreate = attempt => {
    const code = genCode();
    const peer = new Peer(ID_PREFIX + code, PEER_OPTS);
    peer.on('open', () => {
      NET.peer = peer; NET.isHost = true; NET.code = code; NET.running = false;
      NET.lobby = [{ name, conn: null }];
      mode = 'online';
      setStatus('');
      show('lobby'); pushLobby();
    });
    peer.on('connection', conn => {
      conn.on('data', m => hostMsg(conn, m));
      conn.on('close', () => guestLeft(conn));
      conn.on('error', () => guestLeft(conn));
    });
    peer.on('error', err => {
      if (err.type === 'unavailable-id' && attempt < 5) { peer.destroy(); tryCreate(attempt + 1); return; }
      if (NET.peer === peer || !NET.peer) { setStatus('Erro de conexão (' + err.type + '). Tente novamente.'); }
    });
    peer.on('disconnected', () => { try { peer.reconnect(); } catch (e) { /* ignora */ } });
  };
  tryCreate(0);
}

function hostMsg(conn, m) {
  if (!m || !m.t) return;
  if (m.t === 'join') {
    if (NET.running) {           // reconexão: quem caiu volta usando o mesmo nome
      const nmx = cleanName(m.name).toLowerCase();
      const i = game ? game.s.players.findIndex(p => p.gone && p.name.toLowerCase() === nmx) : -1;
      if (i < 0) { conn.send({ t: 'err', msg: 'A partida já começou. Para voltar, entre com o mesmo nome de antes.' }); setTimeout(() => conn.close(), 400); return; }
      game.markBack(i);
      NET.seatConns[i] = conn;
      conn.send({ t: 'start', snap: game.snapshot(), you: i });
      return;
    }
    if (NET.lobby.length >= 6) { conn.send({ t: 'err', msg: 'Sala cheia (6/6).' }); setTimeout(() => conn.close(), 400); return; }
    if (NET.lobby.some(x => x.conn === conn)) return;
    let name = cleanName(m.name) || 'Jogador';
    const base = name; let n = 2;
    while (NET.lobby.some(x => x.name.toLowerCase() === name.toLowerCase())) name = base.slice(0, 10) + ' ' + (n++);
    NET.lobby.push({ name, conn });
    pushLobby();
  } else if (m.t === 'roll') {
    const i = NET.seatConns.indexOf(conn);
    if (game && NET.running && i >= 0 && game.s.turn === i) game.roll();
  } else if (m.t === 'move') {
    const i = NET.seatConns.indexOf(conn);
    if (game && NET.running && i >= 0 && game.s.turn === i) game.move(+m.token);
  }
}

function guestLeft(conn) {
  if (!NET.isHost) return;
  if (NET.running) {
    const i = NET.seatConns.indexOf(conn);
    if (i > 0 && game) game.markGone(i);
  } else {
    const before = NET.lobby.length;
    NET.lobby = NET.lobby.filter(x => x.conn !== conn);
    if (NET.lobby.length !== before) pushLobby();
  }
}

function pushLobby() {
  const names = NET.lobby.map(x => x.name);
  NET.lobby.forEach((x, i) => { if (x.conn && x.conn.open) x.conn.send({ t: 'lobby', names, you: i, code: NET.code }); });
  renderLobby(names, 0, true);
}

function renderLobby(names, you, isHost) {
  $('#lobby-code').textContent = NET.code;
  $('#lobby-count').textContent = 'Jogadores (' + names.length + '/6)';
  const ul = $('#lobby-list'); ul.innerHTML = '';
  for (let i = 0; i < 6; i++) {
    const li = el('li', names[i] ? '' : 'empty');
    if (names[i]) {
      li.appendChild(el('span', 'n', names[i] + (i === you ? ' (você)' : '')));
      if (i === 0) li.appendChild(el('span', 'tag', 'host'));
    } else li.appendChild(el('span', 'n', 'Aguardando jogador...'));
    ul.appendChild(li);
  }
  const start = $('#btn-start');
  start.style.display = isHost ? '' : 'none';
  start.disabled = names.length < 2;
  $('#lobby-status').textContent = isHost
    ? (names.length < 2 ? 'Compartilhe o código e espere pelo menos mais 1 jogador.' : 'Tudo pronto. Inicie quando todos entrarem.')
    : 'Aguardando o host iniciar a partida...';
}

function hostStart() {
  if (!NET.isHost || NET.lobby.length < 2) return;
  NET.running = true;
  NET.seatConns = NET.lobby.map(x => x.conn);
  const seats = NET.lobby.map(x => ({ name: x.name, ai: false }));
  if (game) game.dispose();
  game = new Game(seats, (snap, ev) => {
    NET.seatConns.forEach(c => { if (c && c.open) c.send({ t: 'ev', snap, ev }); });
    handle(snap, ev);
  });
  const snap = game.snapshot();
  NET.seatConns.forEach((c, i) => { if (c && c.open) c.send({ t: 'start', snap, you: i }); });
  mode = 'online';
  startView(snap, 0);
  game.plan();
}

function backToLobby() {            // host: volta todos para a sala
  if (game) { game.dispose(); game = null; }
  NET.running = false;
  NET.lobby = NET.lobby.filter(x => !x.conn || x.conn.open);
  NET.lobby.forEach(x => { if (x.conn && x.conn.open) x.conn.send({ t: 'back' }); });
  $('#overlay').classList.remove('show');
  queue = []; busy = false;
  show('lobby'); pushLobby();
}

/* ---------- entrar na sala (convidado) ---------- */
async function joinRoom() {
  const name = cleanName($('#online-name').value) || 'Jogador';
  const code = $('#online-code').value.trim().toUpperCase();
  if (code.length < 5) { setStatus('Digite o código de 5 caracteres da sala.'); return; }
  remember(name, code);
  setStatus('Conectando...');
  try { await loadPeerJS(); } catch (e) { setStatus('Não foi possível carregar o PeerJS. Verifique sua conexão com a internet.'); return; }
  cleanupNet();
  const peer = new Peer(undefined, PEER_OPTS);
  NET.peer = peer; NET.code = code; NET.isHost = false;
  let opened = false;
  const fail = msg => { clearTimeout(to); setStatus(msg); cleanupNet(); show('online'); };
  const to = setTimeout(() => { if (!opened) fail('Tempo esgotado. Confira o código e a internet.'); }, 14000);
  peer.on('error', err => fail(err.type === 'peer-unavailable' ? 'Sala não encontrada. Confira o código.' : 'Erro de conexão (' + err.type + ').'));
  peer.on('open', () => {
    const conn = peer.connect(ID_PREFIX + code, { reliable: true });
    NET.hostConn = conn;
    conn.on('open', () => {
      opened = true; clearTimeout(to);
      mode = 'online';
      conn.send({ t: 'join', name });
    });
    conn.on('data', guestMsg);
    conn.on('close', () => { if (!NET.leaving && mode === 'online') leaveAll('A sala foi encerrada pelo host.'); });
    conn.on('error', () => { if (!NET.leaving && mode === 'online') leaveAll('Conexão perdida.'); });
  });
}

function guestMsg(m) {
  if (!m || !m.t) return;
  if (m.t === 'lobby') {
    renderLobby(m.names, m.you, false);
    setStatus('');
    if (curScreen !== 'lobby') show('lobby');
  } else if (m.t === 'start') {
    mode = 'online'; startView(m.snap, m.you);
  } else if (m.t === 'ev') {
    handle(m.snap, m.ev);
  } else if (m.t === 'back') {
    $('#overlay').classList.remove('show'); queue = []; busy = false; show('lobby');
  } else if (m.t === 'err') {
    const msg = m.msg; cleanupNet(); setStatus(msg); show('online');
  }
}

/* ============================ NAVEGAÇÃO ============================= */
document.querySelectorAll('[data-go]').forEach(b => b.addEventListener('click', () => show(b.dataset.go)));
$('#btn-online').addEventListener('click', () => { setStatus(''); show('online'); });
$('#btn-local').addEventListener('click', () => { renderLocal(); show('local'); });
$('#btn-create').addEventListener('click', createRoom);
$('#btn-join').addEventListener('click', joinRoom);
$('#online-code').addEventListener('input', e => { e.target.value = e.target.value.toUpperCase().replace(/[^A-Z0-9]/g, ''); });
$('#online-code').addEventListener('keydown', e => { if (e.key === 'Enter') joinRoom(); });
$('#btn-start').addEventListener('click', hostStart);
$('#btn-copy-code').addEventListener('click', () => copyText(NET.code));
$('#btn-copy-link').addEventListener('click', () => {
  copyText(location.origin + location.pathname + '?sala=' + NET.code);
});
$('#btn-lobby-leave').addEventListener('click', () => leaveAll());
$('#btn-leave').addEventListener('click', () => { if (confirm('Sair da partida?')) leaveAll(); });
$('#btn-win-menu').addEventListener('click', () => leaveAll());
$('#btn-again').addEventListener('click', () => {
  if (mode === 'online') backToLobby();
  else if (localSeatsCfg) startLocal(localSeatsCfg);
});

document.addEventListener('visibilitychange', () => {
  if (document.visibilityState !== 'visible') return;
  if (curScreen === 'game') keepAwake();
  if (mode === 'online' && !NET.isHost && NET.hostConn && !NET.hostConn.open && (curScreen === 'game' || curScreen === 'lobby')) {
    leaveAll('Conexão perdida. Entre de novo na sala com o mesmo nome para voltar à partida.');
  }
});
try {                          // lembra nome e última sala neste aparelho
  $('#online-name').value = localStorage.getItem('ludo-name') || '';
  $('#online-code').value = localStorage.getItem('ludo-code') || '';
} catch (e) { /* ignora */ }

// link de convite: ?sala=ABCDE abre direto a tela de entrada
(function () {
  const code = (new URLSearchParams(location.search).get('sala') || '').toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 5);
  if (code) { $('#online-code').value = code; show('online'); setStatus('Digite seu nome e toque em Entrar.'); }
})();
