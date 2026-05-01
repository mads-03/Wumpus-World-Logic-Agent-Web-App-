/* ══════════════════════════════════════════════════════════════
   Wumpus World — Logic Agent
   ══════════════════════════════════════════════════════════════
   Sections:
     1. World State
     2. World Generator
     3. Percept Engine
     4. Knowledge Base (Propositional Logic)
     5. CNF Conversion
     6. Resolution Refutation Engine
     7. Agent Decision Logic
     8. UI Renderer
     9. Controls & Event Wiring
   ══════════════════════════════════════════════════════════════ */

/* ── 1. World State ───────────────────────────────────────── */
let W = {
  rows: 4, cols: 4,
  grid: [],          // 2D: {pit, wumpus, gold, breeze, stench, glitter}
  agent: {r:0, c:0},
  alive: true,
  won: false,
  hasGold: false,
  visited: new Set(),
  safeKnown: new Set(),
  dangerKnown: new Set(),
  kb: [],            // array of CNF clauses (each clause = Set of literals)
  kbLog: [],         // human-readable KB entries for display
  inferenceSteps: 0,
  autoTimer: null,
  entailCache: new Map(), // memoize ask() results
};

/* ── 2. World Generator ───────────────────────────────────── */
function generateWorld(rows, cols, numPits) {
  const grid = Array.from({length: rows}, () =>
    Array.from({length: cols}, () => ({
      pit: false, wumpus: false, gold: false,
      breeze: false, stench: false, glitter: false,
    }))
  );

  const allCells = [];
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      if (!(r === 0 && c === 0)) allCells.push([r, c]);

  shuffle(allCells);

  // Place pits
  const pitCells = allCells.splice(0, Math.min(numPits, allCells.length));
  pitCells.forEach(([r, c]) => { grid[r][c].pit = true; });

  // Place wumpus
  if (allCells.length > 0) {
    const [wr, wc] = allCells.splice(0, 1)[0];
    grid[wr][wc].wumpus = true;
  }

  // Place gold
  if (allCells.length > 0) {
    const [gr, gc] = allCells.splice(0, 1)[0];
    grid[gr][gc].gold = true;
    grid[gr][gc].glitter = true;
  }

  // Compute breeze & stench
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      neighbors(r, c, rows, cols).forEach(([nr, nc]) => {
        if (grid[nr][nc].pit)    grid[r][c].breeze = true;
        if (grid[nr][nc].wumpus) grid[r][c].stench = true;
      });
    }
  }

  return grid;
}

function neighbors(r, c, rows, cols) {
  return [[r-1,c],[r+1,c],[r,c-1],[r,c+1]]
    .filter(([nr,nc]) => nr>=0 && nc>=0 && nr<rows && nc<cols);
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}

/* ── 3. Percept Engine ────────────────────────────────────── */
function getPercepts(r, c) {
  const cell = W.grid[r][c];
  return {
    breeze:  cell.breeze,
    stench:  cell.stench,
    glitter: cell.glitter,
    bump:    false,
    scream:  false,
  };
}

/* ── 4. Knowledge Base ────────────────────────────────────── */

// Literal helpers
function litP(r, c)  { return `P_${r}_${c}`; }
function litW(r, c)  { return `W_${r}_${c}`; }
function litB(r, c)  { return `B_${r}_${c}`; }
function litS(r, c)  { return `S_${r}_${c}`; }
function neg(lit)    { return lit.startsWith('~') ? lit.slice(1) : '~' + lit; }

function tell(r, c, percepts) {
  const ns = neighbors(r, c, W.rows, W.cols);

  // Known safe: visited cell has no pit or wumpus
  addClause([neg(litP(r,c))]);
  addClause([neg(litW(r,c))]);
  W.safeKnown.add(key(r,c));

  if (!percepts.breeze) {
    ns.forEach(([nr,nc]) => {
      addClause([neg(litP(nr,nc))]);
      logKB(`¬breeze@(${r},${c}) → ¬P(${nr},${nc})`, 'safe');
    });
  } else {
    const pitDisj = ns.map(([nr,nc]) => litP(nr,nc));
    addClause(pitDisj);                 // B_r_c → (P1 ∨ P2 ∨ ...)
    addClause([litB(r,c)]);             // assert B_r_c
    // (¬P_i ∨ B_r_c) for each neighbor (reverse direction)
    ns.forEach(([nr,nc]) => addClause([neg(litP(nr,nc)), litB(r,c)]));
    logKB(`breeze@(${r},${c}) ↔ ${pitDisj.map(l=>`P(${l.slice(2).replace('_',',')})`).join(' ∨ ')}`, 'danger');
  }

  if (!percepts.stench) {
    ns.forEach(([nr,nc]) => {
      addClause([neg(litW(nr,nc))]);
      logKB(`¬stench@(${r},${c}) → ¬W(${nr},${nc})`, 'safe');
    });
  } else {
    const wDisj = ns.map(([nr,nc]) => litW(nr,nc));
    addClause(wDisj);                   // S_r_c → (W1 ∨ W2 ∨ ...)
    addClause([litS(r,c)]);             // assert S_r_c
    // (¬W_i ∨ S_r_c) for each neighbor (reverse direction)
    ns.forEach(([nr,nc]) => addClause([neg(litW(nr,nc)), litS(r,c)]));
    logKB(`stench@(${r},${c}) ↔ ${wDisj.map(l=>`W(${l.slice(2).replace('_',',')})`).join(' ∨ ')}`, 'danger');
  }

  W.entailCache.clear(); // KB changed → invalidate cache
}

function addClause(literals) {
  const clause = new Set(literals);
  for (const lit of clause) {
    if (clause.has(neg(lit))) return;
  }
  for (const existing of W.kb) {
    if (isSubset(existing, clause)) return;
  }
  W.kb.push(clause);
}

function isSubset(a, b) {
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

function logKB(msg, type) {
  W.kbLog.unshift({ msg, type });
  if (W.kbLog.length > 40) W.kbLog.pop();
}

/* ── 5. CNF Conversion ────────────────────────────────────── */
// KB is already maintained in CNF.

/* ── 6. Resolution Refutation Engine ─────────────────────── */
function ask(literal) {
  if (W.entailCache.has(literal)) return W.entailCache.get(literal);

  const clauses = W.kb.map(c => new Set(c));
  clauses.push(new Set([neg(literal)]));

  const seen = new Set(clauses.map(setToKey));

  let i = 0;
  while (i < clauses.length) {
    for (let j = 0; j < i; j++) {
      const resolvents = resolve(clauses[i], clauses[j]);
      for (const r of resolvents) {
        if (r.size === 0) {
          W.entailCache.set(literal, true);
          return true;
        }
        const k = setToKey(r);
        if (!seen.has(k)) {
          seen.add(k);
          clauses.push(r);
          if (clauses.length > 2000) {
            W.entailCache.set(literal, false);
            return false;
          }
        }
      }
    }
    i++;
  }
  W.entailCache.set(literal, false);
  return false;
}

function resolve(c1, c2) {
  const results = [];
  for (const lit of c1) {
    if (c2.has(neg(lit))) {
      W.inferenceSteps++; // count resolution attempts
      const resolvent = new Set([...c1, ...c2]);
      resolvent.delete(lit);
      resolvent.delete(neg(lit));
      let tautology = false;
      for (const l of resolvent) {
        if (resolvent.has(neg(l))) { tautology = true; break; }
      }
      if (!tautology) results.push(resolvent);
    }
  }
  return results;
}

function setToKey(s) {
  return [...s].sort().join('|');
}

/* ── 7. Agent Decision Logic ──────────────────────────────── */
function isSafe(r, c) {
  if (W.safeKnown.has(key(r,c))) return true;
  const noPit    = ask(neg(litP(r,c)));
  const noWumpus = ask(neg(litW(r,c)));
  if (noPit && noWumpus) {
    W.safeKnown.add(key(r,c));
    logKB(`Proved safe: (${r},${c}) via resolution`, 'infer');
    return true;
  }
  return false;
}

function isDangerous(r, c) {
  if (W.dangerKnown.has(key(r,c))) return true;
  const hasPit    = ask(litP(r,c));
  const hasWumpus = ask(litW(r,c));
  if (hasPit || hasWumpus) {
    W.dangerKnown.add(key(r,c));
    logKB(`Proved danger: (${r},${c}) ${hasPit?'[pit]':''} ${hasWumpus?'[wumpus]':''}`, 'danger');
    return true;
  }
  return false;
}

function agentStep() {
  if (!W.alive || W.won) return;

  const {r, c} = W.agent;

  const cell = W.grid[r][c];
  if (cell.pit || cell.wumpus) {
    W.alive = false;
    setStatus(`💀 Agent died at (${r},${c})${cell.pit?' — fell into a pit':' — eaten by Wumpus'}!`);
    appendLog(`Died at (${r},${c})`, 'danger');
    stopAutoRun();
    renderGrid();
    return;
  }

  if (cell.gold && !W.hasGold) {
    W.hasGold = true;
    cell.gold = false;
    cell.glitter = false;
    W.won = true;
    setStatus('🏆 Agent found the gold! Mission complete!');
    appendLog(`Gold collected at (${r},${c})!`, 'safe');
    stopAutoRun();
    renderGrid();
    updateMetrics();
    return;
  }

  const percepts = getPercepts(r, c);
  W.visited.add(key(r,c));
  tell(r, c, percepts);

  const pList = [];
  if (percepts.breeze)  pList.push('Breeze');
  if (percepts.stench)  pList.push('Stench');
  if (percepts.glitter) pList.push('Glitter');
  updatePerceptDisplay(pList.length ? pList.join(', ') : 'None');
  appendLog(`Moved to (${r},${c}) — percepts: ${pList.length ? pList.join(', ') : 'none'}`, 'move');

  const ns = neighbors(r, c, W.rows, W.cols);
  const safeUnvisited = [], unknowns = [];

  for (const [nr, nc] of ns) {
    const k = key(nr, nc);
    if (W.visited.has(k)) continue;
    if (isDangerous(nr, nc)) {
      continue;
    } else if (isSafe(nr, nc)) {
      safeUnvisited.push([nr, nc]);
    } else {
      unknowns.push([nr, nc]);
    }
  }

  renderGrid();
  updateMetrics();
  updateKBDisplay();

  let next = null;

  if (safeUnvisited.length > 0) {
    next = safeUnvisited[0];
    appendLog(`Moving to safe cell (${next[0]},${next[1]})`, 'safe');
  } else {
    for (const k of W.safeKnown) {
      const [sr, sc] = k.split(',').map(Number);
      if (!W.visited.has(k)) {
        const path = bfsPath(r, c, sr, sc);
        if (path && path.length > 0) {
          next = path[0];
          appendLog(`Backtracking toward safe cell (${sr},${sc})`, 'infer');
          break;
        }
      }
    }

    if (!next && unknowns.length > 0) {
      next = unknowns[0];
      appendLog(`Taking risk on unknown cell (${next[0]},${next[1]})`, 'infer');
    }
  }

  if (!next) {
    setStatus('Agent is stuck — no safe moves available.');
    appendLog('No moves available.', 'danger');
    stopAutoRun();
    return;
  }

  W.agent = {r: next[0], c: next[1]};
  setStatus(`Agent at (${W.agent.r},${W.agent.c})`);
}

function bfsPath(sr, sc, tr, tc) {
  if (sr === tr && sc === tc) return [];
  const queue = [[sr, sc, []]];
  const seen = new Set([key(sr,sc)]);
  while (queue.length) {
    const [r, c, path] = queue.shift();
    for (const [nr, nc] of neighbors(r, c, W.rows, W.cols)) {
      const k = key(nr, nc);
      if (seen.has(k)) continue;
      if (!W.visited.has(k) && !(nr === tr && nc === tc)) continue;
      if (!W.safeKnown.has(k) && !(nr === tr && nc === tc)) continue;
      seen.add(k);
      const newPath = [...path, [nr, nc]];
      if (nr === tr && nc === tc) return newPath;
      queue.push([nr, nc, newPath]);
    }
  }
  return null;
}

function key(r, c) { return `${r},${c}`; }

/* ── 8. UI Renderer ───────────────────────────────────────── */
function renderGrid() {
  const gridEl = document.getElementById('grid');
  gridEl.style.gridTemplateColumns = `repeat(${W.cols}, 64px)`;
  gridEl.innerHTML = '';

  for (let r = 0; r < W.rows; r++) {
    for (let c = 0; c < W.cols; c++) {
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.dataset.r = r;
      cell.dataset.c = c;

      const label = document.createElement('div');
      label.className = 'cell-label';
      label.textContent = `${r},${c}`;

      const content = document.createElement('div');
      content.className = 'cell-content';

      const percept = document.createElement('div');
      percept.className = 'cell-percept';

      const k = key(r, c);
      const isAgent = W.agent.r === r && W.agent.c === c;
      const isVisited = W.visited.has(k);
      const isSafeCell = W.safeKnown.has(k);
      const isDangerCell = W.dangerKnown.has(k);

      const reveal = isVisited || !W.alive || W.won;

      if (isAgent) {
        cell.classList.add('agent');
        content.textContent = '🤖';
      } else if (!reveal && !isSafeCell && !isDangerCell) {
        cell.classList.add('unknown');
        content.textContent = '?';
      } else {
        if (isDangerCell) {
          cell.classList.add('danger');
          content.textContent = reveal ? (W.grid[r][c].pit ? '🕳️' : W.grid[r][c].wumpus ? '👾' : '⚠️') : '⚠️';
        } else if (isSafeCell || isVisited) {
          cell.classList.add('safe');
          if (reveal) {
            if (W.grid[r][c].pit)    content.textContent = '🕳️';
            else if (W.grid[r][c].wumpus) content.textContent = '👾';
            else if (W.grid[r][c].gold)   content.textContent = '🏆';
            else content.textContent = '✓';
          } else {
            content.textContent = '✓';
          }
        } else {
          cell.classList.add('unknown');
          content.textContent = '?';
        }
      }

      if (isVisited && W.alive) {
        const p = getPercepts(r, c);
        const hints = [];
        if (p.breeze)  hints.push('B');
        if (p.stench)  hints.push('S');
        if (p.glitter) hints.push('G');
        percept.textContent = hints.join(' ');
      }

      cell.appendChild(label);
      cell.appendChild(content);
      cell.appendChild(percept);

      cell.addEventListener('click', () => {
        if (!W.alive || W.won) return;
        const {r: ar, c: ac} = W.agent;
        const isAdj = neighbors(ar, ac, W.rows, W.cols).some(([nr,nc]) => nr===r && nc===c);
        if (isAdj) {
          W.agent = {r, c};
          agentStep();
        }
      });

      gridEl.appendChild(cell);
    }
  }
}

function setStatus(msg) {
  document.getElementById('status-msg').textContent = msg;
}

function appendLog(msg, type) {
  const log = document.getElementById('log');
  const entry = document.createElement('div');
  entry.className = `log-entry log-${type}`;
  entry.textContent = `▸ ${msg}`;
  log.prepend(entry);
  while (log.children.length > 60) log.removeChild(log.lastChild);
}

function updateMetrics() {
  document.getElementById('m-steps').textContent   = W.inferenceSteps;
  document.getElementById('m-visited').textContent = W.visited.size;
  document.getElementById('m-safe').textContent    = W.safeKnown.size;
  document.getElementById('m-danger').textContent  = W.dangerKnown.size;
}

function updatePerceptDisplay(text) {
  document.getElementById('percept-display').textContent = text || '—';
}

function updateKBDisplay() {
  const el = document.getElementById('kb-display');
  const showCNF = document.getElementById('kb-mode-toggle').checked;

  if (showCNF) {
    if (W.kb.length === 0) { el.textContent = '—'; return; }
    el.innerHTML = W.kb.slice(-20).map(clause => {
      const lits = [...clause].map(l => l.startsWith('~') ? `¬${l.slice(1)}` : l);
      return `<div class="log-entry">${lits.join(' ∨ ')}</div>`;
    }).reverse().join('');
    return;
  }

  if (W.kbLog.length === 0) { el.textContent = '—'; return; }
  el.innerHTML = W.kbLog.slice(0, 15).map(({msg, type}) =>
    `<div class="log-entry log-${type === 'safe' ? 'safe' : type === 'danger' ? 'danger' : 'infer'}">${msg}</div>`
  ).join('');
}

function stopAutoRun() {
  if (W.autoTimer) {
    clearInterval(W.autoTimer);
    W.autoTimer = null;
    document.getElementById('btn-auto').textContent = 'Auto run';
  }
}

/* ── 9. Controls & Event Wiring ───────────────────────────── */
function initGame() {
  const rows    = parseInt(document.getElementById('rows-input').value) || 4;
  const cols    = parseInt(document.getElementById('cols-input').value) || 4;
  const numPits = parseInt(document.getElementById('pits-input').value) || 3;

  W = {
    rows, cols,
    grid: generateWorld(rows, cols, numPits),
    agent: {r:0, c:0},
    alive: true,
    won: false,
    hasGold: false,
    visited: new Set(),
    safeKnown: new Set(),
    dangerKnown: new Set(),
    kb: [],
    kbLog: [],
    inferenceSteps: 0,
    autoTimer: null,
    entailCache: new Map(),
  };

  W.safeKnown.add('0,0');
  W.visited.add('0,0');

  document.getElementById('setup-screen').style.display = 'none';
  document.getElementById('game-screen').style.display  = 'block';
  document.getElementById('log').innerHTML = '';

  setStatus('Agent at (0,0) — press Step or Auto run');
  updatePerceptDisplay('None');
  updateKBDisplay();

  const percepts = getPercepts(0, 0);
  tell(0, 0, percepts);
  const pList = [];
  if (percepts.breeze)  pList.push('Breeze');
  if (percepts.stench)  pList.push('Stench');
  if (percepts.glitter) pList.push('Glitter');
  updatePerceptDisplay(pList.length ? pList.join(', ') : 'None');
  appendLog(`Start at (0,0) — percepts: ${pList.length ? pList.join(', ') : 'none'}`, 'move');

  renderGrid();
  updateMetrics();
  updateKBDisplay();
}

document.getElementById('start-btn').addEventListener('click', initGame);

document.getElementById('restart-btn').addEventListener('click', () => {
  stopAutoRun();
  document.getElementById('setup-screen').style.display = 'block';
  document.getElementById('game-screen').style.display  = 'none';
});

document.getElementById('btn-step').addEventListener('click', () => {
  if (!W.alive || W.won) return;
  agentStep();
});

document.getElementById('btn-auto').addEventListener('click', () => {
  if (!W.alive || W.won) return;
  if (W.autoTimer) {
    stopAutoRun();
    return;
  }
  document.getElementById('btn-auto').textContent = 'Stop';
  W.autoTimer = setInterval(() => {
    if (!W.alive || W.won) {
      stopAutoRun();
      return;
    }
    agentStep();
  }, 600);
});

document.getElementById('kb-mode-toggle').addEventListener('change', updateKBDisplay);