'use strict';

/* ===================== Difficulty config ===================== */

const DIFFICULTIES = {
  easy:   { size: 6,  animals: 6,  flowers: 3 },
  medium: { size: 8,  animals: 10, flowers: 4 },
  hard:   { size: 10, animals: 15, flowers: 5 },
};

const DIFFICULTY_ORDER = ['easy', 'medium', 'hard'];

/* ===================== Solver ===================== */

function isAdjacentToAnyCreature(grid, row, col) {
  for (let dr = -1; dr <= 1; dr++) {
    for (let dc = -1; dc <= 1; dc++) {
      if (dr === 0 && dc === 0) continue;
      const r = row + dr, c = col + dc;
      if (r < 0 || c < 0 || r >= grid.length || c >= grid[0].length) continue;
      if (grid[r][c] > 0) return true; // > 0: user marks are stored as -1
    }
  }
  return false;
}

// Counts solutions of a puzzle definition up to `limit` (backtracking with
// row/column/type-count pruning and partial clue-sum pruning).
// Returns { count, solution, aborted } where solution is the first one found.
// If nodeBudget is given and the search exceeds it, it stops early with
// aborted: true — the count is then a lower bound, NOT a completed proof.
function countSolutions(puzzle, limit, nodeBudget) {
  const size = puzzle.size;
  const rowCounts = puzzle.rowCounts;
  const colCounts = puzzle.colCounts;
  const typeCounts = puzzle.typeCounts;
  const totalNeeded = typeCounts[1] + typeCounts[2] + typeCounts[3] + typeCounts[4];

  // Locked cells are forced empty: clue cells (which also carry a target
  // neighbor-horn sum, checked incrementally as neighbors get assigned) and
  // flower cells (blocked squares with no sum).
  const clueIndex = [];
  const locked = [];
  for (let r = 0; r < size; r++) {
    clueIndex.push(new Array(size).fill(-1));
    locked.push(new Array(size).fill(false));
  }
  const clueTargets = [];
  for (const key of Object.keys(puzzle.clueCells)) {
    const parts = key.split(',');
    clueIndex[Number(parts[0])][Number(parts[1])] = clueTargets.length;
    locked[Number(parts[0])][Number(parts[1])] = true;
    clueTargets.push(puzzle.clueCells[key]);
  }
  for (const key of Object.keys(puzzle.flowerCells || {})) {
    const parts = key.split(',');
    locked[Number(parts[0])][Number(parts[1])] = true;
  }
  const nClues = clueTargets.length;

  const clueTotalN = new Array(nClues).fill(0);
  const clueNeighborsOf = [];
  for (let i = 0; i < size * size; i++) clueNeighborsOf.push([]);
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      const q = clueIndex[r][c];
      if (q < 0) continue;
      for (let dr = -1; dr <= 1; dr++) {
        for (let dc = -1; dc <= 1; dc++) {
          if (dr === 0 && dc === 0) continue;
          const nr = r + dr, nc = c + dc;
          if (nr < 0 || nc < 0 || nr >= size || nc >= size) continue;
          if (locked[nr][nc]) continue;
          clueTotalN[q]++;
          clueNeighborsOf[nr * size + nc].push(q);
        }
      }
    }
  }
  for (let q = 0; q < nClues; q++) {
    if (clueTotalN[q] === 0 && clueTargets[q] !== 0) return { count: 0, solution: null };
  }

  // Suffix capacities (free cells remaining), for "can this row/col/board
  // still reach its required count" pruning.
  const rowCapAfter = [];
  for (let r = 0; r < size; r++) {
    const arr = new Array(size + 1).fill(0);
    for (let c = size - 1; c >= 0; c--) arr[c] = arr[c + 1] + (locked[r][c] ? 0 : 1);
    rowCapAfter.push(arr);
  }
  const colCapAfter = [];
  for (let r = 0; r <= size; r++) colCapAfter.push(new Array(size).fill(0));
  for (let r = size - 1; r >= 0; r--) {
    for (let c = 0; c < size; c++) {
      colCapAfter[r][c] = colCapAfter[r + 1][c] + (locked[r][c] ? 0 : 1);
    }
  }
  const globalCapAfter = new Array(size * size + 1).fill(0);
  for (let i = size * size - 1; i >= 0; i--) {
    const r = Math.floor(i / size), c = i % size;
    globalCapAfter[i] = globalCapAfter[i + 1] + (locked[r][c] ? 0 : 1);
  }

  const grid = [];
  for (let r = 0; r < size; r++) grid.push(new Array(size).fill(0));
  const rowUsed = new Array(size).fill(0);
  const colUsed = new Array(size).fill(0);
  const typeUsed = [0, 0, 0, 0, 0];
  const cluePartial = new Array(nClues).fill(0);
  const clueAssigned = new Array(nClues).fill(0);
  let placedTotal = 0;
  let found = 0;
  let firstSolution = null;
  let nodes = 0;
  let aborted = false;

  function updateClues(r, c, v) {
    let ok = true;
    const list = clueNeighborsOf[r * size + c];
    for (let i = 0; i < list.length; i++) {
      const q = list[i];
      clueAssigned[q]++;
      cluePartial[q] += v;
      if (cluePartial[q] > clueTargets[q]) ok = false;
      if (cluePartial[q] + 4 * (clueTotalN[q] - clueAssigned[q]) < clueTargets[q]) ok = false;
    }
    return ok;
  }

  function revertClues(r, c, v) {
    const list = clueNeighborsOf[r * size + c];
    for (let i = 0; i < list.length; i++) {
      const q = list[i];
      clueAssigned[q]--;
      cluePartial[q] -= v;
    }
  }

  function search(r, c) {
    if (r === size) {
      for (let i = 0; i < size; i++) if (colUsed[i] !== colCounts[i]) return false;
      for (let t = 1; t <= 4; t++) if (typeUsed[t] !== typeCounts[t]) return false;
      found++;
      if (firstSolution === null) firstSolution = grid.map(row => row.slice());
      return found >= limit;
    }
    if (c === size) {
      if (rowUsed[r] !== rowCounts[r]) return false;
      return search(r + 1, 0);
    }
    if (locked[r][c]) return search(r, c + 1);

    for (let v = 0; v <= 4; v++) {
      nodes++;
      if (nodeBudget && nodes > nodeBudget) { aborted = true; return true; }
      if (v > 0) {
        if (rowUsed[r] >= rowCounts[r]) break;
        if (colUsed[c] >= colCounts[c]) break;
        if (isAdjacentToAnyCreature(grid, r, c)) break;
        if (typeUsed[v] >= typeCounts[v]) continue;
      }
      grid[r][c] = v;
      if (v > 0) { rowUsed[r]++; colUsed[c]++; typeUsed[v]++; placedTotal++; }
      const cluesOk = updateClues(r, c, v);
      const feasible =
        rowUsed[r] + rowCapAfter[r][c + 1] >= rowCounts[r] &&
        colUsed[c] + colCapAfter[r + 1][c] >= colCounts[c] &&
        placedTotal + globalCapAfter[r * size + c + 1] >= totalNeeded;
      let stop = false;
      if (cluesOk && feasible) stop = search(r, c + 1);
      revertClues(r, c, v);
      grid[r][c] = 0;
      if (v > 0) { rowUsed[r]--; colUsed[c]--; typeUsed[v]--; placedTotal--; }
      if (stop) return true;
    }
    return false;
  }

  search(0, 0);
  return { count: found, solution: firstSolution, aborted };
}

/* ===================== Generator ===================== */

// Per-check cap on solver search nodes during generation (~tens of ms each):
// keeps the worst 10x10 uniqueness proofs from freezing the page.
const SOLVER_NODE_BUDGET = 300000;

function shuffleInPlace(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    const tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
  }
  return arr;
}

function computeNeighborSum(grid, row, col) {
  let sum = 0;
  for (let dr = -1; dr <= 1; dr++) {
    for (let dc = -1; dc <= 1; dc++) {
      if (dr === 0 && dc === 0) continue;
      const r = row + dr, c = col + dc;
      if (r < 0 || c < 0 || r >= grid.length || c >= grid[0].length) continue;
      if (grid[r][c] > 0) sum += grid[r][c]; // > 0: user marks are stored as -1
    }
  }
  return sum;
}

// Builds a random solution grid: creatures placed one at a time in random
// legal cells. Returns null if it keeps getting stuck.
function buildRandomSolution(size, typeCounts) {
  const types = [];
  for (let t = 1; t <= 4; t++) {
    for (let k = 0; k < typeCounts[t]; k++) types.push(t);
  }
  for (let attempt = 0; attempt < 200; attempt++) {
    shuffleInPlace(types);
    const grid = [];
    for (let r = 0; r < size; r++) grid.push(new Array(size).fill(0));
    let placedAll = true;
    for (const t of types) {
      const legal = [];
      for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
          if (grid[r][c] === 0 && !isAdjacentToAnyCreature(grid, r, c)) legal.push([r, c]);
        }
      }
      if (legal.length === 0) { placedAll = false; break; }
      const pick = legal[Math.floor(Math.random() * legal.length)];
      grid[pick[0]][pick[1]] = t;
    }
    if (placedAll) return grid;
  }
  return null;
}

// Random creature mix: every type appears at least once, the rest of the
// animals are distributed at random.
function randomTypeCounts(totalAnimals) {
  const counts = { 1: 1, 2: 1, 3: 1, 4: 1 };
  for (let i = 4; i < totalAnimals; i++) {
    counts[1 + Math.floor(Math.random() * 4)]++;
  }
  return counts;
}

// Generates a puzzle with a guaranteed unique solution: random solution,
// then a few flower cells (blocked, no sum), then reveal cell clues one at a
// time until the solver confirms uniqueness. Restarts from scratch if all
// clues revealed and still not unique.
function generatePuzzle(difficulty) {
  const config = DIFFICULTIES[difficulty];
  const size = config.size;
  let restarts = 0;
  while (true) {
    const typeCounts = randomTypeCounts(config.animals);
    const solution = buildRandomSolution(size, typeCounts);
    if (solution !== null) {
      const rowCounts = new Array(size).fill(0);
      const colCounts = new Array(size).fill(0);
      const emptyCells = [];
      for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
          if (solution[r][c] > 0) {
            rowCounts[r]++;
            colCounts[c]++;
          } else {
            emptyCells.push({ row: r, col: c, sum: computeNeighborSum(solution, r, c) });
          }
        }
      }
      shuffleInPlace(emptyCells);
      const flowerCells = {};
      for (const cell of emptyCells.splice(0, config.flowers)) {
        flowerCells[cell.row + ',' + cell.col] = true;
      }
      const clueCells = {};
      const candidate = { size, clueCells, flowerCells, rowCounts, colCounts, typeCounts };
      // A budget-aborted check is treated as "not unique yet" (reveal another
      // clue); uniqueness is only ever declared by a completed search.
      let check = countSolutions(candidate, 2, SOLVER_NODE_BUDGET);
      let unique = check.count === 1 && !check.aborted;
      for (let i = 0; !unique && i < emptyCells.length; i++) {
        const cell = emptyCells[i];
        clueCells[cell.row + ',' + cell.col] = cell.sum;
        check = countSolutions(candidate, 2, SOLVER_NODE_BUDGET);
        unique = check.count === 1 && !check.aborted;
      }
      if (unique) return { size, solution, clueCells, flowerCells, rowCounts, colCounts, typeCounts };
    }
    restarts++;
    if (restarts > 20) console.warn('Horned Garden generator: restart #' + restarts);
  }
}

/* ===================== Console tests ===================== */

function testSolver() {
  const puzzle = {
    size: 5,
    rowCounts: [2, 0, 1, 0, 2],
    colCounts: [2, 0, 1, 0, 2],
    typeCounts: { 1: 2, 2: 1, 3: 1, 4: 1 },
    clueCells: { '0,1': 1, '0,3': 2, '2,0': 0, '2,4': 0, '4,1': 4, '4,3': 1 },
  };
  const expected = [
    [1, 0, 0, 0, 2],
    [0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0],
    [0, 0, 0, 0, 0],
    [4, 0, 0, 0, 1],
  ];
  const result = countSolutions(puzzle, 2);
  console.log('Solved grid:');
  for (const row of result.solution) console.log(row.join(' '));
  const matches = JSON.stringify(result.solution) === JSON.stringify(expected);
  console.log('unique:', result.count === 1, '| matches expected solution:', matches);
  return result;
}

function testGenerate(difficulty) {
  const d = difficulty || 'easy';
  const t0 = performance.now();
  const p = generatePuzzle(d);
  const ms = Math.round(performance.now() - t0);
  const check = countSolutions(p, 2);
  console.log('generated "' + d + '" in ' + ms + 'ms — ' +
    Object.keys(p.clueCells).length + ' clue cells, ' +
    Object.keys(p.flowerCells).length + ' flowers, unique: ' + (check.count === 1));
  console.log(p);
  return p;
}

if (typeof window !== 'undefined') {
  window.testSolver = testSolver;
  window.testGenerate = testGenerate;
  window.HG = { countSolutions, generatePuzzle };
}

/* ===================== UI ===================== */

const TYPE_COLORS = { 1: '#6fa055', 2: '#4e8f89', 3: '#946cab', 4: '#cd9143' };

function creatureIcon(type) {
  const color = TYPE_COLORS[type];
  const cx = 20, cy = 23, r = 12;
  const angles = [];
  if (type === 1) {
    angles.push(0);
  } else {
    for (let i = 0; i < type; i++) angles.push(-55 + i * (110 / (type - 1)));
  }
  let horns = '';
  for (const aDeg of angles) {
    const a = (aDeg - 90) * Math.PI / 180;
    const a1 = a - 0.17, a2 = a + 0.17;
    const bx1 = cx + Math.cos(a1) * (r - 1), by1 = cy + Math.sin(a1) * (r - 1);
    const bx2 = cx + Math.cos(a2) * (r - 1), by2 = cy + Math.sin(a2) * (r - 1);
    const tx = cx + Math.cos(a) * (r + 9), ty = cy + Math.sin(a) * (r + 9);
    horns += '<polygon points="' + bx1.toFixed(1) + ',' + by1.toFixed(1) + ' ' +
      tx.toFixed(1) + ',' + ty.toFixed(1) + ' ' +
      bx2.toFixed(1) + ',' + by2.toFixed(1) + '" fill="' + color + '"/>';
  }
  return '<svg viewBox="0 0 40 40" xmlns="http://www.w3.org/2000/svg" aria-hidden="true">' +
    horns +
    '<circle cx="' + cx + '" cy="' + cy + '" r="' + r + '" fill="' + color + '"/>' +
    '<circle cx="15.5" cy="20.5" r="1.7" fill="#fff"/>' +
    '<circle cx="24.5" cy="20.5" r="1.7" fill="#fff"/>' +
    '<text x="20" y="31" text-anchor="middle" font-size="9" font-weight="700" fill="#fff">' + type + '</text>' +
    '</svg>';
}

// Small neutral horned-head silhouette for row/column headers: the count is
// shown as repeated figures, like the original game (no figures = zero).
function headerGlyphs(count) {
  const glyph = '<svg class="hglyph" viewBox="0 0 20 20" xmlns="http://www.w3.org/2000/svg" aria-hidden="true">' +
    '<polygon points="4.2,1.5 7.8,7.5 2.5,8.5"/>' +
    '<polygon points="15.8,1.5 12.2,7.5 17.5,8.5"/>' +
    '<circle cx="10" cy="13" r="6.3"/>' +
    '</svg>';
  let out = '';
  for (let i = 0; i < count; i++) out += glyph;
  return out;
}

const state = { difficulty: 'easy', selectedType: 1, status: 'generating' };
let puzzle = null;
let userGrid = null;
let cellEls = [];
let rowHeaderEls = [];
let colHeaderEls = [];
let appEl, gridEl, statusEl, bannerEl, sliderEl, resetBtn, newBtn, paletteBtns, diffLabelEls;

function init() {
  appEl = document.getElementById('app');
  gridEl = document.getElementById('grid');
  statusEl = document.getElementById('status');
  bannerEl = document.getElementById('banner');
  sliderEl = document.getElementById('difficulty');
  resetBtn = document.getElementById('reset-btn');
  newBtn = document.getElementById('new-btn');
  diffLabelEls = Array.from(document.querySelectorAll('#diff-labels span'));
  paletteBtns = Array.from(document.querySelectorAll('.pal-btn'));

  for (const btn of paletteBtns) {
    if (btn.dataset.type === 'mark') {
      btn.innerHTML = '<span class="mark-glyph">❀</span><span class="pal-count">note</span>';
      btn.addEventListener('click', () => selectType('mark'));
    } else {
      const type = Number(btn.dataset.type);
      btn.innerHTML = creatureIcon(type) + '<span class="pal-count" data-count="' + type + '">0/0</span>';
      btn.addEventListener('click', () => selectType(type));
    }
  }
  sliderEl.addEventListener('input', () => {
    const next = DIFFICULTY_ORDER[Number(sliderEl.value)];
    if (next !== state.difficulty) {
      state.difficulty = next;
      startNewPuzzle();
    }
    updateDiffLabels();
  });
  newBtn.addEventListener('click', startNewPuzzle);
  resetBtn.addEventListener('click', resetPuzzle);
  const helpBtn = document.getElementById('help-btn');
  const rulesEl = document.getElementById('rules');
  helpBtn.addEventListener('click', () => { rulesEl.hidden = false; });
  document.getElementById('rules-close').addEventListener('click', () => { rulesEl.hidden = true; });
  rulesEl.addEventListener('click', (e) => { if (e.target === rulesEl) rulesEl.hidden = true; });
  window.addEventListener('resize', applyCellSize);

  updateDiffLabels();
  startNewPuzzle();
}

function updateDiffLabels() {
  for (let i = 0; i < diffLabelEls.length; i++) {
    diffLabelEls[i].classList.toggle('active', i === Number(sliderEl.value));
  }
}

function selectType(type) {
  if (state.status !== 'playing') return;
  state.selectedType = type;
  for (const btn of paletteBtns) {
    btn.classList.toggle('selected', btn.dataset.type === String(type));
  }
}

function startNewPuzzle() {
  state.status = 'generating';
  appEl.classList.add('generating');
  appEl.classList.remove('solved');
  statusEl.hidden = false;
  bannerEl.hidden = true;
  sliderEl.disabled = true;
  gridEl.innerHTML = '';
  setTimeout(() => {
    puzzle = generatePuzzle(state.difficulty);
    userGrid = [];
    for (let r = 0; r < puzzle.size; r++) userGrid.push(new Array(puzzle.size).fill(0));
    state.status = 'playing';
    appEl.classList.remove('generating');
    statusEl.hidden = true;
    sliderEl.disabled = false;
    buildBoard();
    selectType(state.selectedType);
    updateFeedback();
  }, 30);
}

function applyCellSize() {
  if (!puzzle) return;
  // Fit the board in both directions: the app is a single screen with no
  // scroll, so subtract the fixed chrome (header, slider, palette, actions).
  const availW = Math.min(window.innerWidth, 560) - 48;
  const availH = Math.max(window.innerHeight - 300, 180);
  const per = Math.min(availW, availH) / (puzzle.size + 1);
  const cell = Math.max(24, Math.min(52, Math.floor(per) - 3));
  gridEl.style.setProperty('--cell', cell + 'px');
}

function buildBoard() {
  const size = puzzle.size;
  applyCellSize();
  gridEl.innerHTML = '';
  gridEl.style.gridTemplateColumns = 'repeat(' + (size + 1) + ', var(--cell))';
  cellEls = [];
  rowHeaderEls = [];
  colHeaderEls = [];

  const corner = document.createElement('div');
  corner.className = 'corner';
  gridEl.appendChild(corner);
  for (let c = 0; c < size; c++) {
    const h = document.createElement('div');
    h.className = 'col-header';
    h.innerHTML = headerGlyphs(puzzle.colCounts[c]);
    colHeaderEls.push(h);
    gridEl.appendChild(h);
  }
  for (let r = 0; r < size; r++) {
    const h = document.createElement('div');
    h.className = 'row-header';
    h.innerHTML = headerGlyphs(puzzle.rowCounts[r]);
    rowHeaderEls.push(h);
    gridEl.appendChild(h);
    const rowEls = [];
    for (let c = 0; c < size; c++) {
      const cell = document.createElement('button');
      cell.type = 'button';
      const key = r + ',' + c;
      if (key in puzzle.clueCells) {
        cell.className = 'cell clue';
        cell.textContent = puzzle.clueCells[key];
        cell.tabIndex = -1;
      } else if (key in puzzle.flowerCells) {
        cell.className = 'cell flower';
        cell.textContent = '❀';
        cell.tabIndex = -1;
      } else {
        cell.className = 'cell';
        cell.addEventListener('click', handleCellClick.bind(null, r, c));
      }
      rowEls.push(cell);
      gridEl.appendChild(cell);
    }
    cellEls.push(rowEls);
  }
}

function handleCellClick(r, c) {
  if (state.status !== 'playing') return;
  const cell = cellEls[r][c];
  const current = userGrid[r][c];
  if (state.selectedType === 'mark') {
    // Dark-flower note: "no creature here". Free to place anywhere, ignored
    // by every rule check.
    userGrid[r][c] = current === -1 ? 0 : -1;
  } else if (current === state.selectedType) {
    userGrid[r][c] = 0;
  } else if (current <= 0 && isAdjacentToAnyCreature(userGrid, r, c)) {
    cell.classList.remove('flash');
    void cell.offsetWidth;
    cell.classList.add('flash');
    return;
  } else {
    userGrid[r][c] = state.selectedType;
  }
  renderCell(r, c);
  updateFeedback();
  if (isBoardSolved()) showSolved();
}

function renderCell(r, c) {
  const v = userGrid[r][c];
  if (v === 0) cellEls[r][c].innerHTML = '';
  else if (v === -1) cellEls[r][c].innerHTML = '<span class="mark">❀</span>';
  else cellEls[r][c].innerHTML = creatureIcon(v);
}

function updateFeedback() {
  const size = puzzle.size;
  const rowUsed = new Array(size).fill(0);
  const colUsed = new Array(size).fill(0);
  const typeUsed = [0, 0, 0, 0, 0];
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      const v = userGrid[r][c];
      if (v > 0) { rowUsed[r]++; colUsed[c]++; typeUsed[v]++; }
    }
  }
  for (let r = 0; r < size; r++) {
    const over = rowUsed[r] > puzzle.rowCounts[r];
    rowHeaderEls[r].classList.toggle('ok', rowUsed[r] === puzzle.rowCounts[r]);
    rowHeaderEls[r].classList.toggle('over', over);
    // A zero row shows no figures, so an overcount there needs an explicit mark.
    if (puzzle.rowCounts[r] === 0) rowHeaderEls[r].textContent = over ? '✕' : '';
  }
  for (let c = 0; c < size; c++) {
    const over = colUsed[c] > puzzle.colCounts[c];
    colHeaderEls[c].classList.toggle('ok', colUsed[c] === puzzle.colCounts[c]);
    colHeaderEls[c].classList.toggle('over', over);
    if (puzzle.colCounts[c] === 0) colHeaderEls[c].textContent = over ? '✕' : '';
  }
  for (let t = 1; t <= 4; t++) {
    const el = document.querySelector('[data-count="' + t + '"]');
    el.textContent = typeUsed[t] + '/' + puzzle.typeCounts[t];
    el.classList.toggle('over', typeUsed[t] > puzzle.typeCounts[t]);
  }
  for (const key of Object.keys(puzzle.clueCells)) {
    const parts = key.split(',');
    const r = Number(parts[0]), c = Number(parts[1]);
    const sum = computeNeighborSum(userGrid, r, c);
    cellEls[r][c].classList.toggle('over', sum > puzzle.clueCells[key]);
  }
}

function isBoardSolved() {
  const size = puzzle.size;
  const rowUsed = new Array(size).fill(0);
  const colUsed = new Array(size).fill(0);
  const typeUsed = [0, 0, 0, 0, 0];
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      const v = userGrid[r][c];
      if (v > 0) { rowUsed[r]++; colUsed[c]++; typeUsed[v]++; }
    }
  }
  for (let r = 0; r < size; r++) if (rowUsed[r] !== puzzle.rowCounts[r]) return false;
  for (let c = 0; c < size; c++) if (colUsed[c] !== puzzle.colCounts[c]) return false;
  for (let t = 1; t <= 4; t++) if (typeUsed[t] !== puzzle.typeCounts[t]) return false;
  for (const key of Object.keys(puzzle.clueCells)) {
    const parts = key.split(',');
    if (computeNeighborSum(userGrid, Number(parts[0]), Number(parts[1])) !== puzzle.clueCells[key]) return false;
  }
  return true;
}

function showSolved() {
  state.status = 'solved';
  appEl.classList.add('solved');
  bannerEl.hidden = false;
}

function resetPuzzle() {
  if (!puzzle || state.status === 'generating') return;
  for (let r = 0; r < puzzle.size; r++) {
    for (let c = 0; c < puzzle.size; c++) {
      if (userGrid[r][c] !== 0) {
        userGrid[r][c] = 0;
        cellEls[r][c].innerHTML = '';
      }
    }
  }
  bannerEl.hidden = true;
  appEl.classList.remove('solved');
  state.status = 'playing';
  updateFeedback();
}

if (typeof window !== 'undefined') {
  window.HG.debug = () => ({ puzzle, userGrid, state });
}

function isCapacitorNative() {
  return !!(window.Capacitor && window.Capacitor.isNativePlatform && window.Capacitor.isNativePlatform());
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', () => {
    if (isCapacitorNative()) document.body.classList.add('capacitor');
    init();
  });
}
