import './style.css';

const PIECES = {
  K: '♔', Q: '♕', R: '♖', B: '♗', N: '♘', P: '♙',
  k: '♚', q: '♛', r: '♜', b: '♝', n: '♞', p: '♟',
};
const PIECE_NAMES = { K: 'king', Q: 'queen', R: 'rook', B: 'bishop', N: 'knight', P: 'pawn' };
const PROMOTIONS = [
  ['q', '♕', 'Queen'],
  ['r', '♖', 'Rook'],
  ['b', '♗', 'Bishop'],
  ['n', '♘', 'Knight'],
];

const boardElement = document.querySelector('#board');
const statusElement = document.querySelector('#statusText');
const historyElement = document.querySelector('#moveHistory');
const moveCountElement = document.querySelector('#moveCount');
const pulseElement = document.querySelector('#enginePulse');
const promotionDialog = document.querySelector('#promotionDialog');
const promotionChoices = document.querySelector('#promotionChoices');
const thinkTime = document.querySelector('#thinkTime');

const worker = new Worker(new URL('./engine-worker.js', import.meta.url), { type: 'module' });
const pending = new Map();
let requestId = 0;
let state = null;
let moves = [];
let moveLabels = [];
let selected = null;
let flipped = false;
let busy = true;
let lastMove = null;
let errorMessage = '';

worker.onmessage = ({ data }) => {
  const request = pending.get(data.id);
  if (!request) return;
  pending.delete(data.id);
  if (data.error) request.reject(new Error(data.error));
  else request.resolve(data.result);
};

function engineRequest(action, extra = {}) {
  const id = ++requestId;
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
    worker.postMessage({ id, action, moves, ...extra });
  });
}

function parseFen(fen) {
  const board = {};
  const ranks = fen.split(' ')[0].split('/');
  for (let row = 0; row < 8; row += 1) {
    let file = 0;
    for (const token of ranks[row]) {
      if (/\d/.test(token)) file += Number(token);
      else {
        board[`${String.fromCharCode(97 + file)}${8 - row}`] = token;
        file += 1;
      }
    }
  }
  return board;
}

function squareOrder() {
  const files = flipped ? 'hgfedcba' : 'abcdefgh';
  const ranks = flipped ? '12345678' : '87654321';
  return [...ranks].flatMap((rank) => [...files].map((file) => `${file}${rank}`));
}

function setBusy(value) {
  busy = value;
  boardElement.classList.toggle('locked', value);
  pulseElement.hidden = !value;
  document.querySelector('#newGame').disabled = value;
}

function statusText() {
  if (errorMessage) return errorMessage;
  if (!state) return 'Loading engine…';
  if (state.status === 'checkmate') return state.side === 'w' ? 'Checkmate · Warhorse wins' : 'Checkmate · You win';
  if (state.status === 'stalemate') return 'Stalemate · Draw';
  if (state.status === 'draw') return 'Draw';
  if (busy) return 'Warhorse is calculating';
  if (state.status === 'check') return state.side === 'w' ? 'Check · Your move' : 'Warhorse is in check';
  return state.side === 'w' ? 'Your move' : 'Warhorse to move';
}

function renderBoard() {
  if (!state) return;
  const board = parseFen(state.fen);
  const legalTargets = selected
    ? new Set(state.legal.filter((move) => move.startsWith(selected)).map((move) => move.slice(2, 4)))
    : new Set();
  boardElement.replaceChildren();
  for (const coordinate of squareOrder()) {
    const fileIndex = coordinate.charCodeAt(0) - 97;
    const rankIndex = Number(coordinate[1]) - 1;
    const piece = board[coordinate];
    const square = document.createElement('button');
    square.type = 'button';
    square.className = `square ${(fileIndex + rankIndex) % 2 ? 'light-square' : 'dark-square'}`;
    square.dataset.square = coordinate;
    square.setAttribute('role', 'gridcell');
    square.setAttribute('aria-label', piece ? `${coordinate}, ${piece === piece.toUpperCase() ? 'white' : 'black'} ${PIECE_NAMES[piece.toUpperCase()]}` : coordinate);
    if (coordinate === selected) square.classList.add('selected');
    if (lastMove?.includes(coordinate)) square.classList.add('last-move');
    if (legalTargets.has(coordinate)) square.classList.add(piece ? 'capture-target' : 'move-target');
    if (piece) {
      const glyph = document.createElement('span');
      glyph.className = `piece ${piece === piece.toUpperCase() ? 'white-piece' : 'black-piece'}`;
      glyph.textContent = PIECES[piece];
      square.append(glyph);
    }
    if ((!flipped && coordinate[0] === 'a') || (flipped && coordinate[0] === 'h')) square.dataset.rank = coordinate[1];
    if ((!flipped && coordinate[1] === '1') || (flipped && coordinate[1] === '8')) square.dataset.file = coordinate[0];
    square.addEventListener('click', () => selectSquare(coordinate));
    boardElement.append(square);
  }
}

function renderHistory() {
  moveCountElement.textContent = `${moves.length} ${moves.length === 1 ? 'move' : 'moves'}`;
  if (!moveLabels.length) {
    historyElement.innerHTML = '<p class="history-empty">Your game will appear here.</p>';
    return;
  }
  historyElement.replaceChildren();
  for (let index = 0; index < moveLabels.length; index += 2) {
    const row = document.createElement('div');
    row.className = 'move-row';
    row.innerHTML = `<span>${index / 2 + 1}.</span><strong>${moveLabels[index]}</strong><strong>${moveLabels[index + 1] || ''}</strong>`;
    historyElement.append(row);
  }
  historyElement.scrollTop = historyElement.scrollHeight;
}

function render() {
  renderBoard();
  renderHistory();
  statusElement.textContent = statusText();
  statusElement.dataset.state = state?.status || 'loading';
}

function notation(uci, fen, result) {
  const board = parseFen(fen);
  const from = uci.slice(0, 2);
  const to = uci.slice(2, 4);
  const piece = board[from];
  if (piece?.toUpperCase() === 'K' && Math.abs(from.charCodeAt(0) - to.charCodeAt(0)) === 2) {
    return to[0] === 'g' ? 'O-O' : 'O-O-O';
  }
  const capture = Boolean(board[to]) || (piece?.toUpperCase() === 'P' && from[0] !== to[0]);
  const prefix = piece?.toUpperCase() === 'P' ? (capture ? from[0] : '') : piece?.toUpperCase() || '';
  const promotion = uci[4] ? `=${uci[4].toUpperCase()}` : '';
  const suffix = result.status === 'checkmate' ? '#' : result.inCheck ? '+' : '';
  return `${prefix}${capture ? '×' : ''}${to}${promotion}${suffix}`;
}

function choosePromotion(candidates) {
  return new Promise((resolve) => {
    promotionDialog.returnValue = 'cancel';
    promotionChoices.replaceChildren();
    for (const [suffix, glyph, name] of PROMOTIONS) {
      if (!candidates.some((move) => move.endsWith(suffix))) continue;
      const button = document.createElement('button');
      button.type = 'submit';
      button.value = suffix;
      button.setAttribute('aria-label', name);
      button.innerHTML = `<span>${glyph}</span><small>${name}</small>`;
      promotionChoices.append(button);
    }
    promotionDialog.addEventListener('close', () => resolve(promotionDialog.returnValue), { once: true });
    promotionDialog.showModal();
  });
}

async function playMove(candidates) {
  let uci = candidates[0];
  if (candidates.length > 1) {
    const promotion = await choosePromotion(candidates);
    if (promotion === 'cancel') return;
    uci = candidates.find((move) => move.endsWith(promotion));
    if (!uci) return;
  }
  const before = state.fen;
  errorMessage = '';
  setBusy(true);
  selected = null;
  render();
  try {
    const playerResult = await engineRequest('play', { move: uci });
    moves.push(uci);
    moveLabels.push(notation(uci, before, playerResult));
    lastMove = uci;
    state = playerResult;
    render();
    if (['checkmate', 'stalemate', 'draw'].includes(state.status)) return;

    const engineBefore = state.fen;
    const engineResult = await engineRequest('engine', { thinkTime: Number(thinkTime.value) });
    if (engineResult.engineMove) {
      moves.push(engineResult.engineMove);
      moveLabels.push(notation(engineResult.engineMove, engineBefore, engineResult));
      lastMove = engineResult.engineMove;
    }
    state = engineResult;
  } catch (error) {
    errorMessage = `Engine error: ${error.message}`;
  } finally {
    setBusy(false);
    render();
  }
}

function selectSquare(coordinate) {
  if (busy || !state || state.side !== 'w' || ['checkmate', 'stalemate', 'draw'].includes(state.status)) return;
  if (selected) {
    const candidates = state.legal.filter((move) => move.startsWith(selected + coordinate));
    if (candidates.length) {
      playMove(candidates);
      return;
    }
  }
  const board = parseFen(state.fen);
  selected = board[coordinate]?.toUpperCase() === board[coordinate] && state.legal.some((move) => move.startsWith(coordinate))
    ? coordinate
    : null;
  renderBoard();
}

async function newGame() {
  setBusy(true);
  moves = [];
  moveLabels = [];
  selected = null;
  lastMove = null;
  errorMessage = '';
  try {
    state = await engineRequest('state');
  } catch (error) {
    errorMessage = `Engine failed to load: ${error.message}`;
  } finally {
    setBusy(false);
    render();
  }
}

document.querySelector('#newGame').addEventListener('click', newGame);
document.querySelector('#flipBoard').addEventListener('click', () => {
  flipped = !flipped;
  renderBoard();
});

newGame();
