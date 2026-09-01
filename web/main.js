import './style.css';

const PIECES = {
  K: '♔', Q: '♕', R: '♖', B: '♗', N: '♘', P: '♙',
  k: '♚', q: '♛', r: '♜', b: '♝', n: '♞', p: '♟',
};
const PIECE_NAMES = { K: 'king', Q: 'queen', R: 'rook', B: 'bishop', N: 'knight', P: 'pawn' };
const PIECE_VALUES = { Q: 9, R: 5, B: 3, N: 3, P: 1 };
const PROMOTIONS = [
  ['q', 'Queen'],
  ['r', 'Rook'],
  ['b', 'Bishop'],
  ['n', 'Knight'],
];
const TERMINAL_STATES = new Set(['checkmate', 'stalemate', 'draw']);

const elements = {
  modeScreen: document.querySelector('#modeScreen'),
  gameScreen: document.querySelector('#gameScreen'),
  modeTitle: document.querySelector('#modeTitle'),
  board: document.querySelector('#board'),
  status: document.querySelector('#statusText'),
  turnHeading: document.querySelector('#turnHeading'),
  history: document.querySelector('#moveHistory'),
  moveCount: document.querySelector('#moveCount'),
  pulse: document.querySelector('#enginePulse'),
  promotionDialog: document.querySelector('#promotionDialog'),
  promotionChoices: document.querySelector('#promotionChoices'),
  thinkTime: document.querySelector('#thinkTime'),
  engineCard: document.querySelector('#engineCard'),
  engineSettings: document.querySelector('#engineSettings'),
  engineStatus: document.querySelector('#engineStatus'),
  modeLabel: document.querySelector('#modeLabel'),
  turnToast: document.querySelector('#turnToast'),
  topName: document.querySelector('#topName'),
  topRole: document.querySelector('#topRole'),
  topAvatar: document.querySelector('#topAvatar'),
  bottomName: document.querySelector('#bottomName'),
  bottomRole: document.querySelector('#bottomRole'),
  bottomAvatar: document.querySelector('#bottomAvatar'),
  capturedByWhite: document.querySelector('#capturedByWhite'),
  capturedByBlack: document.querySelector('#capturedByBlack'),
  capturedByWhiteRow: document.querySelector('#capturedByWhiteRow'),
  capturedByBlackRow: document.querySelector('#capturedByBlackRow'),
  materialAdvantage: document.querySelector('#materialAdvantage'),
  lastCapture: document.querySelector('#lastCapture'),
  restart: document.querySelector('#restartGame'),
  flip: document.querySelector('#flipBoard'),
  resign: document.querySelector('#resignGame'),
  newGame: document.querySelector('#newGame'),
};

const pending = new Map();
let worker;
let requestId = 0;
let gameId = 0;
let mode = null;
let state = null;
let moves = [];
let moveLabels = [];
let moveCaptures = [];
let captured = { w: [], b: [] };
let selected = null;
let flipped = false;
let busy = false;
let thinking = false;
let lastMove = null;
let errorMessage = '';
let outcome = null;
let toastTimer = null;
let captureTimer = null;

function createWorker() {
  const nextWorker = new Worker(new URL('./engine-worker.js', import.meta.url), { type: 'module' });
  worker = nextWorker;
  nextWorker.onmessage = ({ data }) => {
    const request = pending.get(data.id);
    if (!request) return;
    pending.delete(data.id);
    if (data.error) {
      if (worker === nextWorker) {
        nextWorker.terminate();
        worker = null;
      }
      request.reject(new Error(data.error));
      for (const otherRequest of pending.values()) otherRequest.reject(new Error(data.error));
      pending.clear();
    } else request.resolve(data.result);
  };
  nextWorker.onerror = (event) => {
    event.preventDefault();
    if (worker !== nextWorker) return;
    worker = null;
    const message = event.message || 'The local engine worker stopped unexpectedly';
    for (const request of pending.values()) request.reject(new Error(message));
    pending.clear();
  };
}

function replaceWorker() {
  worker?.terminate();
  worker = null;
  for (const request of pending.values()) request.reject(new Error('Request cancelled'));
  pending.clear();
}

function engineRequest(action, extra = {}) {
  if (!worker) createWorker();
  const id = ++requestId;
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
    try {
      worker.postMessage({ id, action, moves: [...moves], ...extra });
    } catch (error) {
      pending.delete(id);
      reject(error);
    }
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

function sideName(side) {
  return side === 'w' ? 'White' : 'Black';
}

function playerName(side) {
  if (mode === 'engine') return side === 'w' ? 'You' : 'Warhorse';
  return side === 'w' ? 'Player 1' : 'Player 2';
}

function isTerminal() {
  return Boolean(outcome || (state && TERMINAL_STATES.has(state.status)));
}

function setBusy(value, engineThinking = false) {
  busy = value;
  thinking = value && engineThinking;
  elements.board.classList.toggle('locked', value || isTerminal());
  elements.pulse.hidden = !thinking;
  for (const control of [elements.restart, elements.resign, elements.newGame]) control.disabled = value;
}

function statusCopy() {
  if (errorMessage) return { heading: 'Engine unavailable', detail: errorMessage, key: 'error' };
  if (!state) return { heading: 'Setting the pieces', detail: 'Preparing the board…', key: 'loading' };
  if (outcome?.type === 'resignation') {
    return {
      heading: `${sideName(outcome.winner)} wins`,
      detail: `${playerName(outcome.loser)} resigned`,
      key: 'resignation',
    };
  }
  if (state.status === 'checkmate') {
    const winner = state.side === 'w' ? 'b' : 'w';
    return { heading: 'Checkmate', detail: `${playerName(winner)} wins as ${sideName(winner)}`, key: 'checkmate' };
  }
  if (state.status === 'stalemate') return { heading: 'Stalemate', detail: 'The game is drawn', key: 'stalemate' };
  if (state.status === 'draw') return { heading: 'Draw', detail: 'The game has ended', key: 'draw' };
  if (thinking) return { heading: 'Warhorse thinking', detail: 'Calculating a reply…', key: 'thinking' };

  const side = sideName(state.side);
  const player = playerName(state.side);
  if (state.status === 'check') return { heading: `${side} in check`, detail: `${player} to move`, key: 'check' };
  if (mode === 'engine') return { heading: state.side === 'w' ? 'Your turn' : 'Warhorse to move', detail: `${side} to move`, key: state.side };
  return { heading: `${side} to move`, detail: player, key: state.side };
}

function playerDetails(side) {
  if (mode === 'engine') {
    return side === 'w'
      ? { name: 'You', role: 'White', avatar: 'Y' }
      : { name: 'Warhorse', role: 'Black · Rust engine', avatar: 'W' };
  }
  return side === 'w'
    ? { name: 'Player 1', role: 'White', avatar: '1' }
    : { name: 'Player 2', role: 'Black', avatar: '2' };
}

function renderCaptured(element, side) {
  element.replaceChildren();
  if (!captured[side].length) {
    element.textContent = '—';
    return;
  }
  for (const piece of captured[side]) {
    const glyph = document.createElement('span');
    glyph.textContent = PIECES[piece];
    glyph.title = `${piece === piece.toUpperCase() ? 'White' : 'Black'} ${PIECE_NAMES[piece.toUpperCase()]}`;
    element.append(glyph);
  }
}

function renderMaterial() {
  renderCaptured(elements.capturedByWhite, 'w');
  renderCaptured(elements.capturedByBlack, 'b');
  if (!state) {
    elements.materialAdvantage.textContent = 'Material even';
    return;
  }
  const balance = Object.values(parseFen(state.fen)).reduce((total, piece) => {
    const value = PIECE_VALUES[piece.toUpperCase()] || 0;
    return total + (piece === piece.toUpperCase() ? value : -value);
  }, 0);
  elements.materialAdvantage.textContent = balance === 0
    ? 'Material even'
    : `${balance > 0 ? 'White' : 'Black'} +${Math.abs(balance)}`;
}

function renderPlayers() {
  const topSide = flipped ? 'w' : 'b';
  const bottomSide = flipped ? 'b' : 'w';
  const top = playerDetails(topSide);
  const bottom = playerDetails(bottomSide);

  elements.topName.textContent = top.name;
  elements.topRole.textContent = top.role;
  elements.topAvatar.textContent = top.avatar;
  elements.topAvatar.className = `player-avatar ${topSide === 'w' ? 'light' : 'dark'}`;
  elements.bottomName.textContent = bottom.name;
  elements.bottomRole.textContent = bottom.role;
  elements.bottomAvatar.textContent = bottom.avatar;
  elements.bottomAvatar.className = `player-avatar ${bottomSide === 'w' ? 'light' : 'dark'}`;
  const topRow = document.querySelector('#topPlayer');
  const bottomRow = document.querySelector('#bottomPlayer');
  (topSide === 'b' ? topRow : bottomRow).append(elements.pulse);
  topRow.classList.toggle('active-player', state?.side === topSide && !isTerminal());
  bottomRow.classList.toggle('active-player', state?.side === bottomSide && !isTerminal());
}

function renderBoard() {
  if (!state) return;
  const focusedSquare = document.activeElement?.dataset.square || selected;
  const order = squareOrder();
  const board = parseFen(state.fen);
  const selectedPiece = selected ? board[selected] : null;
  const legalTargets = selected
    ? new Set(state.legal.filter((move) => move.startsWith(selected)).map((move) => move.slice(2, 4)))
    : new Set();
  const checkedKing = state.inCheck
    ? Object.keys(board).find((coordinate) => board[coordinate] === (state.side === 'w' ? 'K' : 'k'))
    : null;

  elements.board.replaceChildren();
  elements.board.classList.toggle('game-over', isTerminal());
  for (const coordinate of order) {
    const fileIndex = coordinate.charCodeAt(0) - 97;
    const rankIndex = Number(coordinate[1]) - 1;
    const piece = board[coordinate];
    const square = document.createElement('button');
    square.type = 'button';
    square.className = `square ${(fileIndex + rankIndex) % 2 ? 'light-square' : 'dark-square'}`;
    square.dataset.square = coordinate;
    square.tabIndex = coordinate === (focusedSquare || order[0]) ? 0 : -1;
    square.setAttribute('role', 'gridcell');
    square.setAttribute('aria-label', piece ? `${coordinate}, ${piece === piece.toUpperCase() ? 'white' : 'black'} ${PIECE_NAMES[piece.toUpperCase()]}` : coordinate);
    if (coordinate === selected) square.classList.add('selected');
    if (lastMove?.slice(0, 4).includes(coordinate)) square.classList.add('last-move');
    if (coordinate === checkedKing) square.classList.add(state.status === 'checkmate' ? 'checkmate' : 'in-check');
    if (legalTargets.has(coordinate)) {
      const enPassant = selectedPiece?.toUpperCase() === 'P' && selected?.[0] !== coordinate[0];
      square.classList.add(piece || enPassant ? 'capture-target' : 'move-target');
    }
    if (piece) {
      const glyph = document.createElement('span');
      glyph.className = `piece ${piece === piece.toUpperCase() ? 'white-piece' : 'black-piece'}`;
      glyph.textContent = PIECES[piece];
      square.append(glyph);
    }
    if ((!flipped && coordinate[0] === 'a') || (flipped && coordinate[0] === 'h')) square.dataset.rank = coordinate[1];
    if ((!flipped && coordinate[1] === '1') || (flipped && coordinate[1] === '8')) square.dataset.file = coordinate[0];
    square.addEventListener('click', () => selectSquare(coordinate));
    square.addEventListener('keydown', (event) => moveBoardFocus(event, coordinate));
    elements.board.append(square);
  }
  if (focusedSquare) elements.board.querySelector(`[data-square="${focusedSquare}"]`)?.focus({ preventScroll: true });
}

function moveBoardFocus(event, coordinate) {
  const offsets = { ArrowLeft: -1, ArrowRight: 1, ArrowUp: -8, ArrowDown: 8 };
  if (!(event.key in offsets)) return;
  event.preventDefault();
  const order = squareOrder();
  const index = order.indexOf(coordinate);
  const column = index % 8;
  if ((event.key === 'ArrowLeft' && column === 0) || (event.key === 'ArrowRight' && column === 7)) return;
  const target = order[index + offsets[event.key]];
  if (!target) return;
  elements.board.querySelectorAll('.square').forEach((square) => { square.tabIndex = -1; });
  const targetElement = elements.board.querySelector(`[data-square="${target}"]`);
  targetElement.tabIndex = 0;
  targetElement.focus();
}

function renderHistory() {
  elements.moveCount.textContent = `${moves.length} ${moves.length === 1 ? 'move' : 'moves'}`;
  if (!moveLabels.length) {
    elements.history.innerHTML = `<p class="history-empty">${mode === 'pass' ? 'White begins the game.' : 'The first move is yours.'}</p>`;
    return;
  }
  elements.history.replaceChildren();
  for (let index = 0; index < moveLabels.length; index += 2) {
    const row = document.createElement('div');
    row.className = 'move-row';
    const number = document.createElement('span');
    number.className = 'move-number';
    number.textContent = `${index / 2 + 1}.`;
    row.append(number);
    for (const moveIndex of [index, index + 1]) {
      const label = document.createElement('strong');
      label.className = 'move-entry';
      const notationText = document.createElement('span');
      notationText.textContent = moveLabels[moveIndex] || '';
      label.append(notationText);
      if (moveCaptures[moveIndex]) {
        const detail = document.createElement('small');
        detail.className = 'capture-detail';
        const capturedName = PIECE_NAMES[moveCaptures[moveIndex].piece.toUpperCase()];
        detail.textContent = `× ${capturedName[0].toUpperCase()}${capturedName.slice(1)}`;
        label.append(detail);
      }
      if (moveIndex === moveLabels.length - 1) label.classList.add('latest-move');
      row.append(label);
    }
    elements.history.append(row);
  }
  elements.history.scrollTop = elements.history.scrollHeight;
}

function render() {
  if (!mode) return;
  renderBoard();
  renderHistory();
  renderMaterial();
  renderPlayers();
  const copy = statusCopy();
  elements.turnHeading.textContent = copy.heading;
  elements.status.textContent = copy.detail;
  elements.status.dataset.state = copy.key;
  elements.modeLabel.textContent = mode === 'engine' ? 'VS WARHORSE' : 'PASS & PLAY';
  elements.engineCard.hidden = mode !== 'engine';
  elements.engineSettings.hidden = mode !== 'engine';
  elements.engineStatus.textContent = errorMessage ? 'OFFLINE' : thinking ? 'THINKING' : 'READY';
  elements.engineStatus.dataset.state = errorMessage ? 'error' : thinking ? 'thinking' : 'ready';
  elements.resign.disabled = busy || isTerminal();
  elements.board.classList.toggle('locked', busy || isTerminal());
}

function notation(uci, fen, result, legalMoves) {
  const board = parseFen(fen);
  const from = uci.slice(0, 2);
  const to = uci.slice(2, 4);
  const piece = board[from];
  if (piece?.toUpperCase() === 'K' && Math.abs(from.charCodeAt(0) - to.charCodeAt(0)) === 2) {
    const suffix = result.status === 'checkmate' ? '#' : result.inCheck ? '+' : '';
    return `${to[0] === 'g' ? 'O-O' : 'O-O-O'}${suffix}`;
  }
  const capture = Boolean(board[to]) || (piece?.toUpperCase() === 'P' && from[0] !== to[0]);
  const pieceType = piece?.toUpperCase();
  let disambiguation = '';
  if (pieceType && !['P', 'K'].includes(pieceType)) {
    const alternatives = legalMoves.filter((move) => {
      const otherFrom = move.slice(0, 2);
      return move !== uci && move.slice(2, 4) === to && board[otherFrom]?.toUpperCase() === pieceType;
    });
    if (alternatives.length) {
      const sharesFile = alternatives.some((move) => move[0] === from[0]);
      const sharesRank = alternatives.some((move) => move[1] === from[1]);
      disambiguation = !sharesFile ? from[0] : !sharesRank ? from[1] : from;
    }
  }
  const prefix = pieceType === 'P' ? (capture ? from[0] : '') : `${pieceType || ''}${disambiguation}`;
  const promotion = uci[4] ? `=${uci[4].toUpperCase()}` : '';
  const suffix = result.status === 'checkmate' ? '#' : result.inCheck ? '+' : '';
  return `${prefix}${capture ? 'x' : ''}${to}${promotion}${suffix}`;
}

function recordCapture(uci, fen) {
  const board = parseFen(fen);
  const from = uci.slice(0, 2);
  const to = uci.slice(2, 4);
  const mover = board[from];
  let taken = board[to];
  if (!taken && mover?.toUpperCase() === 'P' && from[0] !== to[0]) {
    taken = mover === mover.toUpperCase() ? 'p' : 'P';
  }
  if (!taken) return null;
  const capturer = mover === mover?.toUpperCase() ? 'w' : 'b';
  const capture = { capturer, piece: taken };
  captured[capturer].push(taken);
  return capture;
}

function showCaptureFeedback(capture) {
  if (!capture) return;
  const row = capture.capturer === 'w' ? elements.capturedByWhiteRow : elements.capturedByBlackRow;
  window.clearTimeout(captureTimer);
  elements.capturedByWhiteRow.classList.remove('capture-flash');
  elements.capturedByBlackRow.classList.remove('capture-flash');
  void row.offsetWidth;
  row.classList.add('capture-flash');
  elements.lastCapture.textContent = `${sideName(capture.capturer)} captured a ${sideName(capture.capturer === 'w' ? 'b' : 'w').toLowerCase()} ${PIECE_NAMES[capture.piece.toUpperCase()]}`;
  elements.lastCapture.hidden = false;
  captureTimer = window.setTimeout(() => row.classList.remove('capture-flash'), 700);
}

function choosePromotion(candidates) {
  return new Promise((resolve) => {
    const isWhite = state.side === 'w';
    elements.promotionDialog.returnValue = 'cancel';
    elements.promotionChoices.replaceChildren();
    for (const [suffix, name] of PROMOTIONS) {
      if (!candidates.some((move) => move.endsWith(suffix))) continue;
      const token = isWhite ? suffix.toUpperCase() : suffix;
      const button = document.createElement('button');
      button.type = 'submit';
      button.value = suffix;
      button.setAttribute('aria-label', name);
      const glyph = document.createElement('span');
      glyph.textContent = PIECES[token];
      const label = document.createElement('small');
      label.textContent = name;
      button.append(glyph, label);
      elements.promotionChoices.append(button);
    }
    elements.promotionDialog.addEventListener('close', () => resolve(elements.promotionDialog.returnValue), { once: true });
    elements.promotionDialog.showModal();
  });
}

function showTurnToast(side) {
  if (mode !== 'pass' || isTerminal()) return;
  window.clearTimeout(toastTimer);
  elements.turnToast.textContent = `Pass to ${sideName(side)}`;
  elements.turnToast.hidden = false;
  requestAnimationFrame(() => elements.turnToast.classList.add('visible'));
  toastTimer = window.setTimeout(() => {
    elements.turnToast.classList.remove('visible');
    window.setTimeout(() => { elements.turnToast.hidden = true; }, 180);
  }, 700);
}

async function playMove(candidates) {
  let uci = candidates[0];
  if (candidates.length > 1) {
    const promotion = await choosePromotion(candidates);
    if (promotion === 'cancel') return;
    uci = candidates.find((move) => move.endsWith(promotion));
    if (!uci) return;
  }

  const currentGame = gameId;
  const before = state.fen;
  const playerLegal = state.legal;
  let engineCapture = null;
  errorMessage = '';
  setBusy(true);
  selected = null;
  render();
  try {
    const playerResult = await engineRequest('play', { move: uci });
    if (currentGame !== gameId) return;
    const playerCapture = recordCapture(uci, before);
    moves.push(uci);
    moveLabels.push(notation(uci, before, playerResult, playerLegal));
    moveCaptures.push(playerCapture);
    lastMove = uci;
    state = playerResult;
    setBusy(false);
    render();
    showCaptureFeedback(playerCapture);

    if (TERMINAL_STATES.has(state.status) || mode === 'pass') {
      if (!TERMINAL_STATES.has(state.status)) showTurnToast(state.side);
      return;
    }

    setBusy(true, true);
    render();
    const engineBefore = state.fen;
    const engineLegal = state.legal;
    const engineResult = await engineRequest('engine', { thinkTime: Number(elements.thinkTime.value) });
    if (currentGame !== gameId) return;
    if (engineResult.engineMove) {
      engineCapture = recordCapture(engineResult.engineMove, engineBefore);
      moves.push(engineResult.engineMove);
      moveLabels.push(notation(engineResult.engineMove, engineBefore, engineResult, engineLegal));
      moveCaptures.push(engineCapture);
      lastMove = engineResult.engineMove;
    }
    state = engineResult;
  } catch (error) {
    if (currentGame === gameId) errorMessage = `The local engine could not respond: ${error.message}`;
  } finally {
    if (currentGame === gameId) {
      setBusy(false);
      render();
      showCaptureFeedback(engineCapture);
    }
  }
}

function selectSquare(coordinate) {
  if (busy || !state || isTerminal()) return;
  if (mode === 'engine' && state.side !== 'w') return;
  if (selected) {
    const candidates = state.legal.filter((move) => move.startsWith(selected + coordinate));
    if (candidates.length) {
      playMove(candidates);
      return;
    }
  }
  const board = parseFen(state.fen);
  const piece = board[coordinate];
  const ownsPiece = piece && (state.side === 'w' ? piece === piece.toUpperCase() : piece === piece.toLowerCase());
  selected = ownsPiece && state.legal.some((move) => move.startsWith(coordinate)) ? coordinate : null;
  renderBoard();
}

async function startGame(selectedMode = mode) {
  const currentGame = ++gameId;
  if (selectedMode !== mode) flipped = false;
  mode = selectedMode;
  state = null;
  moves = [];
  moveLabels = [];
  moveCaptures = [];
  captured = { w: [], b: [] };
  selected = null;
  lastMove = null;
  errorMessage = '';
  outcome = null;
  window.clearTimeout(toastTimer);
  window.clearTimeout(captureTimer);
  elements.turnToast.hidden = true;
  elements.turnToast.classList.remove('visible');
  elements.lastCapture.hidden = true;
  elements.capturedByWhiteRow.classList.remove('capture-flash');
  elements.capturedByBlackRow.classList.remove('capture-flash');
  elements.modeScreen.hidden = true;
  elements.gameScreen.hidden = false;
  window.scrollTo(0, 0);
  elements.turnHeading.focus({ preventScroll: true });
  setBusy(true);
  render();
  try {
    const initialState = await engineRequest('state');
    if (currentGame === gameId) state = initialState;
  } catch (error) {
    if (currentGame === gameId) errorMessage = `The local engine failed to load: ${error.message}`;
  } finally {
    if (currentGame === gameId) {
      setBusy(false);
      render();
      elements.board.querySelector('.square')?.focus({ preventScroll: true });
    }
  }
}

function showModeScreen() {
  gameId += 1;
  replaceWorker();
  mode = null;
  state = null;
  selected = null;
  setBusy(false);
  elements.gameScreen.hidden = true;
  elements.modeScreen.hidden = false;
  window.scrollTo(0, 0);
  elements.modeTitle.focus({ preventScroll: true });
}

function resignGame() {
  if (!state || busy || isTerminal()) return;
  const loser = mode === 'engine' ? 'w' : state.side;
  outcome = { type: 'resignation', loser, winner: loser === 'w' ? 'b' : 'w' };
  selected = null;
  render();
}

document.querySelectorAll('[data-mode]').forEach((button) => {
  button.addEventListener('click', () => startGame(button.dataset.mode));
});
document.querySelector('#brandHome').addEventListener('click', showModeScreen);
document.querySelector('#changeMode').addEventListener('click', showModeScreen);
elements.newGame.addEventListener('click', showModeScreen);
elements.restart.addEventListener('click', () => startGame(mode));
elements.resign.addEventListener('click', resignGame);
elements.flip.addEventListener('click', () => {
  flipped = !flipped;
  renderBoard();
  renderPlayers();
});

showModeScreen();
