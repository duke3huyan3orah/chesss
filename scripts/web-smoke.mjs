import { spawn } from 'node:child_process';
import { chromium } from 'playwright-core';

const server = spawn(process.execPath, ['node_modules/vite/bin/vite.js', 'preview', '--host', '127.0.0.1', '--port', '4173'], {
  stdio: ['ignore', 'pipe', 'inherit'],
});

async function waitForServer() {
  for (let attempt = 0; attempt < 50; attempt += 1) {
    try {
      const response = await fetch('http://127.0.0.1:4173');
      if (response.ok) return;
    } catch {}
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  throw new Error('Vite preview server did not start');
}

let browser;
try {
  await waitForServer();
  browser = await chromium.launch({
    executablePath: process.env.PLAYWRIGHT_BROWSER || 'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
    headless: true,
  });
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const errors = [];
  page.on('pageerror', (error) => errors.push(error.message));
  await page.addInitScript(() => {
    const BrowserWorker = window.Worker;
    window.__warhorseWorkerActions = [];
    window.Worker = class extends BrowserWorker {
      postMessage(message, transfer) {
        window.__warhorseWorkerActions.push(message.action);
        return super.postMessage(message, transfer);
      }
    };
  });
  await page.goto('http://127.0.0.1:4173', { waitUntil: 'networkidle' });
  await page.getByRole('heading', { name: 'Choose your game' }).waitFor();

  const dimensions = () => page.evaluate(() => {
    const board = document.querySelector('#board').getBoundingClientRect();
    const squares = [...document.querySelectorAll('.square')].map((square) => square.getBoundingClientRect());
    return {
      board: [board.width, board.height],
      squareCount: squares.length,
      squareWidths: [...new Set(squares.map((square) => square.width))],
      squareHeights: [...new Set(squares.map((square) => square.height))],
    };
  });
  const closeEnough = (left, right) => Math.abs(left - right) < 0.02;
  const assertStable = async (expected, label) => {
    const actual = await dimensions();
    if (actual.squareCount !== 64) throw new Error(`${label}: board does not contain 64 squares`);
    if (!closeEnough(actual.board[0], actual.board[1])) throw new Error(`${label}: board is not square`);
    if (!closeEnough(actual.board[0], expected[0]) || !closeEnough(actual.board[1], expected[1])) throw new Error(`${label}: board dimensions changed`);
    if (actual.squareWidths.length !== 1 || actual.squareHeights.length !== 1 || !closeEnough(actual.squareWidths[0], actual.squareHeights[0])) {
      throw new Error(`${label}: square dimensions are inconsistent`);
    }
  };
  const expectPiece = async (square, glyph, label) => {
    const actual = await page.locator(`[data-square="${square}"] .piece`).textContent();
    if (actual !== glyph) throw new Error(`${label}: expected ${glyph} on ${square}, found ${actual}`);
  };
  let ply = 0;
  const move = async (from, to, promotion) => {
    await page.locator(`[data-square="${from}"]`).click();
    await page.locator(`[data-square="${to}"]`).click();
    if (promotion) await page.getByRole('button', { name: promotion, exact: true }).click();
    ply += 1;
    await page.getByText(`${ply} ${ply === 1 ? 'move' : 'moves'}`, { exact: true }).waitFor();
    await page.waitForFunction(() => {
      const board = document.querySelector('#board');
      const status = document.querySelector('#statusText')?.dataset.state;
      return !board.classList.contains('locked') || ['checkmate', 'stalemate', 'draw'].includes(status);
    });
  };
  const restart = async () => {
    await page.getByRole('button', { name: 'Restart', exact: true }).click();
    await page.getByText('0 moves', { exact: true }).waitFor();
    await page.locator('#board:not(.locked)').waitFor();
    ply = 0;
  };

  await page.getByRole('button', { name: /Pass & Play/ }).click();
  await page.getByRole('heading', { name: 'White to move' }).waitFor();
  if (!(await page.evaluate(() => document.activeElement?.classList.contains('square')))) throw new Error('Keyboard focus did not enter the board');
  if (await page.locator('.piece').count() !== 32) throw new Error('Pass & Play initial board did not render 32 pieces');
  if (await page.locator('#engineCard').isVisible()) throw new Error('Engine card is visible in Pass & Play');
  if (await page.locator('#engineSettings').isVisible()) throw new Error('Engine settings are visible in Pass & Play');
  await page.locator('[data-square="a8"]').focus();
  await page.keyboard.press('ArrowRight');
  if (await page.evaluate(() => document.activeElement?.dataset.square) !== 'b8') throw new Error('Board arrow-key navigation failed');
  await page.locator('[data-square="e2"]').focus();
  await page.keyboard.press('Enter');
  if (await page.evaluate(() => document.activeElement?.dataset.square) !== 'e2') throw new Error('Board selection did not preserve keyboard focus');

  const desktopBoard = (await dimensions()).board;
  await assertStable(desktopBoard, 'starting position');
  await page.evaluate(() => {
    const glyphs = ['♔', '♕', '♖', '♗', '♘', '♙', '♚', '♛', '♜', '♝', '♞', '♟'];
    const middle = [...document.querySelectorAll('.square')].filter((square) => ['3', '4', '5', '6'].includes(square.dataset.square[1]));
    middle.forEach((square, index) => {
      square.replaceChildren();
      const piece = document.createElement('span');
      piece.className = 'piece';
      piece.textContent = glyphs[index % glyphs.length];
      square.append(piece);
    });
  });
  await assertStable(desktopBoard, 'dense middle ranks');
  for (let index = 0; index < 24; index += 1) {
    await page.evaluate((step) => {
      const squares = [...document.querySelectorAll('.square')];
      const from = squares[step % squares.length];
      const to = squares[(step * 11 + 19) % squares.length];
      const piece = from.querySelector('.piece');
      to.querySelector('.piece')?.remove();
      if (piece) to.append(piece);
      if (step === 23 && piece) piece.textContent = '♕';
    }, index);
    await assertStable(desktopBoard, `dense move/capture/promotion ${index + 1}`);
  }
  await restart();
  await page.evaluate(() => { window.__warhorseWorkerActions = []; });

  await move('e2', 'e4');
  await page.getByRole('heading', { name: 'Black to move' }).waitFor();
  await page.waitForTimeout(850);
  if (await page.getByText('1 move', { exact: true }).count() !== 1) throw new Error('Pass & Play generated an automatic reply');
  await move('e7', 'e5');
  await page.getByRole('heading', { name: 'White to move' }).waitFor();
  await assertStable(desktopBoard, 'repeated Pass & Play turns');
  let passActions = await page.evaluate(() => [...window.__warhorseWorkerActions]);
  if (passActions.includes('engine')) throw new Error('Pass & Play invoked engine move generation');

  await restart();
  await move('e2', 'e4');
  await move('d7', 'd5');
  await move('e4', 'd5');
  if ((await page.locator('#capturedByWhite').textContent()) !== '♟') throw new Error('Pawn captured by White was not shown under White');
  if ((await page.locator('#capturedByBlack').textContent()) !== '—') throw new Error('Black capture row changed before Black captured');
  if ((await page.locator('#materialAdvantage').textContent()) !== 'White +1') throw new Error('White material advantage is incorrect');
  if (!(await page.locator('.move-entry.latest-move').textContent()).includes('exd5× Pawn')) throw new Error('Pawn capture context is missing from history');
  await page.getByText('White captured a black pawn', { exact: true }).waitFor();
  await move('d8', 'd5');
  if ((await page.locator('#capturedByBlack').textContent()) !== '♙') throw new Error('Pawn captured by Black was not shown under Black');
  if ((await page.locator('#materialAdvantage').textContent()) !== 'Material even') throw new Error('Even material balance is incorrect');
  if (!(await page.locator('.move-entry.latest-move').textContent()).includes('Qxd5× Pawn')) throw new Error('Queen capture context is missing from history');
  await page.getByText('Black captured a white pawn', { exact: true }).waitFor();
  await assertStable(desktopBoard, 'multiple captures by both sides');
  await page.getByRole('button', { name: 'Flip board' }).click();
  if ((await page.locator('#capturedByWhite').textContent()) !== '♟' || (await page.locator('#capturedByBlack').textContent()) !== '♙') {
    throw new Error('Board flip changed captured-piece ownership');
  }
  await page.getByRole('button', { name: 'Flip board' }).click();
  await page.setViewportSize({ width: 1100, height: 900 });
  const ledgerFits = await page.evaluate(() => {
    const ledger = document.querySelector('#capturedByWhite');
    ledger.replaceChildren(...Array.from({ length: 15 }, () => {
      const piece = document.createElement('span');
      piece.textContent = '♟';
      return piece;
    }));
    return ledger.scrollWidth <= ledger.clientWidth;
  });
  if (!ledgerFits) throw new Error('Full captured-piece ledger is clipped');
  await page.setViewportSize({ width: 1280, height: 900 });
  await assertStable(desktopBoard, 'full captured-piece ledger');

  await restart();
  if ((await page.locator('#capturedByWhite').textContent()) !== '—' || (await page.locator('#capturedByBlack').textContent()) !== '—') {
    throw new Error('Restart did not clear captured pieces');
  }
  if (await page.locator('#lastCapture').isVisible()) throw new Error('Restart did not clear last-capture feedback');
  await move('g1', 'f3');
  await move('e7', 'e5');
  await move('f3', 'e5');
  if (!(await page.locator('.move-entry.latest-move').textContent()).includes('Nxe5× Pawn')) throw new Error('Knight capture was not recorded');
  await assertStable(desktopBoard, 'knight capture');

  await restart();
  for (const [from, to] of [['e2', 'e4'], ['d7', 'd5'], ['f1', 'b5'], ['c7', 'c6'], ['b5', 'c6']]) await move(from, to);
  const bishopCapture = await page.locator('.move-entry.latest-move').textContent();
  if (!bishopCapture.includes('Bxc6') || !bishopCapture.includes('× Pawn')) throw new Error('Bishop capture was not recorded');
  await assertStable(desktopBoard, 'bishop capture');

  await restart();
  for (const [from, to] of [['a2', 'a4'], ['h7', 'h5'], ['a1', 'a3'], ['h5', 'h4'], ['a3', 'h3'], ['a7', 'a6'], ['h3', 'h4']]) await move(from, to);
  if (!(await page.locator('.move-entry.latest-move').textContent()).includes('Rxh4× Pawn')) throw new Error('Rook capture was not recorded');
  await assertStable(desktopBoard, 'rook capture');

  await restart();
  for (const [from, to] of [['f2', 'f3'], ['a7', 'a6'], ['b1', 'c3'], ['a6', 'a5'], ['g1', 'h3'], ['h7', 'h6'], ['h3', 'f2'], ['h6', 'h5'], ['c3', 'e4']]) await move(from, to);
  if (!(await page.locator('.move-entry.latest-move').textContent()).startsWith('Nce4')) throw new Error('Ambiguous knight history lacks file disambiguation');

  await restart();
  for (const [from, to] of [['e2', 'e4'], ['e7', 'e5'], ['f1', 'c4'], ['b8', 'c6'], ['d1', 'h5'], ['g8', 'f6'], ['h5', 'f7']]) {
    await move(from, to);
  }
  await page.getByRole('heading', { name: 'Checkmate' }).waitFor();
  await page.getByText('Player 1 wins as White', { exact: true }).waitFor();
  if (await page.locator('.square.checkmate').count() !== 1) throw new Error('Checkmated king is not highlighted');
  await assertStable(desktopBoard, 'complete Pass & Play checkmate game');

  await restart();
  for (const [from, to] of [['e2', 'e4'], ['e7', 'e5'], ['g1', 'f3'], ['b8', 'c6'], ['f1', 'e2'], ['g8', 'f6'], ['e1', 'g1']]) {
    await move(from, to);
  }
  await expectPiece('g1', '♔', 'castling');
  await expectPiece('f1', '♖', 'castling');
  await assertStable(desktopBoard, 'castling');

  await restart();
  for (const [from, to] of [['e2', 'e4'], ['a7', 'a6'], ['e4', 'e5'], ['d7', 'd5'], ['e5', 'd6']]) {
    await move(from, to);
  }
  await expectPiece('d6', '♙', 'en passant');
  if (await page.locator('[data-square="d5"] .piece').count()) throw new Error('En passant did not remove the captured pawn');
  await assertStable(desktopBoard, 'en passant');

  await restart();
  for (const [from, to] of [['a2', 'a4'], ['h7', 'h6'], ['a4', 'a5'], ['h6', 'h5'], ['a5', 'a6'], ['h5', 'h4'], ['a6', 'b7'], ['h4', 'h3']]) {
    await move(from, to);
  }
  await move('b7', 'a8', 'Knight');
  await expectPiece('a8', '♘', 'underpromotion');
  await assertStable(desktopBoard, 'real promotion');

  await page.getByRole('button', { name: 'Flip board' }).click();
  if (await page.locator('.square').first().getAttribute('data-square') !== 'h1') throw new Error('Board flip failed');
  await assertStable(desktopBoard, 'flipped promoted position');
  await restart();
  await page.getByRole('button', { name: 'Resign', exact: true }).click();
  await page.getByRole('heading', { name: 'Black wins' }).waitFor();
  await page.getByText('Player 1 resigned', { exact: true }).waitFor();
  await assertStable(desktopBoard, 'Pass & Play resignation');
  passActions = await page.evaluate(() => [...window.__warhorseWorkerActions]);
  if (passActions.includes('engine')) throw new Error('A Pass & Play flow invoked engine move generation');

  await page.getByRole('button', { name: 'New game', exact: true }).click();
  await page.getByRole('heading', { name: 'Choose your game' }).waitFor();
  await page.getByRole('button', { name: /Vs Warhorse/ }).click();
  await page.getByRole('heading', { name: 'Your turn' }).waitFor();
  if (!(await page.locator('#engineCard').isVisible())) throw new Error('Engine card is hidden in Vs Warhorse');
  if (!(await page.locator('#engineSettings').isVisible())) throw new Error('Engine settings are hidden in Vs Warhorse');
  await page.locator('#thinkTime').selectOption('250');
  await page.evaluate(() => { window.__warhorseWorkerActions = []; });
  ply = 0;
  const engineMove = async (from, to, expectedPly) => {
    await page.locator(`[data-square="${from}"]`).click();
    await page.locator(`[data-square="${to}"]`).click();
    await page.getByText(`${expectedPly} moves`, { exact: true }).waitFor({ timeout: 10_000 });
    await page.getByRole('heading', { name: 'Your turn' }).waitFor();
    await page.locator('#board:not(.locked)').waitFor();
  };
  await engineMove('e2', 'e4', 2);
  await engineMove('g1', 'f3', 4);
  await engineMove('d2', 'd4', 6);
  if (!(await page.locator('#capturedByBlack').textContent()).includes('♙')) throw new Error('Warhorse capture was not shown under Black');
  await engineMove('f3', 'd4', 8);
  if (!(await page.locator('#capturedByWhite').textContent()).includes('♟')) throw new Error('Player capture was not shown under White in Vs Warhorse');
  if (!(await page.locator('.move-entry').filter({ hasText: 'Nxd4' }).textContent()).includes('× Pawn')) throw new Error('Vs Warhorse capture history is missing context');
  await page.setViewportSize({ width: 1280, height: 680 });
  const shortPanelFits = await page.evaluate(() => {
    const history = document.querySelector('#moveHistory').getBoundingClientRect();
    const settings = document.querySelector('#engineSettings').getBoundingClientRect();
    const panel = document.querySelector('.game-panel');
    return history.height >= 68 && history.bottom <= settings.top && panel.scrollHeight >= panel.clientHeight;
  });
  if (!shortPanelFits) throw new Error('Game panel content is not contained at short desktop height');
  await page.setViewportSize({ width: 1280, height: 900 });
  const engineActions = await page.evaluate(() => [...window.__warhorseWorkerActions]);
  if (!engineActions.includes('play') || !engineActions.includes('engine')) throw new Error('Vs Warhorse did not request a player move and engine reply');
  await assertStable(desktopBoard, 'real player and engine moves');
  await page.getByRole('button', { name: 'Flip board' }).click();
  if (await page.locator('.square').first().getAttribute('data-square') !== 'h1') throw new Error('Vs Warhorse board flip failed');
  await assertStable(desktopBoard, 'flipped Vs Warhorse position');
  await page.getByRole('button', { name: 'Resign', exact: true }).click();
  await page.getByRole('heading', { name: 'Black wins' }).waitFor();
  await page.getByRole('button', { name: 'Restart', exact: true }).click();
  await page.getByRole('heading', { name: 'Your turn' }).waitFor();
  await page.getByRole('button', { name: 'Resign', exact: true }).click();
  await page.getByRole('heading', { name: 'Black wins' }).waitFor();
  await page.getByRole('button', { name: 'Restart', exact: true }).click();
  await page.getByRole('heading', { name: 'Your turn' }).waitFor();
  await page.locator('#thinkTime').selectOption('2500');
  await page.locator('[data-square="d2"]').click();
  await page.locator('[data-square="d3"]').click();
  await page.getByRole('heading', { name: 'Warhorse thinking' }).waitFor();
  await page.getByRole('button', { name: 'Change', exact: true }).click();
  await page.getByRole('button', { name: /Pass & Play/ }).click();
  await page.getByRole('heading', { name: 'White to move' }).waitFor({ timeout: 1500 });

  await page.setViewportSize({ width: 800, height: 1000 });
  const tabletBoard = (await dimensions()).board;
  await assertStable(tabletBoard, 'tablet game-over position');
  const tabletLayout = await page.evaluate(() => {
    const board = document.querySelector('.board-column').getBoundingClientRect();
    const panel = document.querySelector('.game-panel').getBoundingClientRect();
    return { boardBottom: board.bottom, panelTop: panel.top };
  });
  if (tabletLayout.panelTop < tabletLayout.boardBottom) throw new Error('Tablet panel overlaps the board');

  await page.setViewportSize({ width: 390, height: 844 });
  const mobileBoard = (await dimensions()).board;
  await assertStable(mobileBoard, 'mobile game-over position');
  if (mobileBoard[0] >= desktopBoard[0]) throw new Error('Board did not scale down on mobile');

  await page.getByRole('button', { name: 'New game', exact: true }).click();
  await page.setViewportSize({ width: 400, height: 300 });
  await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
  await page.getByRole('button', { name: /Pass & Play/ }).click();
  await page.getByRole('heading', { name: 'White to move' }).waitFor();
  if ((await page.locator('#capturedByWhite').textContent()) !== '—' || (await page.locator('#capturedByBlack').textContent()) !== '—') {
    throw new Error('New game did not clear captured pieces');
  }
  const landscape = await page.evaluate(() => {
    const board = document.querySelector('#board').getBoundingClientRect();
    return { scrollY: window.scrollY, top: board.top, bottom: board.bottom, width: board.width, height: board.height };
  });
  if (landscape.scrollY !== 0 || landscape.top < 0 || landscape.bottom > 300) throw new Error('Landscape game did not open with the full board visible');
  if (!closeEnough(landscape.width, landscape.height)) throw new Error('Landscape board is not square');
  if (errors.length) throw new Error(errors.join('\n'));
  console.log(
    `web smoke: desktop ${desktopBoard[0]}x${desktopBoard[1]}, tablet ${tabletBoard[0]}x${tabletBoard[1]}, mobile ${mobileBoard[0]}x${mobileBoard[1]}, landscape ${landscape.width}x${landscape.height}; modes, turns, dense ranks, captures, checkmate, castling, en passant, promotion, resign, engine reply, controls, and responsive layout passed`,
  );
} finally {
  if (browser) await browser.close();
  server.kill();
}
