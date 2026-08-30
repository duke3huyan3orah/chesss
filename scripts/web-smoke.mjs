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
  await page.goto('http://127.0.0.1:4173', { waitUntil: 'networkidle' });
  await page.getByText('Your move', { exact: true }).waitFor();
  if (await page.locator('.piece').count() !== 32) throw new Error('Initial board did not render 32 pieces');

  const dimensions = () => page.evaluate(() => {
    const board = document.querySelector('#board').getBoundingClientRect();
    const squares = [...document.querySelectorAll('.square')].map((square) => square.getBoundingClientRect());
    return {
      board: [board.width, board.height],
      squareWidths: [...new Set(squares.map((square) => square.width))],
      squareHeights: [...new Set(squares.map((square) => square.height))],
    };
  });
  const assertStable = async (expected, label) => {
    const actual = await dimensions();
    if (actual.board[0] !== actual.board[1]) throw new Error(`${label}: board is not square`);
    if (actual.board[0] !== expected[0] || actual.board[1] !== expected[1]) throw new Error(`${label}: board dimensions changed`);
    if (actual.squareWidths.length !== 1 || actual.squareHeights.length !== 1 || actual.squareWidths[0] !== actual.squareHeights[0]) {
      throw new Error(`${label}: square dimensions are inconsistent`);
    }
  };
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
    await assertStable(desktopBoard, `move/capture/promotion ${index + 1}`);
  }

  await page.getByRole('button', { name: 'New game' }).click();
  await page.getByText('Your move', { exact: true }).waitFor();
  // This leaves the tiny opening book, exercising a real timed WASM search.
  await page.locator('[data-square="d2"]').click();
  await page.locator('[data-square="d3"]').click();
  await page.getByText('2 moves', { exact: true }).waitFor({ timeout: 10_000 });
  await page.getByText('Your move', { exact: true }).waitFor();
  if (await page.locator('.piece').count() !== 32) throw new Error('Position desynchronized after engine reply');
  await assertStable(desktopBoard, 'real player and engine moves');
  await page.getByRole('button', { name: 'Flip board' }).click();
  if (await page.locator('.square').first().getAttribute('data-square') !== 'h1') throw new Error('Board flip failed');
  await page.getByRole('button', { name: 'New game' }).click();
  await page.getByText('0 moves', { exact: true }).waitFor();

  await page.setViewportSize({ width: 390, height: 844 });
  const mobileBoard = (await dimensions()).board;
  await assertStable(mobileBoard, 'mobile position');
  if (mobileBoard[0] >= desktopBoard[0]) throw new Error('Board did not scale down on mobile');
  if (errors.length) throw new Error(errors.join('\n'));
  console.log(
    `web smoke: fixed dimensions passed (desktop ${desktopBoard[0]}×${desktopBoard[1]}, mobile ${mobileBoard[0]}×${mobileBoard[1]}); dense ranks, moves, captures, promotion, engine reply, history, flip, and reset passed`,
  );
} finally {
  if (browser) await browser.close();
  server.kill();
}
