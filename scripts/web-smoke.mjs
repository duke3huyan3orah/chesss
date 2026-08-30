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
  // This leaves the tiny opening book, exercising a real timed WASM search.
  await page.locator('[data-square="d2"]').click();
  await page.locator('[data-square="d3"]').click();
  await page.getByText('2 moves', { exact: true }).waitFor({ timeout: 10_000 });
  await page.getByText('Your move', { exact: true }).waitFor();
  if (await page.locator('.piece').count() !== 32) throw new Error('Position desynchronized after engine reply');
  await page.getByRole('button', { name: 'Flip board' }).click();
  if (await page.locator('.square').first().getAttribute('data-square') !== 'h1') throw new Error('Board flip failed');
  await page.getByRole('button', { name: 'New game' }).click();
  await page.getByText('0 moves', { exact: true }).waitFor();
  if (errors.length) throw new Error(errors.join('\n'));
  console.log('web smoke: board, legal move, engine reply, history, flip, and reset passed');
} finally {
  if (browser) await browser.close();
  server.kill();
}
