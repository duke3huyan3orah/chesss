'use strict';

import childProcess from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

if (process.argv[2] === '--worker') {
  const fs = await import('node:fs');
  const { WASI } = await import('node:wasi');
  const wasi = new WASI({
    version: 'preview1',
    args: ['warhorse', ...process.argv.slice(3)],
    env: process.env,
    stdin: 0,
    stdout: 1,
    stderr: 2,
  });
  const wasmPath = path.join(__dirname, 'target', 'wasm32-wasip1', 'release', 'warhorse.wasm');
  WebAssembly.instantiate(fs.readFileSync(wasmPath), { wasi_snapshot_preview1: wasi.wasiImport })
    .then(({ instance }) => wasi.start(instance))
    .catch((error) => {
      console.error(error);
      process.exitCode = 1;
    });
} else if (process.argv.length > 2) {
  const child = childProcess.spawn(
    process.execPath,
    ['--no-warnings', __filename, '--worker', ...process.argv.slice(2)],
    { stdio: 'inherit' },
  );
  child.on('exit', (code) => process.exit(code ?? 1));
} else {
  const readline = await import('node:readline');
  let engine;
  let restarting = false;
  let searching = false;
  let stopRequested = false;
  let stopTimer = null;
  let infiniteSearch = false;
  let latestMove = null;
  let outputBuffer = '';
  let lastPosition = 'position startpos';
  const options = new Map();
  const pending = [];

  function interruptSearch() {
    if (!searching) return;
    searching = false;
    stopRequested = false;
    if (stopTimer) clearTimeout(stopTimer);
    stopTimer = null;
    restarting = true;
    engine.kill();
    process.stdout.write(`bestmove ${latestMove || '0000'}\n`);
  }

  function startEngine(replayState) {
    outputBuffer = '';
    engine = childProcess.spawn(process.execPath, ['--no-warnings', __filename, '--worker'], {
      stdio: ['pipe', 'pipe', 'pipe'],
    });
    engine.stderr.pipe(process.stderr);
    engine.stdout.on('data', (chunk) => {
      if (restarting) return;
      const text = chunk.toString();
      process.stdout.write(text);
      outputBuffer += text;
      let newline;
      while ((newline = outputBuffer.indexOf('\n')) !== -1) {
        const line = outputBuffer.slice(0, newline).trim();
        outputBuffer = outputBuffer.slice(newline + 1);
        const pv = line.match(/\spv\s+(\S+)/);
        if (pv) latestMove = pv[1];
        if (line.startsWith('bestmove ')) {
          searching = false;
          stopRequested = false;
          if (stopTimer) clearTimeout(stopTimer);
          stopTimer = null;
        }
      }
      if (stopRequested && latestMove) interruptSearch();
    });
    engine.on('exit', (code) => {
      if (restarting) {
        restarting = false;
        startEngine(true);
      } else if (code && code !== 0) {
        process.exitCode = code;
      }
    });
    if (replayState) {
      for (const command of options.values()) engine.stdin.write(`${command}\n`);
      engine.stdin.write(`${lastPosition}\n`);
      while (pending.length) engine.stdin.write(`${pending.shift()}\n`);
    }
  }

  startEngine(false);
  readline.createInterface({ input: process.stdin }).on('line', (line) => {
    const command = line.trim();
    if (command.startsWith('position ')) lastPosition = command;
    if (command === 'ucinewgame') lastPosition = 'position startpos';
    if (command.startsWith('setoption name ')) {
      const name = command.slice('setoption name '.length).split(' value ')[0];
      options.set(name, command);
    }
    if (command.startsWith('go')) {
      searching = true;
      stopRequested = false;
      infiniteSearch = command.split(/\s+/).includes('infinite');
      latestMove = null;
    }
    if (command === 'stop' && searching) {
      if (latestMove) interruptSearch();
      else {
        stopRequested = true;
        stopTimer = setTimeout(interruptSearch, 500);
      }
      return;
    }
    if (command === 'quit') {
      restarting = false;
      if (infiniteSearch && searching) engine.kill();
      else {
        engine.stdin.end('quit\n');
        setTimeout(() => engine.kill(), 2_000).unref();
      }
      process.stdin.pause();
      engine.once('exit', () => process.exit(0));
      return;
    }
    if (restarting) {
      pending.push(command);
      return;
    }
    engine.stdin.write(`${command}\n`);
  });
}
