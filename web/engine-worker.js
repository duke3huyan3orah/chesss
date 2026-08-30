import { WASI, File, OpenFile, ConsoleStdout } from '@bjorn3/browser_wasi_shim';

let compiledModule;

async function getModule() {
  if (!compiledModule) {
    compiledModule = (async () => {
      const response = await fetch('/engine/warhorse.wasm');
      if (!response.ok) throw new Error(`Engine download failed (${response.status})`);
      try {
        return await WebAssembly.compileStreaming(response.clone());
      } catch {
        return WebAssembly.compile(await response.arrayBuffer());
      }
    })();
  }
  return compiledModule;
}

async function invoke(args) {
  const stdout = [];
  const stderr = [];
  const fds = [
    new OpenFile(new File([])),
    ConsoleStdout.lineBuffered((line) => stdout.push(line)),
    ConsoleStdout.lineBuffered((line) => stderr.push(line)),
  ];
  const wasi = new WASI(['warhorse', 'web', ...args], [], fds, { debug: false });
  const instance = await WebAssembly.instantiate(await getModule(), {
    wasi_snapshot_preview1: wasi.wasiImport,
  });
  wasi.start(instance);
  const line = stdout.findLast((value) => value.trim().startsWith('{'));
  if (!line) throw new Error(stderr.join('\n') || 'Engine returned no state');
  const result = JSON.parse(line);
  if (!result.ok) throw new Error(result.error || 'Engine request failed');
  return result;
}

self.onmessage = async ({ data }) => {
  try {
    const moves = data.moves.length ? data.moves.join(',') : '-';
    const args = data.action === 'state'
      ? ['state', moves]
      : data.action === 'play'
        ? ['play', moves, data.move]
        : ['engine', moves, String(data.thinkTime)];
    self.postMessage({ id: data.id, result: await invoke(args) });
  } catch (error) {
    self.postMessage({ id: data.id, error: error instanceof Error ? error.message : String(error) });
  }
};
