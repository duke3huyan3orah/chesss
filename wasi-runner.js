'use strict';

import fs from 'node:fs';
import { WASI } from 'node:wasi';

const wasmPath = process.argv[2];
const wasi = new WASI({
  version: 'preview1',
  args: [wasmPath, ...process.argv.slice(3)],
  env: process.env,
  stdin: 0,
  stdout: 1,
  stderr: 2,
});

WebAssembly.instantiate(fs.readFileSync(wasmPath), { wasi_snapshot_preview1: wasi.wasiImport })
  .then(({ instance }) => wasi.start(instance))
  .catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
