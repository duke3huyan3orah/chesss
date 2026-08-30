import { spawnSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';

const localCargo = process.platform === 'win32'
  ? join(process.env.USERPROFILE || '', '.cargo', 'bin', 'cargo.exe')
  : join(process.env.HOME || '', '.cargo', 'bin', 'cargo');
const cargo = process.env.CARGO || (existsSync(localCargo) ? localCargo : 'cargo');
const build = spawnSync(cargo, ['build', '--release'], { stdio: 'inherit' });

if (build.error) throw build.error;
if (build.status !== 0) process.exit(build.status ?? 1);

const source = resolve('target/wasm32-wasip1/release/warhorse.wasm');
const destination = resolve('public/engine/warhorse.wasm');
mkdirSync(dirname(destination), { recursive: true });
copyFileSync(source, destination);
console.log(`Copied engine to ${destination}`);
