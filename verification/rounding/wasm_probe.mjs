// GPL-2.0-or-later. Exercise primitive f64 operations directly in WebAssembly.
import { readFileSync } from 'node:fs';

const vectors = JSON.parse(readFileSync(0, 'utf8'));
const section = (id, bytes) => [id, bytes.length, ...bytes];
const operators = ['add', 'sub', 'mul', 'div'];
const exports = operators.flatMap((name, index) => [name.length, ...Buffer.from(name), 0, index]);
// Core binary format: f64 parameters/results (0x7c), local.get (0x20),
// f64.add/sub/mul/div (0xa0..0xa3), end (0x0b). Each body has zero locals.
const binary = new Uint8Array([
  0, 97, 115, 109, 1, 0, 0, 0,
  ...section(1, [1, 0x60, 2, 0x7c, 0x7c, 1, 0x7c]),
  ...section(3, [4, 0, 0, 0, 0]),
  ...section(7, [4, ...exports]),
  ...section(10, [4, ...operators.flatMap((_, i) => [7, 0, 0x20, 0, 0x20, 1, 0xa0 + i, 0x0b])]),
]);
const instance = new WebAssembly.Instance(new WebAssembly.Module(binary));
const buffer = new ArrayBuffer(8);
const view = new DataView(buffer);
const number = (bits) => {
  view.setBigUint64(0, BigInt(`0x${bits}`), true);
  return view.getFloat64(0, true);
};
const encode = (value) => {
  view.setFloat64(0, value, true);
  return view.getBigUint64(0, true).toString(16).padStart(16, '0');
};
const results = vectors.map(({ op, left, right }) => encode(instance.exports[op](number(left), number(right))));
process.stdout.write(JSON.stringify({ node: process.version, v8: process.versions.v8,
  wasmBinaryHex: Buffer.from(binary).toString('hex'), results }));
