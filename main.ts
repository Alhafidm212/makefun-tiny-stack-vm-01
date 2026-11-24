// tiny-stack-vm: a small interpreter for make.fun's tiny stack ISA (v1).
// One run answers every instance under the input dir: for each <id> it reads
// program.bin + input.bin and writes stdout.bin + exit.txt under the output dir.
// Semantics follow the ISA: 32-bit wrapping ints, 256-slot data stack, 64-deep
// call stack, 256 words of memory, 1,000,000 step limit, 65,536 output limit,
// ten traps with their own exit codes (2..11).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table, packed one byte per opcode: (imm << 4) | (pops << 2) | pushes,
// stored +1 so 0 still means "no such opcode" (trap 5). Decoded once at load,
// so the hot loop pays one typed-array read instead of an object lookup.
const SPEC = new Uint8Array(256);
for (const [o, v] of [
  [0, 1], [1, 18], [2, 66], [3, 5], [4, 7], [5, 11], [6, 12], [7, 16],
  [16, 10], [17, 10], [18, 10], [19, 10], [20, 10], [21, 10], [22, 10], [23, 6],
  [24, 10], [25, 10], [26, 10], [27, 6], [28, 10], [29, 10], [30, 10],
  [32, 10], [33, 10], [34, 10],
  [48, 33], [49, 37], [50, 37], [51, 33], [52, 1],
  [64, 6], [65, 9], [80, 5], [81, 5], [82, 2], [83, 5],
]) SPEC[o] = v;

function run(prog: Uint8Array, input: Uint8Array): { bytes: Uint8Array; code: number } {
  const n = prog.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, steps = 0, olen = 0;
  const end = (code: number) => ({ bytes: out.slice(0, olen), code });

  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const s = SPEC[op];
    if (!s) return end(5);
    const q = s - 1, imm = q >> 4, pops = (q >> 2) & 3, pushes = q & 3;
    if (pc + imm >= n) return end(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    pc = next;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: st[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02:
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 0x17: st[sp - 1] = -st[sp - 1] | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        cs[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = cs[--cp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr >= 256) return end(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return end(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 0x52:
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return end(st[--sp] & 255);
    }
  }
}

const IND = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTD = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IND).sort()) {
  const dir = join(IND, id);
  let prog: Uint8Array, input: Uint8Array;
  try {
    prog = new Uint8Array(readFileSync(join(dir, 'program.bin')));
    input = new Uint8Array(readFileSync(join(dir, 'input.bin')));
  } catch { continue; }
  const r = run(prog, input);
  mkdirSync(join(OUTD, id), { recursive: true });
  writeFileSync(join(OUTD, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(OUTD, id, 'exit.txt'), `${r.code}\n`);
}
