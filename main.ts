// A complete interpreter for make.fun's tiny stack ISA v1, written from the
// kit's ISA.md. One run answers a whole set: /input/<id>/program.bin plus
// input.bin in, /output/<id>/stdout.bin and exit.txt out. All ten trap codes,
// the step and output limits, wrapping 32-bit arithmetic, unsigned DIVU/MODU/
// LTU, and the INT_MIN/-1 edge cases are honoured.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

type Answer = { out: Uint8Array; code: number };

function run(p: Uint8Array, input: Uint8Array): Answer {
  const n = p.length;
  const st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const done = (code: number): Answer => ({ out: out.subarray(0, ol), code });

  for (;;) {
    if (steps === 1000000) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside the program
    const op = p[pc];
    const known =
      op <= 0x07 ||
      (op >= 0x10 && op <= 0x22) ||
      (op >= 0x30 && op <= 0x34) ||
      op === 0x40 ||
      op === 0x41 ||
      (op >= 0x50 && op <= 0x53);
    if (!known) return done(5); // unknown opcode
    const imm = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= n) return done(9); // immediate cut off by the end
    steps++;
    switch (op) {
      case 0x00: // HALT
        return done(0);
      case 0x01: // PUSH8, sign-extended
        if (sp === 256) return done(3);
        st[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
        break;
      case 0x02: // PUSH32, little-endian
        if (sp === 256) return done(3);
        st[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
        break;
      case 0x03: // POP
        if (sp < 1) return done(2);
        sp--;
        pc++;
        break;
      case 0x04: // DUP
        if (sp < 1) return done(2);
        if (sp === 256) return done(3);
        st[sp] = st[sp - 1];
        sp++;
        pc++;
        break;
      case 0x05: // SWAP
        if (sp < 2) return done(2);
        {
          const t = st[sp - 1];
          st[sp - 1] = st[sp - 2];
          st[sp - 2] = t;
        }
        pc++;
        break;
      case 0x06: // OVER
        if (sp < 2) return done(2);
        if (sp === 256) return done(3);
        st[sp] = st[sp - 2];
        sp++;
        pc++;
        break;
      case 0x07: // ROT
        if (sp < 3) return done(2);
        {
          const a = st[sp - 3];
          st[sp - 3] = st[sp - 2];
          st[sp - 2] = st[sp - 1];
          st[sp - 1] = a;
        }
        pc++;
        break;
      case 0x17: // NEG
        if (sp < 1) return done(2);
        st[sp - 1] = -st[sp - 1] | 0;
        pc++;
        break;
      case 0x1b: // NOT
        if (sp < 1) return done(2);
        st[sp - 1] = ~st[sp - 1];
        pc++;
        break;
      case 0x10: // ADD
      case 0x11: // SUB
      case 0x12: // MUL
      case 0x13: // DIV
      case 0x14: // MOD
      case 0x15: // DIVU
      case 0x16: // MODU
      case 0x18: // AND
      case 0x19: // OR
      case 0x1a: // XOR
      case 0x1c: // SHL
      case 0x1d: // SHR
      case 0x1e: // SHRU
      case 0x20: // EQ
      case 0x21: // LT
      case 0x22: { // LTU
        if (sp < 2) return done(2);
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
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
        pc++;
        break;
      }
      case 0x30: // JMP
      case 0x31: // JZ
      case 0x32: { // JNZ
        const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
        pc += 3;
        if (op === 0x30) {
          pc += rel;
        } else {
          if (sp < 1) return done(2);
          const v = st[--sp];
          if ((op === 0x31) === (v === 0)) pc += rel;
        }
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return done(7);
        cs[cp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return done(8);
        pc = cs[--cp];
        break;
      case 0x40: { // LOAD
        if (sp < 1) return done(2);
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        st[sp - 1] = mem[addr];
        pc++;
        break;
      }
      case 0x41: { // STORE
        if (sp < 2) return done(2);
        const addr = st[sp - 1];
        const v = st[sp - 2];
        if (addr < 0 || addr > 255) return done(6);
        sp -= 2;
        mem[addr] = v;
        pc++;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII, no newline
        if (sp < 1) return done(2);
        const s = String(st[sp - 1]);
        if (ol + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        pc++;
        break;
      }
      case 0x51: // PUTC
        if (sp < 1) return done(2);
        if (ol + 1 > 65536) return done(11);
        out[ol++] = st[--sp] & 255;
        pc++;
        break;
      case 0x52: // IN, -1 once the input is used up
        if (sp === 256) return done(3);
        st[sp++] = ip < input.length ? input[ip++] : -1;
        pc++;
        break;
      case 0x53: // EXIT, low byte of the code
        if (sp < 1) return done(2);
        return done(st[--sp] & 255);
      default:
        return done(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
