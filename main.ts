// tiny-stack-vm: interpreter for make.fun's tiny stack ISA v1 (kit ISA.md).
// Answers all 40 instances in one run: /input/<id>/{program,input}.bin in,
// /output/<id>/{stdout.bin,exit.txt} out (or MAKEFUN_INPUT_DIR/OUTPUT_DIR).
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";

// Opcode table, from ISA.md: [byte, immediate bytes, values popped, values pushed].
// The 37 opcodes the ISA names; any other byte is trap 5 (unknown opcode).
const OPS = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Uint8Array(256);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [b, i, p, u] of OPS) { KNOWN[b] = 1; IMM[b] = i; POP[b] = p; PSH[b] = u; }

const enc = new TextEncoder();

// Runs one program on its input bytes. Returns [bytes written, exit code].
// Checks run in ISA.md's order: step limit, pc range, unknown opcode,
// truncated immediate, stack underflow/overflow, instruction trap, effect.
// A trap keeps earlier output; the trapping instruction writes nothing.
function run(P, I) {
  const n = P.length;
  const D = new Int32Array(256);   // data stack, at most 256 values
  const C = new Int32Array(64);    // call stack, at most 64 return addresses
  const M = new Int32Array(256);   // memory, 256 words
  const O = new Uint8Array(65536); // output, at most 65,536 bytes
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (exit) => [O.subarray(0, ol), exit];
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const b = P[pc];
    if (!KNOWN[b]) return end(5);
    const im = IMM[b];
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < POP[b]) return end(2);
    if (sp - POP[b] + PSH[b] > 256) return end(3);
    pc = nx;
    switch (b) {
      case 0x00: return end(0); // HALT
      case 0x01: D[sp++] = (P[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps: -INT_MIN is INT_MIN)
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const y = D[sp - 1], x = D[sp - 2];
        let r;
        switch (b) {
          case 0x10: r = (x + y) | 0; break; // ADD, wraps
          case 0x11: r = (x - y) | 0; break; // SUB, wraps
          case 0x12: r = Math.imul(x, y); break; // MUL, exact low 32 bits
          case 0x13: // DIV, truncated toward zero
            if (y === 0) return end(4);
            r = x === -2147483648 && y === -1 ? x : (x / y) | 0;
            break;
          case 0x14: // MOD, sign of x
            if (y === 0) return end(4);
            r = y === -1 ? 0 : (x % y) | 0;
            break;
          case 0x15: // DIVU, unsigned
            if (y === 0) return end(4);
            r = Math.floor((x >>> 0) / (y >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned
            if (y === 0) return end(4);
            r = ((x >>> 0) % (y >>> 0)) | 0;
            break;
          case 0x18: r = x & y; break; // AND
          case 0x19: r = x | y; break; // OR
          case 0x1a: r = x ^ y; break; // XOR
          case 0x1c: r = x << (y & 31); break; // SHL, low 5 bits of count
          case 0x1d: r = x >> (y & 31); break; // SHR, arithmetic
          case 0x1e: r = (x >>> (y & 31)) | 0; break; // SHRU, logical
          case 0x20: r = x === y ? 1 : 0; break; // EQ
          case 0x21: r = x < y ? 1 : 0; break; // LT, signed
          default: r = (x >>> 0) < (y >>> 0) ? 1 : 0; break; // 0x22 LTU, unsigned
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ: signed offset from next
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (b !== 0x30) {
          const v = D[--sp];
          take = b === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL: unsigned target, 64 return addresses at most
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE: ( value address -- )
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const s = enc.encode(String(D[sp - 1]));
        if (ol + s.length > 65536) return end(11);
        sp--;
        O.set(s, ol);
        ol += s.length;
        break;
      }
      case 0x51: // PUTC: one byte, low 8 bits
        if (ol + 1 > 65536) return end(11);
        O[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < I.length ? I[ip++] : -1; break; // IN: -1 past the end
      default: return end(D[--sp] & 255); // 0x53 EXIT: low byte
    }
  }
}

// Entrypoint: answer all 40 instances of the set in one run.
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (let k = 1; k <= 40; k++) {
  const id = "i" + String(k).padStart(3, "0");
  const [out, exit] = run(
    readFileSync(`${IN_DIR}/${id}/program.bin`),
    readFileSync(`${IN_DIR}/${id}/input.bin`),
  );
  mkdirSync(`${OUT_DIR}/${id}`, { recursive: true });
  writeFileSync(`${OUT_DIR}/${id}/stdout.bin`, out);
  writeFileSync(`${OUT_DIR}/${id}/exit.txt`, exit + "\n");
}
