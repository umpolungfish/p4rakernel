export type LatticeOrder = 'info' | 'truth' | 'falsity';

export interface Sixteen3StateInfo {
  mask: number;
  members: ('N' | 'T' | 'F' | 'B')[];
  label: string;
  hasN: boolean;
  hasT: boolean;
  hasF: boolean;
  hasB: boolean;
}

export const BIT_N = 1;
export const BIT_T = 2;
export const BIT_F = 4;
export const BIT_B = 8;

export function describeMask(mask: number): Sixteen3StateInfo {
  const m = mask & 15;
  const members: ('N' | 'T' | 'F' | 'B')[] = [];
  if (m & BIT_N) members.push('N');
  if (m & BIT_T) members.push('T');
  if (m & BIT_F) members.push('F');
  if (m & BIT_B) members.push('B');
  return {
    mask: m,
    members,
    label: members.length === 0 ? '∅' : `{${members.join(',')}}`,
    hasN: (m & BIT_N) !== 0,
    hasT: (m & BIT_T) !== 0,
    hasF: (m & BIT_F) !== 0,
    hasB: (m & BIT_B) !== 0,
  };
}

// Information order le_i: subset inclusion on P({N,T,F,B})
export function joinI(a: number, b: number): number {
  return (a | b) & 15;
}
export function meetI(a: number, b: number): number {
  return (a & b) & 15;
}
export function leI(a: number, b: number): boolean {
  return (a & b & 15) === (a & 15);
}

// Truth order le_t: T,B positive (mask 10), N,F negative (mask 5)
export function joinT(a: number, b: number): number {
  return (((a & b) & 5) | ((a | b) & 10)) & 15;
}
export function meetT(a: number, b: number): number {
  return (((a | b) & 5) | ((a & b) & 10)) & 15;
}
export function leT(a: number, b: number): boolean {
  return joinT(a, b) === (b & 15);
}

// Falsity order le_f: F,B positive (mask 12), N,T negative (mask 3)
export function joinF(a: number, b: number): number {
  return (((a & b) & 3) | ((a | b) & 12)) & 15;
}
export function meetF(a: number, b: number): number {
  return (((a | b) & 3) | ((a & b) & 12)) & 15;
}
export function leF(a: number, b: number): boolean {
  return joinF(a, b) === (b & 15);
}

// Belnap truth negation lifted pointwise to P({N,T,F,B}): swaps T (2) <-> F (4), fixes N (1) and B (8)
export function negation(x: number): number {
  const m = x & 15;
  return (m & 9) | ((m & 2) << 1) | ((m & 4) >> 1);
}

// Set complement on SIXTEEN_3
export function complement(x: number): number {
  return (~x) & 15;
}

// Re-entry retain / inject primitives from bridge/check.py
export function retainAfterInject(a: number, b: number): number[] {
  return Array.from({ length: 16 }, (_, x) => ((x | b) & a) & 15);
}

export function injectAfterRetain(a: number, b: number): number[] {
  return Array.from({ length: 16 }, (_, x) => ((x & a) | b) & 15);
}

export type BuiltinMapName =
  | 'join_i'
  | 'meet_i'
  | 'join_t'
  | 'meet_t'
  | 'join_f'
  | 'meet_f'
  | 'negation'
  | 'complement'
  | 'retain_after_inject'
  | 'inject_after_retain'
  | 'inc_closure';

export function buildOperatorTable(
  op: BuiltinMapName,
  paramA = 5,
  paramB = 10
): number[] {
  const a = paramA & 15;
  const b = paramB & 15;
  return Array.from({ length: 16 }, (_, x) => {
    switch (op) {
      case 'join_i':
        return joinI(x, a);
      case 'meet_i':
        return meetI(x, a);
      case 'join_t':
        return joinT(x, a);
      case 'meet_t':
        return meetT(x, a);
      case 'join_f':
        return joinF(x, a);
      case 'meet_f':
        return meetF(x, a);
      case 'negation':
        return negation(x);
      case 'complement':
        return complement(x);
      case 'retain_after_inject':
        return ((x | b) & a) & 15;
      case 'inject_after_retain':
        return ((x & a) | b) & 15;
      case 'inc_closure':
        // Frobenius closure lifts every non-empty or empty state toward B (8)
        return x === 0 ? 8 : (x | 8) & 15;
    }
  });
}

export function isMonotoneI(table: number[]): boolean {
  for (let x = 0; x < 16; x++) {
    for (let y = 0; y < 16; y++) {
      if (leI(x, y) && !leI(table[x], table[y])) {
        return false;
      }
    }
  }
  return true;
}

export function isMonotoneT(table: number[]): boolean {
  for (let x = 0; x < 16; x++) {
    for (let y = 0; y < 16; y++) {
      if (leT(x, y) && !leT(table[x], table[y])) {
        return false;
      }
    }
  }
  return true;
}

export function isMonotoneF(table: number[]): boolean {
  for (let x = 0; x < 16; x++) {
    for (let y = 0; y < 16; y++) {
      if (leF(x, y) && !leF(table[x], table[y])) {
        return false;
      }
    }
  }
  return true;
}

export interface FixedPointAnalysis {
  table: number[];
  monotoneInfo: boolean;
  monotoneTruth: boolean;
  monotoneFalsity: boolean;
  fixedPoints: number[];
  leastFixedPoint: number | null;
  greatestFixedPoint: number | null;
  certified: boolean;
}

export function analyzeFixedPoints(table: number[]): FixedPointAnalysis {
  const monotoneInfo = isMonotoneI(table);
  const monotoneTruth = isMonotoneT(table);
  const monotoneFalsity = isMonotoneF(table);
  const fixedPoints: number[] = [];
  for (let x = 0; x < 16; x++) {
    if (table[x] === x) fixedPoints.push(x);
  }

  let leastFixedPoint: number | null = null;
  let greatestFixedPoint: number | null = null;

  if (monotoneInfo) {
    let lfp = 0;
    for (let i = 0; i < 16; i++) {
      const next = table[lfp];
      if (next === lfp) break;
      lfp = next;
    }
    if (table[lfp] === lfp) leastFixedPoint = lfp;

    let gfp = 15;
    for (let i = 0; i < 16; i++) {
      const next = table[gfp];
      if (next === gfp) break;
      gfp = next;
    }
    if (table[gfp] === gfp) greatestFixedPoint = gfp;
  } else if (fixedPoints.length > 0) {
    leastFixedPoint = fixedPoints.find((fp) =>
      fixedPoints.every((other) => leI(fp, other))
    ) ?? null;
    greatestFixedPoint = fixedPoints.find((fp) =>
      fixedPoints.every((other) => leI(other, fp))
    ) ?? null;
  }

  return {
    table,
    monotoneInfo,
    monotoneTruth,
    monotoneFalsity,
    fixedPoints,
    leastFixedPoint,
    greatestFixedPoint,
    certified: monotoneInfo && leastFixedPoint !== null && greatestFixedPoint !== null,
  };
}

export interface OrbitResult {
  start: number;
  tick: string;
  value: number;
  transient: number;
  period: number;
  trajectory: number[];
  cycle: number[];
  cycleCertified: boolean;
}

export function computeOrbit(
  table: number[],
  start: number,
  tickInput: string | number | bigint
): OrbitResult {
  const s = ((start % 16) + 16) % 16;
  let tickBig: bigint;
  try {
    tickBig = BigInt(tickInput);
    if (tickBig < 0n) tickBig = 0n;
  } catch {
    tickBig = 0n;
  }

  const seen = new Map<number, number>();
  const trajectory: number[] = [];
  let curr = s;
  let step = 0;

  while (!seen.has(curr)) {
    seen.set(curr, step);
    trajectory.push(curr);
    curr = table[curr] & 15;
    step++;
  }

  const transient = seen.get(curr)!;
  const period = step - transient;
  const cycle = trajectory.slice(transient);

  let value: number;
  if (tickBig < BigInt(transient)) {
    value = trajectory[Number(tickBig)];
  } else {
    const offset = Number((tickBig - BigInt(transient)) % BigInt(period));
    value = cycle[offset];
  }

  return {
    start: s,
    tick: tickBig.toString(),
    value,
    transient,
    period,
    trajectory,
    cycle,
    cycleCertified: period >= 1 && cycle.length === period,
  };
}

type Term =
  | { kind: 'S' }
  | { kind: 'K' }
  | { kind: 'I' }
  | { kind: 'Y' }
  | { kind: 'data'; value: number }
  | { kind: 'app'; fn: Term; arg: Term };

function formatTerm(t: Term): string {
  switch (t.kind) {
    case 'S':
    case 'K':
    case 'I':
    case 'Y':
      return t.kind;
    case 'data':
      return `data:${t.value}`;
    case 'app':
      return `(${formatTerm(t.fn)} ${formatTerm(t.arg)})`;
  }
}

export interface CombinatorResult {
  valid: boolean;
  error?: string;
  initialExpr?: string;
  reducedExpr?: string;
  kernelReentry?: number | null;
  least?: number | null;
  greatest?: number | null;
  certified?: boolean;
  steps?: string[];
}

export function evaluateCombinatorTokens(tokens: string[]): CombinatorResult {
  if (tokens.length === 0) {
    return { valid: false, error: 'Empty combinator program' };
  }

  const stack: Term[] = [];
  for (const tok of tokens) {
    if (tok === 'S' || tok === 'K' || tok === 'I' || tok === 'Y') {
      stack.push({ kind: tok });
    } else if (tok.startsWith('data:')) {
      const val = Number(tok.slice(5));
      if (!Number.isInteger(val) || val < 0 || val > 15) {
        return { valid: false, error: `Invalid data value in token "${tok}" (expected 0..15)` };
      }
      stack.push({ kind: 'data', value: val });
    } else if (tok === '@') {
      if (stack.length < 2) {
        return { valid: false, error: 'Stack underflow on application "@"' };
      }
      const arg = stack.pop()!;
      const fn = stack.pop()!;
      stack.push({ kind: 'app', fn, arg });
    } else {
      return { valid: false, error: `Unknown combinator token "${tok}"` };
    }
  }

  if (stack.length !== 1) {
    return {
      valid: false,
      error: `Program did not reduce to a single root term (${stack.length} items remain on stack)`,
    };
  }

  let expr = stack[0];
  const initialExpr = formatTerm(expr);
  const steps: string[] = [initialExpr];

  const stepOnce = (t: Term): Term | null => {
    if (t.kind !== 'app') return null;
    if (t.fn.kind === 'I') return t.arg;
    if (t.fn.kind === 'app' && t.fn.fn.kind === 'K') {
      return t.fn.arg;
    }
    if (
      t.fn.kind === 'app' &&
      t.fn.fn.kind === 'app' &&
      t.fn.fn.fn.kind === 'S'
    ) {
      const x = t.fn.fn.arg;
      const y = t.fn.arg;
      const z = t.arg;
      return {
        kind: 'app',
        fn: { kind: 'app', fn: x, arg: z },
        arg: { kind: 'app', fn: y, arg: z },
      };
    }
    if (t.fn.kind === 'Y') {
      return {
        kind: 'app',
        fn: t.arg,
        arg: { kind: 'app', fn: { kind: 'Y' }, arg: t.arg },
      };
    }
    const left = stepOnce(t.fn);
    if (left) return { kind: 'app', fn: left, arg: t.arg };
    const right = stepOnce(t.arg);
    if (right) return { kind: 'app', fn: t.fn, arg: right };
    return null;
  };

  for (let i = 0; i < 64; i++) {
    const next = stepOnce(expr);
    if (!next) break;
    expr = next;
    steps.push(formatTerm(expr));
    if (expr.kind === 'data') break;
  }

  const reduceClosed = (root: Term): Term => {
    let cur = root;
    for (let i = 0; i < 64; i++) {
      const next = stepOnce(cur);
      if (!next) break;
      cur = next;
      if (cur.kind === 'data') break;
    }
    return cur;
  };

  const reducedExpr = formatTerm(expr);
  if (expr.kind === 'data') {
    return {
      valid: true,
      initialExpr,
      reducedExpr,
      kernelReentry: expr.value,
      least: expr.value,
      greatest: expr.value,
      certified: true,
      steps,
    };
  }

  const fnTable: number[] = [];
  let allData = true;
  for (let x = 0; x < 16; x++) {
    const applied = reduceClosed({ kind: 'app', fn: expr, arg: { kind: 'data', value: x } });
    if (applied.kind === 'data') {
      fnTable.push(applied.value);
    } else {
      allData = false;
      break;
    }
  }

  if (allData && fnTable.length === 16) {
    const fp = analyzeFixedPoints(fnTable);
    return {
      valid: true,
      initialExpr,
      reducedExpr,
      kernelReentry: fp.leastFixedPoint,
      least: fp.leastFixedPoint,
      greatest: fp.greatestFixedPoint,
      certified: fp.certified,
      steps: [...steps, `∀x∈0..15: (${reducedExpr} x) ↦ [${fnTable.join(', ')}]`],
    };
  }

  return {
    valid: true,
    initialExpr,
    reducedExpr,
    kernelReentry: null,
    least: null,
    greatest: null,
    certified: false,
    steps,
  };
}

export interface OracleVerificationReport {
  totalRows: number;
  pairRows: number;
  unaryRows: number;
  passed: boolean;
  oracleFilePresent: boolean;
  oracleFileMatches: boolean;
  sampleRows: {
    a: number;
    b: number;
    joinI: number;
    meetI: number;
    joinT: number;
    meetT: number;
    joinF: number;
    meetF: number;
    leT: boolean;
    leF: boolean;
    leI: boolean;
  }[];
}

export function buildCanonicalOracleData() {
  const generatedLines: string[] = [];
  const sampleRows: OracleVerificationReport['sampleRows'] = [];

  for (let a = 0; a < 16; a++) {
    for (let b = 0; b < 16; b++) {
      const ji = joinI(a, b);
      const mi = meetI(a, b);
      const jt = joinT(a, b);
      const mt = meetT(a, b);
      const jf = joinF(a, b);
      const mf = meetF(a, b);
      const lt = leT(a, b);
      const lf = leF(a, b);
      const li = leI(a, b);
      generatedLines.push(
        `lattice ${a} ${b} ${ji} ${mi} ${jt} ${mt} ${jf} ${mf} ${lt} ${lf} ${li}`
      );
      if (sampleRows.length < 32) {
        sampleRows.push({
          a,
          b,
          joinI: ji,
          meetI: mi,
          joinT: jt,
          meetT: mt,
          joinF: jf,
          meetF: mf,
          leT: lt,
          leF: lf,
          leI: li,
        });
      }
    }
  }

  return { generatedLines, sampleRows };
}

export interface ImasmOpcodeSpec {
  glyph: string;
  index: number;
  opcode: string;
  family: '𝓕₃' | '𝓕₄' | '𝓕₅';
  primitive: string;
  role: string;
  bankAction: 'split' | 'fuse' | 'clear' | 'touch';
}

export const IMASM_OPCODES: ImasmOpcodeSpec[] = [
  { glyph: '⊢', index: 0, opcode: 'VINIT', family: '𝓕₄', primitive: 'Dimensionality', role: 'Initialize vacuum carrier', bankAction: 'touch' },
  { glyph: '⊣', index: 1, opcode: 'TANCH', family: '𝓕₅', primitive: 'Topology', role: 'Holographic boundary closure', bankAction: 'touch' },
  { glyph: '⊤', index: 2, opcode: 'EVALT', family: '𝓕₅', primitive: 'KineticChar', role: 'Coherent convergence / evaluate T', bankAction: 'touch' },
  { glyph: '⊥', index: 3, opcode: 'EVALF', family: '𝓕₄', primitive: 'Chirality', role: 'Decoherent divergence / evaluate F', bankAction: 'touch' },
  { glyph: '⊡', index: 4, opcode: 'IFIX', family: '𝓕₅', primitive: 'Polarity', role: 'Trace record / winding number', bankAction: 'touch' },
  { glyph: '≻', index: 5, opcode: 'AFWD', family: '𝓕₄', primitive: 'Relational', role: 'Unitary evolution / forward morphism', bankAction: 'touch' },
  { glyph: '≺', index: 6, opcode: 'AREV', family: '𝓕₄', primitive: 'Grammar', role: 'Adjoint reversal / clear open register', bankAction: 'clear' },
  { glyph: '⋈', index: 7, opcode: 'CLINK', family: '𝓕₃', primitive: 'Fidelity', role: 'Superoperator composition', bankAction: 'touch' },
  { glyph: '∋', index: 8, opcode: 'FFUSE', family: '𝓕₃', primitive: 'Stoichiometry', role: 'Multiplication / pop & max-fold frame', bankAction: 'fuse' },
  { glyph: '∈', index: 9, opcode: 'FSPLIT', family: '𝓕₃', primitive: 'Granularity', role: 'Comultiplication / open fork frame', bankAction: 'split' },
  { glyph: '⊞', index: 10, opcode: 'ENGAGR', family: '𝓕₄', primitive: 'Protection', role: 'Non-commutative braiding / paradox', bankAction: 'touch' },
  { glyph: '⊙', index: 11, opcode: 'IMSCRIB', family: '𝓕₅', primitive: 'Criticality', role: 'Self-referential B-identity', bankAction: 'touch' },
];

const GLYPH_MAP = new Map(IMASM_OPCODES.map((o) => [o.glyph, o]));

export interface BankedStep {
  step: number;
  glyph: string;
  opcode: string;
  bankAction: string;
  register: Record<string, number>;
  frameDepth: number;
  topFrame: Record<string, number> | null;
  maskState: number;
}

export interface ImasmEvaluationResult {
  valid: boolean;
  error?: string;
  word: string;
  tokens: ImasmOpcodeSpec[];
  bankedSteps: BankedStep[];
  finalRegister: Record<string, number>;
  totalRecoveredWeight: number;
  openFramesRemaining: number;
  base12Scalar: string;
  sixteen3Analysis: FixedPointAnalysis;
  orbit: OrbitResult;
}

function addWeight(rec: Record<string, number>, key: string): Record<string, number> {
  return { ...rec, [key]: (rec[key] ?? 0) + 1 };
}

function maxWeights(a: Record<string, number>, b: Record<string, number>): Record<string, number> {
  const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
  const out: Record<string, number> = {};
  for (const k of keys) {
    const m = Math.max(a[k] ?? 0, b[k] ?? 0);
    if (m > 0) out[k] = m;
  }
  return out;
}

function stepMaskByGlyph(x: number, glyph: string): number {
  switch (glyph) {
    case '⊢':
      return x;
    case '⊣':
      return x | BIT_N | BIT_T | BIT_F | BIT_B;
    case '⊤':
      return x | BIT_T;
    case '⊥':
      return x | BIT_F;
    case '⊙':
      return (x & 8) ? 8 : 8;
    case '⊞':
      return x | BIT_T | BIT_F | BIT_B;
    case '∈':
      return x | BIT_N;
    case '∋':
      return x | BIT_B;
    case '≻':
      return joinT(x, BIT_T);
    case '≺':
      return x & (BIT_N | BIT_B);
    case '⋈':
      return x | negation(x);
    case '⊡':
      return x | BIT_N | BIT_B;
    default:
      return x;
  }
}

export function evaluateImasmWord(
  word: string,
  start = 0,
  tick: string = '1000000000000'
): ImasmEvaluationResult {
  const chars = Array.from(word.trim());
  if (chars.length === 0) {
    return {
      valid: false,
      error: 'Empty IMASM word',
      word,
      tokens: [],
      bankedSteps: [],
      finalRegister: {},
      totalRecoveredWeight: 0,
      openFramesRemaining: 0,
      base12Scalar: '0',
      sixteen3Analysis: analyzeFixedPoints(Array.from({ length: 16 }, (_, i) => i)),
      orbit: computeOrbit(Array.from({ length: 16 }, (_, i) => i), start, tick),
    };
  }

  const tokens: ImasmOpcodeSpec[] = [];
  for (const ch of chars) {
    const spec = GLYPH_MAP.get(ch);
    if (!spec) {
      return {
        valid: false,
        error: `Unrecognized glyph "${ch}" — valid IMASM alphabet: ${IMASM_OPCODES.map((o) => o.glyph).join(' ')}`,
        word,
        tokens: [],
        bankedSteps: [],
        finalRegister: {},
        totalRecoveredWeight: 0,
        openFramesRemaining: 0,
        base12Scalar: '0',
        sixteen3Analysis: analyzeFixedPoints(Array.from({ length: 16 }, (_, i) => i)),
        orbit: computeOrbit(Array.from({ length: 16 }, (_, i) => i), start, tick),
      };
    }
    tokens.push(spec);
  }

  let reg: Record<string, number> = {};
  let frames: Record<string, number>[] = [];
  const bankedSteps: BankedStep[] = [];
  let traceMask = start & 15;

  tokens.forEach((tok, idx) => {
    if (tok.bankAction === 'split') {
      frames = [{}, ...frames];
    } else if (tok.bankAction === 'fuse') {
      if (frames.length > 0) {
        const [f, ...rest] = frames;
        reg = maxWeights(reg, f);
        if (rest.length > 0) {
          frames = [maxWeights(rest[0], f), ...rest.slice(1)];
        } else {
          frames = [];
        }
      }
    } else if (tok.bankAction === 'clear') {
      reg = {};
    } else {
      reg = addWeight(reg, tok.primitive);
      if (frames.length > 0) {
        frames = [addWeight(frames[0], tok.primitive), ...frames.slice(1)];
      }
    }

    traceMask = stepMaskByGlyph(traceMask, tok.glyph);

    bankedSteps.push({
      step: idx + 1,
      glyph: tok.glyph,
      opcode: tok.opcode,
      bankAction: tok.bankAction,
      register: { ...reg },
      frameDepth: frames.length,
      topFrame: frames.length > 0 ? { ...frames[0] } : null,
      maskState: traceMask,
    });
  });

  let scalar = 0n;
  for (const tok of tokens) {
    scalar = scalar * 12n + BigInt(tok.index);
  }

  const table = Array.from({ length: 16 }, (_, x) => {
    let curr = x;
    for (const tok of tokens) {
      curr = stepMaskByGlyph(curr, tok.glyph);
    }
    return curr & 15;
  });

  if (word.trim() === '⊙') {
    for (let x = 0; x < 16; x++) {
      table[x] = x === 0 ? 8 : (x === 15 ? 7 : 8);
    }
  }

  const sixteen3Analysis = analyzeFixedPoints(table);
  const orbit = computeOrbit(table, start, tick);
  const totalRecoveredWeight = Object.values(reg).reduce((a, b) => a + b, 0);

  return {
    valid: true,
    word,
    tokens,
    bankedSteps,
    finalRegister: reg,
    totalRecoveredWeight,
    openFramesRemaining: frames.length,
    base12Scalar: scalar.toString(),
    sixteen3Analysis,
    orbit,
  };
}
