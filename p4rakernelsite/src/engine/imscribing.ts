export const PRIMITIVE_AXES = [
  { key: 'dim', symbol: 'D', name: 'Dimensionality', values: ['𐑛', '𐑨', '𐑼', '𐑦'] },
  { key: 'top', symbol: 'T', name: 'Topology', values: ['𐑡', '𐑰', '𐑥', '𐑶', '𐑸'] },
  { key: 'rel', symbol: 'R', name: 'Relational', values: ['𐑩', '𐑽', '𐑑', '𐑾'] },
  { key: 'pol', symbol: 'P', name: 'Polarity', values: ['𐑗', '𐑿', '𐑯', '𐑬', '𐑹'] },
  { key: 'fid', symbol: 'F', name: 'Fidelity', values: ['𐑱', '𐑞', '𐑐'] },
  { key: 'kin', symbol: 'K', name: 'KineticChar', values: ['𐑘', '𐑤', '𐑧', '𐑺', '𐑪'] },
  { key: 'gran', symbol: 'G', name: 'Granularity', values: ['𐑚', '𐑔', '𐑲'] },
  { key: 'gram', symbol: 'Γ', name: 'Grammar', values: ['𐑝', '𐑜', '𐑠', '𐑵'] },
  { key: 'crit', symbol: 'Φ', name: 'Criticality', values: ['𐑢', '⊙', '𐑮', '𐑻', '𐑣'] },
  { key: 'chir', symbol: 'H', name: 'Chirality', values: ['𐑓', '𐑒', '𐑖', '𐑫'] },
  { key: 'stoi', symbol: 'S', name: 'Stoichiometry', values: ['𐑙', '𐑕', '𐑳'] },
  { key: 'prot', symbol: 'Ω', name: 'Protection', values: ['𐑷', '𐑴', '𐑭', '𐑟'] },
] as const;

export type PrimitiveKey = (typeof PRIMITIVE_AXES)[number]['key'];
export type ImscriptionTuple = Record<PrimitiveKey, string>;

export const IMSCRIPTION_PRESETS: Record<string, { label: string; source: string; tuple: ImscriptionTuple }> = {
  frobenius_bottom: {
    label: 'Frobenius Bottom (⊥)',
    source: 'Frobenius.lean · HowNaturalNumbersArise.lean',
    tuple: {
      dim: '𐑛', top: '𐑡', rel: '𐑩', pol: '𐑗',
      fid: '𐑱', kin: '𐑘', gran: '𐑚', gram: '𐑝',
      crit: '𐑢', chir: '𐑓', stoi: '𐑙', prot: '𐑷',
    },
  },
  human_brain: {
    label: 'Human Brain (C=1)',
    source: 'Consciousness.lean',
    tuple: {
      dim: '𐑨', top: '𐑶', rel: '𐑾', pol: '𐑹',
      fid: '𐑐', kin: '𐑧', gran: '𐑲', gram: '𐑠',
      crit: '⊙', chir: '𐑖', stoi: '𐑙', prot: '𐑭',
    },
  },
  replicative_core: {
    label: 'Replicative Core (L9₀)',
    source: 'CL9NK_Chain.lean',
    tuple: {
      dim: '𐑛', top: '𐑥', rel: '𐑑', pol: '𐑬',
      fid: '𐑐', kin: '𐑪', gran: '𐑔', gram: '𐑝',
      crit: '⊙', chir: '𐑫', stoi: '𐑳', prot: '𐑭',
    },
  },
  compton_split_radius: {
    label: 'Compton Split Radius',
    source: 'CatalogImmutability.lean',
    tuple: {
      dim: '𐑨', top: '𐑸', rel: '𐑽', pol: '𐑬',
      fid: '𐑐', kin: '𐑧', gran: '𐑚', gram: '𐑵',
      crit: '⊙', chir: '𐑖', stoi: '𐑳', prot: '𐑴',
    },
  },
  dark_energy: {
    label: 'Dark Energy',
    source: 'CatalogImmutability.lean',
    tuple: {
      dim: '𐑦', top: '𐑸', rel: '𐑽', pol: '𐑯',
      fid: '𐑐', kin: '𐑧', gran: '𐑚', gram: '𐑵',
      crit: '⊙', chir: '𐑫', stoi: '𐑳', prot: '𐑴',
    },
  },
  frobenius_top: {
    label: 'Frobenius Top (⊤)',
    source: 'Frobenius.lean',
    tuple: {
      dim: '𐑦', top: '𐑸', rel: '𐑾', pol: '𐑹',
      fid: '𐑐', kin: '𐑪', gran: '𐑲', gram: '𐑵',
      crit: '𐑣', chir: '𐑫', stoi: '𐑳', prot: '𐑟',
    },
  },
};

function idxOf(key: PrimitiveKey, val: string): number {
  const axis = PRIMITIVE_AXES.find((a) => a.key === key)!;
  const idx = (axis.values as readonly string[]).indexOf(val);
  return idx >= 0 ? idx : 0;
}

export function computeMeet(a: ImscriptionTuple, b: ImscriptionTuple): ImscriptionTuple {
  const out = {} as ImscriptionTuple;
  for (const axis of PRIMITIVE_AXES) {
    const ia = idxOf(axis.key, a[axis.key]);
    const ib = idxOf(axis.key, b[axis.key]);
    out[axis.key] = ia < ib ? a[axis.key] : b[axis.key];
  }
  return out;
}

export function computeJoin(a: ImscriptionTuple, b: ImscriptionTuple): ImscriptionTuple {
  const out = {} as ImscriptionTuple;
  for (const axis of PRIMITIVE_AXES) {
    const ia = idxOf(axis.key, a[axis.key]);
    const ib = idxOf(axis.key, b[axis.key]);
    out[axis.key] = ia < ib ? b[axis.key] : a[axis.key];
  }
  return out;
}

export function computeTensor(a: ImscriptionTuple, b: ImscriptionTuple): ImscriptionTuple {
  const out = {} as ImscriptionTuple;
  for (const axis of PRIMITIVE_AXES) {
    const ia = idxOf(axis.key, a[axis.key]);
    const ib = idxOf(axis.key, b[axis.key]);
    if (axis.key === 'pol' || axis.key === 'fid') {
      out[axis.key] = ia < ib ? a[axis.key] : b[axis.key];
    } else {
      out[axis.key] = ia < ib ? b[axis.key] : a[axis.key];
    }
  }
  return out;
}

export function primitiveConflicts(a: ImscriptionTuple, b: ImscriptionTuple): string[] {
  const conflicts: string[] = [];
  for (const axis of PRIMITIVE_AXES) {
    if (a[axis.key] !== b[axis.key]) {
      conflicts.push(axis.symbol);
    }
  }
  return conflicts;
}

export function primitiveDistance(a: ImscriptionTuple, b: ImscriptionTuple): number {
  let sqsum = 0;
  for (const axis of PRIMITIVE_AXES) {
    const d = idxOf(axis.key, a[axis.key]) - idxOf(axis.key, b[axis.key]);
    sqsum += d * d;
  }
  return sqsum / 12;
}

export function consciousnessScore(s: ImscriptionTuple): {
  phiCGate: boolean;
  kSlowGate: boolean;
  score: number;
} {
  const phiCGate = s.crit !== '𐑢';
  const kSlowGate = s.kin === '𐑘' || s.kin === '𐑤' || s.kin === '𐑧';
  const score = phiCGate ? (kSlowGate ? 1 : 0.5) : 0;
  return { phiCGate, kSlowGate, score };
}

export function evaluateImscriptionPair(a: ImscriptionTuple, b: ImscriptionTuple) {
  const bottom = IMSCRIPTION_PRESETS.frobenius_bottom.tuple;
  const meet = computeMeet(a, b);
  const join = computeJoin(a, b);
  const tensor = computeTensor(a, b);
  const conflicts = primitiveConflicts(a, b);
  const distance = primitiveDistance(a, b);

  const frobA = JSON.stringify(computeTensor(a, a)) === JSON.stringify(a);
  const frobB = JSON.stringify(computeMeet(a, a)) === JSON.stringify(a);
  const frobD = JSON.stringify(computeJoin(bottom, a)) === JSON.stringify(a);

  const probA = primitiveConflicts(bottom, a).length / 12;
  const probB = primitiveConflicts(bottom, b).length / 12;

  return {
    a,
    b,
    meet,
    join,
    tensor,
    conflicts,
    hammingDistance: conflicts.length,
    primitiveDistance: Number(distance.toFixed(6)),
    consciousnessA: consciousnessScore(a),
    consciousnessB: consciousnessScore(b),
    probA: Number(probA.toFixed(4)),
    probB: Number(probB.toFixed(4)),
    frobeniusLaws: {
      muDeltaA_id: frobA,
      muDeltaB_id: frobB,
      muDeltaD_id: frobD,
    },
  };
}

export interface IuttState {
  bigT: boolean;
  bigF: boolean;
  smallT: boolean;
  smallF: boolean;
}

export function evaluateIuttState(x: IuttState) {
  const intersect = (u: IuttState, v: IuttState): IuttState => ({
    bigT: u.bigT && v.bigT,
    bigF: u.bigF && v.bigF,
    smallT: u.smallT && v.smallT,
    smallF: u.smallF && v.smallF,
  });
  const union = (u: IuttState, v: IuttState): IuttState => ({
    bigT: u.bigT || v.bigT,
    bigF: u.bigF || v.bigF,
    smallT: u.smallT || v.smallT,
    smallF: u.smallF || v.smallF,
  });

  const both: IuttState = { bigT: true, bigF: true, smallT: false, smallF: false };
  const truth: IuttState = { bigT: true, bigF: false, smallT: false, smallF: false };
  const falsity: IuttState = { bigT: false, bigF: true, smallT: false, smallF: false };
  const ambient: IuttState = { bigT: false, bigF: false, smallT: true, smallF: true };

  const erased = intersect(x, both);
  const truthPart = intersect(x, truth);
  const infoPart = intersect(x, ambient);
  const falsePart = intersect(x, falsity);
  const ternaryRecovered = union(union(truthPart, infoPart), falsePart);

  let booleanShadow: 'T' | 'F' = 'F';
  if (erased.bigT && !erased.bigF) booleanShadow = 'T';

  const toFourLabel =
    erased.bigT && erased.bigF ? 'B' : erased.bigT ? 'T' : erased.bigF ? 'F' : 'N';

  const atOne = [0, 1, 0];
  const atTwo = [0, 0, 1];
  const blindScalar = (v: number[]) => v.reduce((s, n) => s + n, 0);
  const weightedVal = (v: number[]) => v.reduce((s, n, j) => s + j * j * n, 0);

  return {
    input: x,
    erased,
    toFourLabel,
    booleanShadow,
    ternaryDecomposition: { truthPart, infoPart, falsePart, matchesInput: JSON.stringify(ternaryRecovered) === JSON.stringify(x) },
    erasureIdempotent: JSON.stringify(intersect(erased, both)) === JSON.stringify(erased),
    filtrationObstruction: {
      atOne: { vec: atOne, degree: 1, blindScalar: blindScalar(atOne), weightedJ2: weightedVal(atOne) },
      atTwo: { vec: atTwo, degree: 2, blindScalar: blindScalar(atTwo), weightedJ2: weightedVal(atTwo) },
      sameBlindScalar: blindScalar(atOne) === blindScalar(atTwo),
      distinctWeightedValues: weightedVal(atOne) !== weightedVal(atTwo),
    },
  };
}

export function getFineStructureBreakdown() {
  const d = 12;
  const dSq = d * d;
  const cartanAxes = 7;
  const integerCore = dSq - cartanAxes;
  const tiltCorrection = Math.atan(0.25) / (4 * Math.sqrt(3));
  let alphaInv = integerCore + tiltCorrection;
  for (let i = 0; i < 6; i++) {
    const alpha = 1 / alphaInv;
    alphaInv = integerCore + tiltCorrection + alpha * alpha * d;
  }
  const broadcastTerm = (1 / alphaInv) ** 2 * d;
  const codata2022 = 137.035999084;
  const residual = Math.abs(alphaInv - codata2022);
  const ppm = (residual / codata2022) * 1e6;

  return {
    d,
    dSq,
    cartanAxes,
    nonAbelianAxes: d - cartanAxes,
    integerCore,
    tiltCorrection: Number(tiltCorrection.toFixed(12)),
    broadcastTerm: Number(broadcastTerm.toFixed(12)),
    computedAlphaInv: Number(alphaInv.toFixed(9)),
    codata2022,
    residual: Number(residual.toFixed(12)),
    ppm: Number(ppm.toFixed(4)),
  };
}

export function simulateOuroboricExchange(state: 'N' | 'T' | 'F' | 'B') {
  const coreflect = (s: 'N' | 'T' | 'F' | 'B'): 'T' | 'F' => {
    if (s === 'T' || s === 'B') return 'T';
    return 'F';
  };
  const infoMass = (s: 'N' | 'T' | 'F' | 'B'): number => (s === 'N' || s === 'B' ? 1 : 0);

  const eveObserved = coreflect(state);
  const aliceMass = infoMass(state);
  const eveMass = infoMass(eveObserved);
  return {
    transmitted: state,
    aliceInfoMass: aliceMass,
    eveCoreflected: eveObserved,
    eveInfoMass: eveMass,
    tamperDetected: eveMass < aliceMass,
    bobAmbientRead: state,
    bobInfoMass: aliceMass,
    losslessForBob: true,
  };
}
