import { describeMask } from './sixteen3.ts';

export interface EvidenceJudgment {
  support: 0 | 1;
  refutation: 0 | 1;
  belnap: 'N' | 'T' | 'F' | 'B';
}

export interface OrganismCompartment {
  id: string;
  depth: number;
  mask: number;
  label: string;
  phase: string;
  evidence: EvidenceJudgment;
  parentMask: number;
}

export interface OrganismCycleTrace {
  steps: number;
  initialMask: number;
  compartments: OrganismCompartment[];
  constitutiveSequence: number[];
  closedToB: boolean;
}

const CONSTITUTIVE_MASKS = [8, 0, 1, 3, 7, 15, 8];
const PHASE_NAMES = [
  'Enclosing B',
  'Opened empty interior',
  'Interior containing N',
  'Articulation {N,T}',
  'Articulation {N,T,F}',
  'Complete interior {N,T,F,B}',
  'Returned to enclosing B',
];

function judgmentForMask(mask: number): EvidenceJudgment {
  const hasT = (mask & 2) !== 0;
  const hasF = (mask & 4) !== 0;
  const hasB = (mask & 8) !== 0;
  const support: 0 | 1 = hasT || hasB ? 1 : 0;
  const refutation: 0 | 1 = hasF || hasB ? 1 : 0;
  let belnap: 'N' | 'T' | 'F' | 'B' = 'N';
  if (support === 1 && refutation === 1) belnap = 'B';
  else if (support === 1) belnap = 'T';
  else if (refutation === 1) belnap = 'F';
  return { support, refutation, belnap };
}

export function simulateOrganismCycle(steps = 12, startMask = 8): OrganismCycleTrace {
  const clampedSteps = Math.max(1, Math.min(48, Math.floor(steps)));
  const startIdx = Math.max(0, CONSTITUTIVE_MASKS.indexOf(startMask & 15));
  const compartments: OrganismCompartment[] = [];

  for (let i = 0; i < clampedSteps; i++) {
    const cyclePos = (startIdx + i) % (CONSTITUTIVE_MASKS.length - 1);
    const mask = CONSTITUTIVE_MASKS[cyclePos];
    const info = describeMask(mask);
    compartments.push({
      id: `comp-${i}`,
      depth: mask === 8 ? 0 : Math.floor(i / 6) + 1,
      mask,
      label: info.label,
      phase: PHASE_NAMES[cyclePos],
      evidence: judgmentForMask(mask),
      parentMask: i === 0 ? startMask & 15 : compartments[i - 1].mask,
    });
  }

  return {
    steps: clampedSteps,
    initialMask: startMask & 15,
    compartments,
    constitutiveSequence: CONSTITUTIVE_MASKS,
    closedToB: compartments[compartments.length - 1]?.mask === 8,
  };
}

export interface OddCosetReport {
  valid: boolean;
  error?: string;
  n: string;
  bitWidth: number;
  m: number;
  modulus2m: string;
  nMod2m: string;
  cosets: {
    pResidue: string;
    qResidue: string;
    productMod2m: string;
    delta: string;
    matchesNMod2m: boolean;
  }[];
  trialFactor?: { p: string; q: string } | null;
}

function modInversePow2(a: bigint, mod: bigint): bigint {
  let t = 0n;
  let newT = 1n;
  let r = mod;
  let newR = ((a % mod) + mod) % mod;
  while (newR !== 0n) {
    const q = r / newR;
    [t, newT] = [newT, t - q * newT];
    [r, newR] = [newR, r - q * newR];
  }
  return t < 0n ? t + mod : t;
}

export function analyzeToroidalSource(sourceInput: string): OddCosetReport {
  const cleaned = sourceInput.trim();
  if (!/^\d+$/.test(cleaned)) {
    return {
      valid: false,
      error: 'Source N must be a positive odd decimal integer',
      n: cleaned,
      bitWidth: 0,
      m: 0,
      modulus2m: '0',
      nMod2m: '0',
      cosets: [],
    };
  }

  const N = BigInt(cleaned);
  if (N < 3n || N % 2n === 0n) {
    return {
      valid: false,
      error: 'Toroidal division requires an odd integer N ≥ 3',
      n: N.toString(),
      bitWidth: N.toString(2).length,
      m: 0,
      modulus2m: '0',
      nMod2m: '0',
      cosets: [],
    };
  }

  const bitWidth = N.toString(2).length;
  const m = Math.max(2, Math.min(16, Math.ceil(bitWidth / 2)));
  const mod = 1n << BigInt(m);
  const nMod = N % mod;

  const sampleP = [1n, 3n, 5n, 7n].map((r) => (r < mod ? r : r % mod));
  const cosets = sampleP.map((pRes) => {
    const qRes = (nMod * modInversePow2(pRes, mod)) % mod;
    const prod = (pRes * qRes) % mod;
    const delta = prod - nMod;
    return {
      pResidue: pRes.toString(),
      qResidue: qRes.toString(),
      productMod2m: prod.toString(),
      delta: delta.toString(),
      matchesNMod2m: prod === nMod,
    };
  });

  let trialFactor: { p: string; q: string } | null = null;
  if (bitWidth <= 40) {
    for (let d = 3n; d * d <= N && d <= 1048576n; d += 2n) {
      if (N % d === 0n) {
        trialFactor = { p: d.toString(), q: (N / d).toString() };
        break;
      }
    }
  }

  return {
    valid: true,
    n: N.toString(),
    bitWidth,
    m,
    modulus2m: mod.toString(),
    nMod2m: nMod.toString(),
    cosets,
    trialFactor,
  };
}
