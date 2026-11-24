export type Belnap = 'N' | 'T' | 'F' | 'B';

export const BELNAP_VALUES: Belnap[] = ['N', 'T', 'F', 'B'];

export function band(a: Belnap, b: Belnap): Belnap {
  if (a === 'F' || b === 'F') return 'F';
  if (a === 'N' || b === 'N') return 'N';
  if (a === 'B' || b === 'B') return 'B';
  return 'T';
}

export function bor(a: Belnap, b: Belnap): Belnap {
  if (a === 'T' || b === 'T') return 'T';
  if (a === 'B' || b === 'B') return 'B';
  if (a === 'N' || b === 'N') return 'N';
  return 'F';
}

export function bnot(a: Belnap): Belnap {
  if (a === 'T') return 'F';
  if (a === 'F') return 'T';
  return a;
}

export function truthLE(a: Belnap, b: Belnap): boolean {
  if (a === 'F' || b === 'T') return true;
  return a === b;
}

export function infoLE(a: Belnap, b: Belnap): boolean {
  if (a === 'N' || b === 'B') return true;
  return a === b;
}

export function tmeet(a: Belnap, b: Belnap): Belnap {
  if (a === b) return a;
  if (a === 'T') return b;
  if (b === 'T') return a;
  return 'F';
}

export function tjoin(a: Belnap, b: Belnap): Belnap {
  if (a === b) return a;
  if (a === 'F') return b;
  if (b === 'F') return a;
  return 'T';
}

export function inc(_s: Belnap): Belnap {
  return 'B';
}

export function isClassical(v: Belnap): boolean {
  return v !== 'B';
}

export function classicalSwitch(v: Belnap): Belnap {
  return v === 'B' ? 'F' : v;
}

export function inCentre(v: Belnap): boolean {
  return tjoin(v, bnot(v)) === 'T';
}

export function boolSwitch(v: Belnap): Belnap {
  return v === 'T' ? 'T' : 'F';
}

export interface BelnapTheoremAudit {
  frobeniusClosureHolds: boolean;
  frobeniusWitnesses: { s: Belnap; incS: Belnap; incIncS: Belnap; equal: boolean }[];
  excludedMiddleResults: { v: Belnap; notV: Belnap; tjoinVNotV: Belnap; inCentre: boolean; isClassical: boolean }[];
  theTwoCutsDifferAtN: boolean;
  classicalRestrictionAdjunctionHolds: boolean;
  classicalReverseAdjunctionFailsAtB: boolean;
  booleanCentreAdjunctionHolds: boolean;
  booleanCentreReverseAdjunctionFailsAtN: boolean;
  infoAdjunctionFails: boolean;
  tables: {
    band: Record<Belnap, Record<Belnap, Belnap>>;
    bor: Record<Belnap, Record<Belnap, Belnap>>;
    tmeet: Record<Belnap, Record<Belnap, Belnap>>;
    tjoin: Record<Belnap, Record<Belnap, Belnap>>;
  };
}

function makeTable(fn: (a: Belnap, b: Belnap) => Belnap): Record<Belnap, Record<Belnap, Belnap>> {
  const out = {} as Record<Belnap, Record<Belnap, Belnap>>;
  for (const a of BELNAP_VALUES) {
    out[a] = {} as Record<Belnap, Belnap>;
    for (const b of BELNAP_VALUES) {
      out[a][b] = fn(a, b);
    }
  }
  return out;
}

export function auditBelnapTheorems(): BelnapTheoremAudit {
  const frobeniusWitnesses = BELNAP_VALUES.map((s) => {
    const incS = inc(s);
    const incIncS = inc(incS);
    return { s, incS, incIncS, equal: incS === incIncS };
  });

  const excludedMiddleResults = BELNAP_VALUES.map((v) => {
    const notV = bnot(v);
    const tjoinVNotV = tjoin(v, notV);
    return {
      v,
      notV,
      tjoinVNotV,
      inCentre: inCentre(v),
      isClassical: isClassical(v),
    };
  });

  const classicalRestrictionAdjunctionHolds = BELNAP_VALUES.filter(isClassical).every((c) =>
    BELNAP_VALUES.every((x) => truthLE(c, x) === truthLE(c, classicalSwitch(x)))
  );

  const classicalReverseAdjunctionFailsAtB =
    truthLE(classicalSwitch('B'), 'F') !== truthLE('B', 'F');

  const booleanCentreAdjunctionHolds = BELNAP_VALUES.filter(inCentre).every((c) =>
    BELNAP_VALUES.every((x) => truthLE(c, x) === truthLE(c, boolSwitch(x)))
  );

  const booleanCentreReverseAdjunctionFailsAtN =
    truthLE(boolSwitch('N'), 'F') !== truthLE('N', 'F');

  const infoAdjunctionFails =
    infoLE('T', 'B') !== infoLE('T', boolSwitch('B'));

  return {
    frobeniusClosureHolds: frobeniusWitnesses.every((w) => w.equal),
    frobeniusWitnesses,
    excludedMiddleResults,
    theTwoCutsDifferAtN: isClassical('N') && !inCentre('N'),
    classicalRestrictionAdjunctionHolds,
    classicalReverseAdjunctionFailsAtB,
    booleanCentreAdjunctionHolds,
    booleanCentreReverseAdjunctionFailsAtN,
    infoAdjunctionFails,
    tables: {
      band: makeTable(band),
      bor: makeTable(bor),
      tmeet: makeTable(tmeet),
      tjoin: makeTable(tjoin),
    },
  };
}
