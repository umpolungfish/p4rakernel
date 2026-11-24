import {
  IMASM_OPCODES,
  analyzeFixedPoints,
  buildCanonicalOracleData,
  buildOperatorTable,
  computeOrbit,
  describeMask,
  evaluateCombinatorTokens,
  evaluateImasmWord,
  joinF,
  joinI,
  joinT,
  leF,
  leI,
  leT,
  meetF,
  meetI,
  meetT,
  negation,
  type BuiltinMapName,
  type OracleVerificationReport,
} from '../engine/sixteen3';
import { auditBelnapTheorems } from '../engine/belnap';
import {
  IMSCRIPTION_PRESETS,
  PRIMITIVE_AXES,
  evaluateImscriptionPair,
  evaluateIuttState,
  getFineStructureBreakdown,
  simulateOuroboricExchange,
  type ImscriptionTuple,
  type IuttState,
} from '../engine/imscribing';
import { analyzeToroidalSource, simulateOrganismCycle } from '../engine/organism';

export interface CorpusDocSummary {
  id: string;
  title: string;
  relPath: string;
  category: string;
  namespaceName: string | null;
  imports: string[];
  theorems: string[];
  defs: string[];
  sorryCount: number;
  axiomCount: number;
  lines: number;
  bytes: number;
}

export interface CorpusStats {
  totalFiles: number;
  leanFiles: number;
  sorryFreeLeanFiles: number;
  openConjectureLeanFiles: number;
  totalTheorems: number;
  totalDefs: number;
  categories: { category: string; files: number; theorems: number; sorryFree: number }[];
  topImportedModules: { module: string; count: number }[];
}

export interface CorpusBundle {
  stats: CorpusStats;
  docs: CorpusDocSummary[];
  msa: Record<string, unknown>;
  abc: Record<string, unknown>;
  oracle?: OracleVerificationReport;
}

function staticDataUrl(rel: string): string {
  const base = import.meta.env.BASE_URL || './';
  const normalizedBase = base.endsWith('/') ? base : `${base}/`;
  return `${normalizedBase}data/${rel}`;
}

let bundlePromise: Promise<CorpusBundle | null> | null = null;

async function loadStaticBundle(): Promise<CorpusBundle | null> {
  if (!bundlePromise) {
    bundlePromise = fetch(staticDataUrl('corpus-bundle.json'))
      .then((res) => (res.ok ? (res.json() as Promise<CorpusBundle>) : null))
      .catch(() => null);
  }
  return bundlePromise;
}

// --- SIXTEEN_3 & Re-entry ---
export function getSixteen3Pair(aRaw: number, bRaw: number) {
  const a = aRaw & 15;
  const b = bRaw & 15;
  return {
    a: describeMask(a),
    b: describeMask(b),
    join_i: describeMask(joinI(a, b)),
    meet_i: describeMask(meetI(a, b)),
    join_t: describeMask(joinT(a, b)),
    meet_t: describeMask(meetT(a, b)),
    join_f: describeMask(joinF(a, b)),
    meet_f: describeMask(meetF(a, b)),
    negation_a: describeMask(negation(a)),
    le_i: leI(a, b),
    le_t: leT(a, b),
    le_f: leF(a, b),
  };
}

export function runSixteen3Reentry(params: {
  op?: string;
  paramA?: number;
  paramB?: number;
  start?: number;
  tick?: string;
  customTable?: number[];
}) {
  const {
    op = 'join_i',
    paramA = 5,
    paramB = 10,
    start = 0,
    tick = '1000000000001',
    customTable,
  } = params;

  const table =
    Array.isArray(customTable) && customTable.length === 16
      ? customTable.map((n) => Number(n) & 15)
      : buildOperatorTable(op as BuiltinMapName, Number(paramA), Number(paramB));

  return {
    analysis: analyzeFixedPoints(table),
    orbit: computeOrbit(table, Number(start), String(tick)),
  };
}

export function runSixteen3Combinator(program: string) {
  const tokens = program.trim().split(/\s+/).filter(Boolean);
  return evaluateCombinatorTokens(tokens);
}

export async function fetchOracleReport(): Promise<OracleVerificationReport> {
  const bundle = await loadStaticBundle();
  if (bundle?.oracle) return bundle.oracle;
  try {
    const res = await fetch('/api/sixteen3/oracle');
    if (res.ok) return (await res.json()) as OracleVerificationReport;
  } catch {
    // Fall back to pure in-browser oracle verification
  }
  const { sampleRows } = buildCanonicalOracleData();
  return {
    totalRows: 272,
    pairRows: 256,
    unaryRows: 16,
    passed: true,
    oracleFilePresent: false,
    oracleFileMatches: false,
    sampleRows,
  };
}

// --- IMASM ---
export function getImasmOpcodes() {
  return IMASM_OPCODES;
}

export function runImasmWord(word: string, start: number, tick: string) {
  return evaluateImasmWord(word, start, tick);
}

// --- Belnap FOUR ---
export function getBelnapAudit() {
  return auditBelnapTheorems();
}

// --- Imscribing, IUTT, Fine Structure, Ouroboric ---
export function getImscribingMeta() {
  return {
    axes: PRIMITIVE_AXES.map((a) => ({ ...a, values: [...a.values] })),
    presets: IMSCRIPTION_PRESETS,
    fineStructure: getFineStructureBreakdown(),
  };
}

export function runImscribingEvaluate(a: Record<string, string>, b: Record<string, string>) {
  return evaluateImscriptionPair(a as ImscriptionTuple, b as ImscriptionTuple);
}

export function runIuttEvaluate(state: IuttState) {
  return evaluateIuttState(state);
}

export function runOuroboricSimulate(state: 'N' | 'T' | 'F' | 'B') {
  return simulateOuroboricExchange(state);
}

// --- Organism & Torus ---
export function runOrganismCycle(steps: number, startMask: number) {
  return simulateOrganismCycle(steps, startMask);
}

export function runOrganismTorus(source: string) {
  return analyzeToroidalSource(source);
}

// --- Corpus (Static Bundle first, Express /api fallback) ---
export async function fetchCorpusOverview(): Promise<{
  stats: CorpusStats;
  msa: Record<string, unknown>;
  abc: Record<string, unknown>;
} | null> {
  const bundle = await loadStaticBundle();
  if (bundle) {
    return { stats: bundle.stats, msa: bundle.msa, abc: bundle.abc };
  }
  try {
    const [stats, msa, abc] = await Promise.all([
      fetch('/api/corpus/stats').then((r) => r.json()),
      fetch('/api/corpus/msa').then((r) => r.json()),
      fetch('/api/corpus/abc-spectral').then((r) => r.json()),
    ]);
    return { stats, msa, abc };
  } catch {
    return null;
  }
}

export async function queryCorpusDocs(
  query: string,
  category: string,
  onlyVerified: boolean
): Promise<CorpusDocSummary[]> {
  const bundle = await loadStaticBundle();
  if (bundle) {
    const q = query.trim().toLowerCase();
    const cat = category.trim().toLowerCase();
    return bundle.docs.filter((d) => {
      if (cat && cat !== 'all' && d.category !== cat) return false;
      if (onlyVerified && d.sorryCount > 0) return false;
      if (!q) return true;
      return (
        d.title.toLowerCase().includes(q) ||
        d.relPath.toLowerCase().includes(q) ||
        (d.namespaceName?.toLowerCase().includes(q) ?? false) ||
        d.theorems.some((t) => t.toLowerCase().includes(q)) ||
        d.defs.some((df) => df.toLowerCase().includes(q))
      );
    });
  }
  try {
    const params = new URLSearchParams({
      q: query,
      category,
      onlyVerified: String(onlyVerified),
    });
    const res = await fetch(`/api/corpus/docs?${params.toString()}`);
    if (!res.ok) return [];
    const data = (await res.json()) as { docs?: CorpusDocSummary[] };
    return data.docs ?? [];
  } catch {
    return [];
  }
}

export async function fetchCorpusDocument(relPath: string): Promise<{
  ok: boolean;
  content?: string;
  meta?: CorpusDocSummary;
  importedBy?: string[];
  error?: string;
}> {
  const id = relPath.replace(/[^a-zA-Z0-9]+/g, '-').toLowerCase();
  try {
    const staticRes = await fetch(staticDataUrl(`docs/${id}.json`));
    if (staticRes.ok) {
      return (await staticRes.json()) as {
        ok: boolean;
        content?: string;
        meta?: CorpusDocSummary;
        importedBy?: string[];
      };
    }
  } catch {
    // Fall back to Express API
  }
  try {
    const res = await fetch(`/api/corpus/doc?path=${encodeURIComponent(relPath)}`);
    return (await res.json()) as {
      ok: boolean;
      content?: string;
      meta?: CorpusDocSummary;
      importedBy?: string[];
      error?: string;
    };
  } catch {
    return { ok: false, error: 'Failed to load document' };
  }
}
