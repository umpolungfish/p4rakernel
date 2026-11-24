import fs from 'node:fs';
import path from 'node:path';

export interface CorpusDocumentSummary {
  id: string;
  title: string;
  relPath: string;
  category:
    | 'core'
    | 'audit'
    | 'millennium'
    | 'erdos'
    | 'biochem'
    | 'classical'
    | 'imasm'
    | 'emergence'
    | 'physics'
    | 'cryptography'
    | 'other';
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

const ROOT = process.cwd();

const CURATED_ROOT_DOCS: { title: string; relPath: string; category: CorpusDocumentSummary['category'] }[] = [
  { title: 'ParaconsistentCore.lean.txt', relPath: 'ParaconsistentCore.lean.txt', category: 'core' },
  { title: 'ParaconsistentFrobeniusClosure.lean.txt', relPath: 'ParaconsistentFrobeniusClosure.lean.txt', category: 'core' },
  { title: 'ClassicalRestriction.lean.txt', relPath: 'ClassicalRestriction.lean.txt', category: 'core' },
  { title: 'DeMorganBooleanCentre.lean.txt', relPath: 'DeMorganBooleanCentre.lean.txt', category: 'core' },
  { title: 'README_AUDIT.md (Yang–Mills Audit)', relPath: 'README_AUDIT.md', category: 'audit' },
  { title: 'CRYSTAL_closure-reads-a-proof.md', relPath: 'CRYSTAL_closure-reads-a-proof.md', category: 'audit' },
  { title: 'p4ramill/AXIOM_AUDIT_REPORT.md', relPath: 'p4ramill/AXIOM_AUDIT_REPORT.md', category: 'audit' },
  { title: 'p4ramill/ELOS.md', relPath: 'p4ramill/ELOS.md', category: 'erdos' },
];

function classifyFile(relPath: string): CorpusDocumentSummary['category'] {
  if (relPath.includes('/Erdos/') || relPath.includes('Erdos')) return 'erdos';
  if (relPath.includes('/Biochem/')) return 'biochem';
  if (relPath.includes('/Classical/')) return 'classical';
  if (relPath.includes('/IMASM/')) return 'imasm';
  if (relPath.includes('/Cryptography/')) return 'cryptography';
  if (relPath.includes('/Gravity/') || relPath.includes('FineStructure') || relPath.includes('Boson') || relPath.includes('Lepton') || relPath.includes('CKM') || relPath.includes('PMNS') || relPath.includes('SIC_')) return 'physics';
  if (relPath.includes('How') && relPath.includes('Arise')) return 'emergence';
  if (relPath.includes('/Millennium/')) return 'millennium';
  if (relPath.endsWith('.md')) return 'audit';
  return 'core';
}

function parseLeanOrDoc(relPath: string, title: string, category: CorpusDocumentSummary['category']): CorpusDocumentSummary {
  const abs = path.join(ROOT, relPath);
  const raw = fs.readFileSync(abs, 'utf-8');
  const linesArr = raw.split(/\r?\n/);

  let namespaceName: string | null = null;
  const imports: string[] = [];
  const theorems: string[] = [];
  const defs: string[] = [];
  let sorryCount = 0;
  let axiomCount = 0;

  let inBlockComment = false;
  for (const line of linesArr) {
    const trimmed = line.trim();
    if (trimmed.startsWith('/-')) inBlockComment = true;
    if (inBlockComment) {
      if (trimmed.includes('-/')) inBlockComment = false;
      continue;
    }
    const codeOnly = trimmed.split('--')[0];
    if (!codeOnly) continue;

    if (!namespaceName) {
      const nsMatch = codeOnly.match(/^namespace\s+([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)/);
      if (nsMatch) namespaceName = nsMatch[1];
    }

    const impMatch = codeOnly.match(/^import\s+([A-Za-z0-9_.]+)/);
    if (impMatch) imports.push(impMatch[1]);

    const thmMatch = codeOnly.match(/^(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)/);
    if (thmMatch) theorems.push(thmMatch[1]);

    const defMatch = codeOnly.match(/^(?:private\s+|noncomputable\s+|abbrev\s+)*(?:def|structure|inductive|abbrev)\s+([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉]+)/);
    if (defMatch) defs.push(defMatch[1]);

    if (/\bsorry\b/.test(codeOnly)) sorryCount++;
    if (/^axiom\s+/.test(codeOnly)) axiomCount++;
  }

  return {
    id: relPath.replace(/[^a-zA-Z0-9]+/g, '-').toLowerCase(),
    title,
    relPath,
    category,
    namespaceName,
    imports,
    theorems,
    defs,
    sorryCount,
    axiomCount,
    lines: linesArr.length,
    bytes: Buffer.byteLength(raw, 'utf-8'),
  };
}

let cachedIndex: CorpusDocumentSummary[] | null = null;

function buildCorpusIndex(): CorpusDocumentSummary[] {
  if (cachedIndex) return cachedIndex;
  const results: CorpusDocumentSummary[] = [];
  const seen = new Set<string>();

  for (const doc of CURATED_ROOT_DOCS) {
    const abs = path.join(ROOT, doc.relPath);
    if (fs.existsSync(abs) && fs.statSync(abs).isFile()) {
      results.push(parseLeanOrDoc(doc.relPath, doc.title, doc.category));
      seen.add(doc.relPath);
    }
  }

  const p4ramillDir = path.join(ROOT, 'p4ramill');
  if (fs.existsSync(p4ramillDir)) {
    const walk = (dir: string) => {
      const entries = fs.readdirSync(dir, { withFileTypes: true });
      for (const entry of entries) {
        const full = path.join(dir, entry.name);
        if (entry.isDirectory()) {
          if (entry.name.startsWith('.') || entry.name === '__pycache__' || entry.name === 'attic') continue;
          walk(full);
        } else if (entry.isFile() && (entry.name.endsWith('.lean') || entry.name.endsWith('.md'))) {
          const relPath = path.relative(ROOT, full);
          if (seen.has(relPath)) continue;
          const title = relPath.replace(/^p4ramill\/Imscribing\//, '').replace(/^p4ramill\//, '');
          results.push(parseLeanOrDoc(relPath, title, classifyFile(relPath)));
          seen.add(relPath);
        }
      }
    };
    walk(p4ramillDir);
  }

  cachedIndex = results;
  return results;
}

export function getMsaAnalysis(): Record<string, unknown> {
  const msaPath = path.join(ROOT, 'msa_analysis.json');
  if (!fs.existsSync(msaPath)) return {};
  return JSON.parse(fs.readFileSync(msaPath, 'utf-8')) as Record<string, unknown>;
}

export function getAbcSpectralReadings(): Record<string, unknown> {
  const p = path.join(ROOT, 'p4ramill/Imscribing/ABC_Spectral_readings.json');
  if (!fs.existsSync(p)) return {};
  return JSON.parse(fs.readFileSync(p, 'utf-8')) as Record<string, unknown>;
}

export function getCorpusStats(): CorpusStats {
  const index = buildCorpusIndex();
  const leanDocs = index.filter((d) => d.relPath.endsWith('.lean') || d.relPath.endsWith('.lean.txt'));
  const catMap = new Map<string, { files: number; theorems: number; sorryFree: number }>();
  const importCounts = new Map<string, number>();

  let totalTheorems = 0;
  let totalDefs = 0;
  let sorryFreeLeanFiles = 0;
  let openConjectureLeanFiles = 0;

  for (const d of index) {
    totalTheorems += d.theorems.length;
    totalDefs += d.defs.length;

    const entry = catMap.get(d.category) ?? { files: 0, theorems: 0, sorryFree: 0 };
    entry.files += 1;
    entry.theorems += d.theorems.length;
    if (d.sorryCount === 0) entry.sorryFree += 1;
    catMap.set(d.category, entry);

    if (d.relPath.endsWith('.lean') || d.relPath.endsWith('.lean.txt')) {
      if (d.sorryCount === 0) sorryFreeLeanFiles++;
      else openConjectureLeanFiles++;
    }

    for (const imp of d.imports) {
      if (imp.startsWith('Imscribing.')) {
        importCounts.set(imp, (importCounts.get(imp) ?? 0) + 1);
      }
    }
  }

  const categories = Array.from(catMap.entries())
    .map(([category, v]) => ({ category, ...v }))
    .sort((a, b) => b.files - a.files);

  const topImportedModules = Array.from(importCounts.entries())
    .map(([module, count]) => ({ module, count }))
    .sort((a, b) => b.count - a.count)
    .slice(0, 15);

  return {
    totalFiles: index.length,
    leanFiles: leanDocs.length,
    sorryFreeLeanFiles,
    openConjectureLeanFiles,
    totalTheorems,
    totalDefs,
    categories,
    topImportedModules,
  };
}

export function listCorpusDocuments(
  query = '',
  category = '',
  onlyVerified = false
): CorpusDocumentSummary[] {
  const index = buildCorpusIndex();
  const q = query.trim().toLowerCase();
  const cat = category.trim().toLowerCase();

  return index.filter((d) => {
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

export function readCorpusDocument(relPath: string): {
  ok: boolean;
  content?: string;
  meta?: CorpusDocumentSummary;
  importedBy?: string[];
  error?: string;
} {
  const normalized = path.normalize(relPath).replace(/^(\.\.[/\\])+/, '');
  const abs = path.resolve(ROOT, normalized);
  if (!abs.startsWith(ROOT + path.sep) && abs !== ROOT) {
    return { ok: false, error: 'Path outside workspace root' };
  }
  if (!fs.existsSync(abs) || !fs.statSync(abs).isFile()) {
    return { ok: false, error: 'Document not found' };
  }
  const index = buildCorpusIndex();
  const meta = index.find((d) => d.relPath === normalized);
  const modName = normalized
    .replace(/^p4ramill\//, '')
    .replace(/\.lean$/, '')
    .replace(/\//g, '.');
  const importedBy = index
    .filter((d) => d.imports.includes(modName))
    .map((d) => d.relPath)
    .slice(0, 30);

  const content = fs.readFileSync(abs, 'utf-8');
  return { ok: true, content: content.slice(0, 65536), meta, importedBy };
}
