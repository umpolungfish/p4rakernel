import fs from 'node:fs';
import path from 'node:path';
import {
  getAbcSpectralReadings,
  getCorpusStats,
  getMsaAnalysis,
  listCorpusDocuments,
  readCorpusDocument,
} from '../server/corpus.ts';
import { verifyCanonicalOracle } from '../server/sixteen3.ts';

const ROOT = process.cwd();
const OUT_DIR = path.join(ROOT, 'public', 'data');
const DOCS_DIR = path.join(OUT_DIR, 'docs');

fs.mkdirSync(DOCS_DIR, { recursive: true });

// Ensure GitHub Pages does not ignore any static files or directories
fs.writeFileSync(path.join(ROOT, 'public', '.nojekyll'), '');

const stats = getCorpusStats();
const docs = listCorpusDocuments('', 'all', false);
const msa = getMsaAnalysis();
const abc = getAbcSpectralReadings();
const oracle = verifyCanonicalOracle();

fs.writeFileSync(
  path.join(OUT_DIR, 'corpus-bundle.json'),
  JSON.stringify({ stats, docs, msa, abc, oracle })
);

let written = 0;
for (const doc of docs) {
  const detail = readCorpusDocument(doc.relPath);
  if (detail.ok) {
    fs.writeFileSync(
      path.join(DOCS_DIR, `${doc.id}.json`),
      JSON.stringify({
        ok: true,
        meta: detail.meta,
        importedBy: detail.importedBy ?? [],
        content: detail.content ?? '',
      })
    );
    written++;
  }
}

console.log(
  `Generated GitHub Pages static bundle: ${written} docs, ${stats.leanFiles} Lean modules, ${stats.totalTheorems} theorems, oracle=${oracle.passed}`
);
