import express from 'express';
import fs from 'node:fs';
import path from 'node:path';
import {
  IMASM_OPCODES,
  analyzeFixedPoints,
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
  verifyCanonicalOracle,
  type BuiltinMapName,
} from './server/sixteen3.ts';
import { auditBelnapTheorems } from './server/belnap.ts';
import { analyzeToroidalSource, simulateOrganismCycle } from './server/organism.ts';
import { getAbcSpectralReadings, getCorpusStats, getMsaAnalysis, listCorpusDocuments, readCorpusDocument } from './server/corpus.ts';
import {
  IMSCRIPTION_PRESETS,
  PRIMITIVE_AXES,
  evaluateImscriptionPair,
  evaluateIuttState,
  getFineStructureBreakdown,
  simulateOuroboricExchange,
} from './server/imscribing.ts';

const PORT = 3000;
const HOST = '0.0.0.0';
const isProd = process.env.NODE_ENV === 'production';

async function startServer() {
  const app = express();
  app.use(express.json());

  // --- SIXTEEN_3 & Re-entry API ---
  app.get('/api/sixteen3/states', (_req, res) => {
    const states = Array.from({ length: 16 }, (_, m) => describeMask(m));
    res.json({ states });
  });

  app.get('/api/sixteen3/pair', (req, res) => {
    const a = Number(req.query.a ?? 5) & 15;
    const b = Number(req.query.b ?? 10) & 15;
    res.json({
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
    });
  });

  app.post('/api/sixteen3/reentry', (req, res) => {
    const {
      op = 'join_i',
      paramA = 5,
      paramB = 10,
      start = 0,
      tick = '1000000000001',
      customTable,
    } = req.body ?? {};

    let table: number[];
    if (Array.isArray(customTable) && customTable.length === 16) {
      table = customTable.map((n: unknown) => Number(n) & 15);
    } else {
      table = buildOperatorTable(op as BuiltinMapName, Number(paramA), Number(paramB));
    }

    const analysis = analyzeFixedPoints(table);
    const orbit = computeOrbit(table, Number(start), String(tick));
    res.json({ analysis, orbit });
  });

  app.post('/api/sixteen3/combinator', (req, res) => {
    const raw = String(req.body?.program ?? 'Y K K data:6 @ @ @');
    const tokens = raw.trim().split(/\s+/).filter(Boolean);
    res.json(evaluateCombinatorTokens(tokens));
  });

  app.get('/api/sixteen3/oracle', (_req, res) => {
    res.json(verifyCanonicalOracle());
  });

  // --- IMASM Banked Machine API ---
  app.get('/api/imasm/opcodes', (_req, res) => {
    res.json({ opcodes: IMASM_OPCODES });
  });

  app.post('/api/imasm/evaluate', (req, res) => {
    const word = String(req.body?.word ?? '⊢∈≻⋈⊙⊤≻⋈⊥≺⋈⊞∋⊡⋈⊙⊣');
    const start = Number(req.body?.start ?? 0);
    const tick = String(req.body?.tick ?? '1000000000000');
    res.json(evaluateImasmWord(word, start, tick));
  });

  // --- Belnap FOUR & Cuts API ---
  app.get('/api/belnap/audit', (_req, res) => {
    res.json(auditBelnapTheorems());
  });

  // --- Imscribing 12-Tuple, IUTT, Physics & Crypto API ---
  app.get('/api/imscribing/meta', (_req, res) => {
    res.json({
      axes: PRIMITIVE_AXES,
      presets: IMSCRIPTION_PRESETS,
      fineStructure: getFineStructureBreakdown(),
    });
  });

  app.post('/api/imscribing/evaluate', (req, res) => {
    const a = req.body?.a ?? IMSCRIPTION_PRESETS.human_brain.tuple;
    const b = req.body?.b ?? IMSCRIPTION_PRESETS.replicative_core.tuple;
    res.json(evaluateImscriptionPair(a, b));
  });

  app.post('/api/imscribing/iutt', (req, res) => {
    const state = req.body?.state ?? { bigT: true, bigF: true, smallT: true, smallF: true };
    res.json(evaluateIuttState(state));
  });

  app.post('/api/imscribing/ouroboric', (req, res) => {
    const state = (req.body?.state ?? 'B') as 'N' | 'T' | 'F' | 'B';
    res.json(simulateOuroboricExchange(state));
  });

  // --- Dialetheic Organism & Toroidal Division API ---
  app.post('/api/organism/cycle', (req, res) => {
    const steps = Number(req.body?.steps ?? 12);
    const startMask = Number(req.body?.startMask ?? 8);
    res.json(simulateOrganismCycle(steps, startMask));
  });

  app.post('/api/organism/torus', (req, res) => {
    const source = String(req.body?.source ?? '2417851639229258349412357');
    res.json(analyzeToroidalSource(source));
  });

  // --- Corpus & MSA Analysis API ---
  app.get('/api/corpus/stats', (_req, res) => {
    res.json(getCorpusStats());
  });

  app.get('/api/corpus/msa', (_req, res) => {
    res.json(getMsaAnalysis());
  });

  app.get('/api/corpus/abc-spectral', (_req, res) => {
    res.json(getAbcSpectralReadings());
  });

  app.get('/api/corpus/docs', (req, res) => {
    const q = String(req.query.q ?? '');
    const category = String(req.query.category ?? '');
    const onlyVerified = req.query.onlyVerified === 'true';
    res.json({ docs: listCorpusDocuments(q, category, onlyVerified) });
  });

  app.get('/api/corpus/doc', (req, res) => {
    const relPath = String(req.query.path ?? '');
    if (!relPath) {
      res.status(400).json({ ok: false, error: 'Missing path parameter' });
      return;
    }
    const result = readCorpusDocument(relPath);
    if (!result.ok) {
      res.status(404).json(result);
      return;
    }
    res.json(result);
  });

  // --- Frontend Serving ---
  if (!isProd) {
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: { middlewareMode: true },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distDir = path.resolve(process.cwd(), 'dist');
    app.use(express.static(distDir));
    app.get('*', (_req, res) => {
      const indexFile = path.join(distDir, 'index.html');
      if (fs.existsSync(indexFile)) {
        res.sendFile(indexFile);
      } else {
        res.status(404).send('Build output not found. Run npm run build first.');
      }
    });
  }

  app.listen(PORT, HOST, () => {
    console.log(`p4rakernel workbench listening on http://${HOST}:${PORT}`);
  });
}

startServer().catch((err) => {
  console.error('Failed to start p4rakernel server:', err);
  process.exit(1);
});
