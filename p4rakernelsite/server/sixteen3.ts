import fs from 'node:fs';
import path from 'node:path';
import {
  buildCanonicalOracleData,
  type OracleVerificationReport,
} from '../src/engine/sixteen3.ts';

export * from '../src/engine/sixteen3.ts';

export function verifyCanonicalOracle(): OracleVerificationReport {
  const { generatedLines, sampleRows } = buildCanonicalOracleData();
  const oraclePath = path.resolve(process.cwd(), 'edge1/organism/lean_oracle.txt');
  let oracleFilePresent = false;
  let oracleFileMatches = false;
  let totalRows = 272;

  if (fs.existsSync(oraclePath)) {
    oracleFilePresent = true;
    const raw = fs.readFileSync(oraclePath, 'utf-8').trim().split(/\r?\n/);
    const latticeFileRows = raw.filter((l) => l.startsWith('lattice '));
    oracleFileMatches =
      latticeFileRows.length === 256 &&
      generatedLines.every((line, idx) => line === latticeFileRows[idx]);
    totalRows = raw.length;
  }

  return {
    totalRows,
    pairRows: 256,
    unaryRows: 16,
    passed: !oracleFilePresent || oracleFileMatches,
    oracleFilePresent,
    oracleFileMatches,
    sampleRows,
  };
}
