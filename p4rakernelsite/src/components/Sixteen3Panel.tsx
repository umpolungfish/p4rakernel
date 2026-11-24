import React, { useEffect, useState } from 'react';
import { CheckCircle2, XCircle, Play, RefreshCw, ShieldCheck } from 'lucide-react';
import { StateChip, formatMaskLabel } from './StateChip';
import { Sixteen3HasseSvg, OrbitPhaseRingSvg } from './Infographics';
import type { FixedPointAnalysis, OrbitResult, Sixteen3StateInfo } from '../types';
import {
  fetchOracleReport,
  getSixteen3Pair,
  runSixteen3Combinator,
  runSixteen3Reentry,
} from '../lib/workbenchApi';

interface PairResult {
  a: Sixteen3StateInfo;
  b: Sixteen3StateInfo;
  join_i: Sixteen3StateInfo;
  meet_i: Sixteen3StateInfo;
  join_t: Sixteen3StateInfo;
  meet_t: Sixteen3StateInfo;
  join_f: Sixteen3StateInfo;
  meet_f: Sixteen3StateInfo;
  negation_a: Sixteen3StateInfo;
  le_i: boolean;
  le_t: boolean;
  le_f: boolean;
}

interface CombinatorResult {
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

interface OracleReport {
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

export const Sixteen3Panel: React.FC = () => {
  const [a, setA] = useState(5);
  const [b, setB] = useState(10);
  const [clickTarget, setClickTarget] = useState<'A' | 'B'>('A');
  const [pair, setPair] = useState<PairResult | null>(null);

  const [op, setOp] = useState<string>('negation');
  const [paramA, setParamA] = useState(7);
  const [paramB, setParamB] = useState(10);
  const [start, setStart] = useState(2);
  const [tick, setTick] = useState('1000000000001');
  const [reentry, setReentry] = useState<{ analysis: FixedPointAnalysis; orbit: OrbitResult } | null>(null);

  const [program, setProgram] = useState('Y K K data:6 @ @ @');
  const [combResult, setCombResult] = useState<CombinatorResult | null>(null);
  const [oracle, setOracle] = useState<OracleReport | null>(null);

  useEffect(() => {
    setPair(getSixteen3Pair(a, b));
  }, [a, b]);

  const runReentry = () => {
    setReentry(runSixteen3Reentry({ op, paramA, paramB, start, tick }));
  };

  useEffect(() => {
    runReentry();
  }, [op, paramA, paramB, start, tick]);

  const runCombinator = () => {
    setCombResult(runSixteen3Combinator(program));
  };

  useEffect(() => {
    runCombinator();
  }, []);

  const runOracle = () => {
    fetchOracleReport().then(setOracle).catch(() => {});
  };

  useEffect(() => {
    runOracle();
  }, []);

  return (
    <div className="space-y-5">
      {/* Section 1: SIXTEEN_3 4D Hasse Lattice + Trilattice Operators */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              SIXTEEN<sub>3</sub> Trilattice Hasse Diagram — 𝒫({'{N, T, F, B}'})
            </h2>
            <p className="text-xs text-slate-400">
              N=1 · T=2 · F=4 · B=8 across ≤<sub>i</sub>, ≤<sub>t</sub>, and ≤<sub>f</sub> partial orders
            </p>
          </div>

          <div className="flex flex-wrap items-center gap-3 text-xs">
            <div className="inline-flex rounded border border-slate-700 bg-[#07090e] p-0.5 font-mono">
              <button
                type="button"
                onClick={() => setClickTarget('A')}
                className={`px-2.5 py-1 rounded text-xs whitespace-nowrap cursor-pointer ${
                  clickTarget === 'A' ? 'bg-emerald-500/20 text-emerald-300' : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                Node click → A
              </button>
              <button
                type="button"
                onClick={() => setClickTarget('B')}
                className={`px-2.5 py-1 rounded text-xs whitespace-nowrap cursor-pointer ${
                  clickTarget === 'B' ? 'bg-cyan-500/20 text-cyan-300' : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                Node click → B
              </button>
            </div>
            <div className="flex items-center gap-1.5">
              <span className="text-slate-400 font-mono">A</span>
              <StateChip mask={a} />
            </div>
            <div className="flex items-center gap-1.5">
              <span className="text-slate-400 font-mono">B</span>
              <StateChip mask={b} />
            </div>
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
          {/* Interactive 4D Hypercube SVG */}
          <div className="lg:col-span-7 rounded border border-slate-800 bg-[#07090e] p-3">
            <Sixteen3HasseSvg
              a={a}
              b={b}
              joinI={pair?.join_i.mask ?? (a | b)}
              meetI={pair?.meet_i.mask ?? (a & b)}
              clickTarget={clickTarget}
              onSelectState={(m) => (clickTarget === 'A' ? setA(m) : setB(m))}
            />
          </div>

          {/* Live 3-Order Telemetry & Compact 0..15 Selector Strip */}
          <div className="lg:col-span-5 space-y-3">
            {pair && (
              <div className="grid grid-cols-1 sm:grid-cols-3 lg:grid-cols-1 gap-2.5">
                <div className="rounded border border-slate-800 bg-[#07090e] p-3 flex items-center justify-between gap-2 text-xs">
                  <div>
                    <div className="text-[11px] font-mono text-slate-400 uppercase">Information (≤<sub>i</sub>)</div>
                    <div className="font-mono text-[11px] text-slate-400 mt-0.5 tabular-nums">
                      A ≤<sub>i</sub> B:{' '}
                      <span className={pair.le_i ? 'text-emerald-400 font-semibold' : 'text-rose-400'}>
                        {String(pair.le_i)}
                      </span>
                    </div>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="font-mono text-slate-500">∨<sub>i</sub></span>
                    <StateChip mask={pair.join_i.mask} />
                    <span className="font-mono text-slate-500">∧<sub>i</sub></span>
                    <StateChip mask={pair.meet_i.mask} />
                  </div>
                </div>

                <div className="rounded border border-slate-800 bg-[#07090e] p-3 flex items-center justify-between gap-2 text-xs">
                  <div>
                    <div className="text-[11px] font-mono text-slate-400 uppercase">Truth (≤<sub>t</sub>)</div>
                    <div className="font-mono text-[11px] text-slate-400 mt-0.5 tabular-nums">
                      A ≤<sub>t</sub> B:{' '}
                      <span className={pair.le_t ? 'text-emerald-400 font-semibold' : 'text-rose-400'}>
                        {String(pair.le_t)}
                      </span>
                    </div>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="font-mono text-slate-500">∨<sub>t</sub></span>
                    <StateChip mask={pair.join_t.mask} />
                    <span className="font-mono text-slate-500">∧<sub>t</sub></span>
                    <StateChip mask={pair.meet_t.mask} />
                  </div>
                </div>

                <div className="rounded border border-slate-800 bg-[#07090e] p-3 flex items-center justify-between gap-2 text-xs">
                  <div>
                    <div className="text-[11px] font-mono text-slate-400 uppercase">Falsity (≤<sub>f</sub>)</div>
                    <div className="font-mono text-[11px] text-slate-400 mt-0.5 tabular-nums">
                      A ≤<sub>f</sub> B:{' '}
                      <span className={pair.le_f ? 'text-emerald-400 font-semibold' : 'text-rose-400'}>
                        {String(pair.le_f)}
                      </span>
                    </div>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="font-mono text-slate-500">∨<sub>f</sub></span>
                    <StateChip mask={pair.join_f.mask} />
                    <span className="font-mono text-slate-500">∧<sub>f</sub></span>
                    <StateChip mask={pair.meet_f.mask} />
                  </div>
                </div>

                <div className="rounded border border-slate-800 bg-[#07090e] px-3 py-2 flex items-center justify-between text-xs font-mono">
                  <span className="text-slate-400">Negation ¬A (T ↔ F)</span>
                  <StateChip mask={pair.negation_a.mask} />
                </div>
              </div>
            )}

            {/* Quick numeric mask selectors */}
            <div className="rounded border border-slate-800 bg-[#07090e] p-3 grid grid-cols-2 gap-3 text-xs font-mono">
              <div>
                <label className="block text-[11px] text-emerald-300 mb-1">Operand A</label>
                <select
                  value={a}
                  onChange={(e) => setA(Number(e.target.value))}
                  className="w-full rounded border border-slate-700 bg-[#0c1017] px-2 py-1 text-xs text-slate-100"
                >
                  {Array.from({ length: 16 }, (_, m) => (
                    <option key={m} value={m}>
                      {m} · {formatMaskLabel(m)}
                    </option>
                  ))}
                </select>
              </div>
              <div>
                <label className="block text-[11px] text-cyan-300 mb-1">Operand B</label>
                <select
                  value={b}
                  onChange={(e) => setB(Number(e.target.value))}
                  className="w-full rounded border border-slate-700 bg-[#0c1017] px-2 py-1 text-xs text-slate-100"
                >
                  {Array.from({ length: 16 }, (_, m) => (
                    <option key={m} value={m}>
                      {m} · {formatMaskLabel(m)}
                    </option>
                  ))}
                </select>
              </div>
            </div>
          </div>
        </div>
      </section>

      {/* Section 2: Re-entry Fixed-Point & Finite-Clock Orbit Phase Ring */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              Knaster–Tarski Fixed Points &amp; Finite-Clock Orbit
            </h2>
            <p className="text-xs text-slate-400">
              BigInt O(1) modular orbit lookup · certified lattice extrema
            </p>
          </div>
          <div className="flex flex-wrap gap-1.5">
            <button
              type="button"
              onClick={() => { setOp('negation'); setStart(2); setTick('1000000000001'); }}
              className="px-2.5 py-1 rounded border border-slate-700 bg-[#07090e] hover:border-amber-500/50 text-xs font-mono text-slate-200 cursor-pointer whitespace-nowrap"
            >
              negation @ 10<sup>12</sup>+1
            </button>
            <button
              type="button"
              onClick={() => { setOp('retain_after_inject'); setParamA(7); setParamB(10); setStart(0); setTick('10'); }}
              className="px-2.5 py-1 rounded border border-slate-700 bg-[#07090e] hover:border-amber-500/50 text-xs font-mono text-slate-200 cursor-pointer whitespace-nowrap"
            >
              retain-after-inject(7,10)
            </button>
            <button
              type="button"
              onClick={() => { setOp('inject_after_retain'); setParamA(7); setParamB(10); setStart(0); setTick('10'); }}
              className="px-2.5 py-1 rounded border border-slate-700 bg-[#07090e] hover:border-amber-500/50 text-xs font-mono text-slate-200 cursor-pointer whitespace-nowrap"
            >
              inject-after-retain(7,10)
            </button>
          </div>
        </div>

        <div className="grid grid-cols-2 sm:grid-cols-5 gap-3 mb-4">
          <div>
            <label className="block text-[11px] text-slate-400 mb-1">Operator Map</label>
            <select
              value={op}
              onChange={(e) => setOp(e.target.value)}
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100"
            >
              <option value="negation">negation (T ↔ F)</option>
              <option value="join_i">info join (x, A)</option>
              <option value="meet_i">info meet (x, A)</option>
              <option value="join_t">truth join (x, A)</option>
              <option value="meet_t">truth meet (x, A)</option>
              <option value="join_f">falsity join (x, A)</option>
              <option value="meet_f">falsity meet (x, A)</option>
              <option value="retain_after_inject">retain-after-inject(A, B)</option>
              <option value="inject_after_retain">inject-after-retain(A, B)</option>
              <option value="inc_closure">inc closure (Frobenius lift)</option>
              <option value="complement">complement (~x)</option>
            </select>
          </div>
          <div>
            <label className="block text-[11px] text-slate-400 mb-1">Param A</label>
            <input
              type="number"
              min={0}
              max={15}
              value={paramA}
              onChange={(e) => setParamA(Number(e.target.value))}
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
            />
          </div>
          <div>
            <label className="block text-[11px] text-slate-400 mb-1">Param B</label>
            <input
              type="number"
              min={0}
              max={15}
              value={paramB}
              onChange={(e) => setParamB(Number(e.target.value))}
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
            />
          </div>
          <div>
            <label className="block text-[11px] text-slate-400 mb-1">Start State</label>
            <input
              type="number"
              min={0}
              max={15}
              value={start}
              onChange={(e) => setStart(Number(e.target.value))}
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
            />
          </div>
          <div>
            <label className="block text-[11px] text-slate-400 mb-1">Clock Tick (BigInt)</label>
            <input
              type="text"
              value={tick}
              onChange={(e) => setTick(e.target.value)}
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
            />
          </div>
        </div>

        {reentry && (
          <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
            <div className="lg:col-span-5 rounded border border-slate-800 bg-[#07090e] p-3">
              <OrbitPhaseRingSvg orbit={reentry.orbit} fixedPoints={reentry.analysis.fixedPoints} />
            </div>

            <div className="lg:col-span-7 space-y-3">
              <div className="grid grid-cols-2 sm:grid-cols-4 gap-2.5 text-xs">
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400 mb-1">Least FP</div>
                  {reentry.analysis.leastFixedPoint !== null ? (
                    <StateChip mask={reentry.analysis.leastFixedPoint} />
                  ) : (
                    <span className="font-mono text-rose-400">none</span>
                  )}
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400 mb-1">Greatest FP</div>
                  {reentry.analysis.greatestFixedPoint !== null ? (
                    <StateChip mask={reentry.analysis.greatestFixedPoint} />
                  ) : (
                    <span className="font-mono text-rose-400">none</span>
                  )}
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400 mb-1">Period · Trans</div>
                  <div className="font-mono text-sm font-semibold text-slate-100 tabular-nums">
                    {reentry.orbit.period} · {reentry.orbit.transient}
                  </div>
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400 mb-1">Orbit Landing</div>
                  <StateChip mask={reentry.orbit.value} highlight />
                </div>
              </div>

              <div className="flex flex-wrap items-center gap-4 text-xs font-mono px-3 py-2 rounded border border-slate-800 bg-[#07090e] tabular-nums">
                <span className="inline-flex items-center gap-1.5">
                  {reentry.analysis.monotoneInfo ? (
                    <CheckCircle2 className="w-3.5 h-3.5 text-emerald-400" />
                  ) : (
                    <XCircle className="w-3.5 h-3.5 text-rose-400" />
                  )}
                  <span>monotone<sub>i</sub></span>
                </span>
                <span className="inline-flex items-center gap-1.5">
                  {reentry.analysis.monotoneTruth ? (
                    <CheckCircle2 className="w-3.5 h-3.5 text-emerald-400" />
                  ) : (
                    <XCircle className="w-3.5 h-3.5 text-slate-500" />
                  )}
                  <span>monotone<sub>t</sub></span>
                </span>
                <span className="inline-flex items-center gap-1.5">
                  {reentry.analysis.certified ? (
                    <CheckCircle2 className="w-3.5 h-3.5 text-emerald-400" />
                  ) : (
                    <XCircle className="w-3.5 h-3.5 text-amber-400" />
                  )}
                  certified
                </span>
                <span className="text-slate-400">
                  cycle=[{reentry.orbit.cycle.join('→')}]
                </span>
              </div>

              <div>
                <div className="text-[11px] font-mono text-slate-400 mb-1.5">
                  16-State Map (click cell to set Start)
                </div>
                <div className="grid grid-cols-4 sm:grid-cols-8 gap-1.5 font-mono text-xs tabular-nums">
                  {reentry.analysis.table.map((out, x) => {
                    const isFixed = x === out;
                    const isStart = x === start;
                    return (
                      <button
                        key={x}
                        type="button"
                        onClick={() => setStart(x)}
                        className={`rounded border px-2 py-1.5 flex items-center justify-between cursor-pointer transition-colors ${
                          isStart
                            ? 'border-cyan-400 bg-cyan-500/15 text-cyan-200'
                            : isFixed
                            ? 'border-emerald-500/40 bg-emerald-500/10 text-emerald-200'
                            : 'border-slate-800 bg-[#07090e] text-slate-300 hover:border-slate-600'
                        }`}
                      >
                        <span className="text-slate-500">{x}→</span>
                        <span className="font-semibold">{out}</span>
                      </button>
                    );
                  })}
                </div>
              </div>
            </div>
          </div>
        )}
      </section>

      {/* Section 3: SKIY Combinator & 256-Row Lean Oracle */}
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-5">
        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <div className="flex items-center justify-between mb-3">
            <h2 className="text-sm font-semibold text-slate-100">
              S / K / I / Y Combinator Re-entry
            </h2>
            <div className="flex flex-wrap gap-1">
              {[
                'Y K K data:6 @ @ @',
                'S K K data:15 @ @ @',
                'I data:8 @',
                'K data:2 data:4 @ @',
              ].map((ex) => (
                <button
                  key={ex}
                  type="button"
                  onClick={() => setProgram(ex)}
                  className="px-2 py-0.5 rounded border border-slate-800 bg-[#07090e] text-[10px] font-mono text-slate-400 hover:text-slate-200 cursor-pointer"
                >
                  {ex.split(' ')[0]} {ex.split(' ')[1]}
                </button>
              ))}
            </div>
          </div>

          <div className="flex gap-2 mb-3">
            <input
              type="text"
              value={program}
              onChange={(e) => setProgram(e.target.value)}
              className="flex-1 rounded border border-slate-700 bg-[#07090e] px-3 py-1.5 text-xs font-mono text-slate-100"
              placeholder="Y K K data:6 @ @ @"
            />
            <button
              type="button"
              onClick={runCombinator}
              className="inline-flex items-center gap-1.5 rounded bg-amber-500/20 border border-amber-500/40 px-3 py-1.5 text-xs font-medium text-amber-200 hover:bg-amber-500/30 cursor-pointer whitespace-nowrap"
            >
              <Play className="w-3.5 h-3.5" />
              Reduce
            </button>
          </div>

          {combResult && (
            <div className="rounded border border-slate-800 bg-[#07090e] p-3 text-xs font-mono space-y-2 tabular-nums">
              {!combResult.valid ? (
                <div className="text-rose-400">Error: {combResult.error}</div>
              ) : (
                <>
                  <div className="flex flex-wrap items-center justify-between gap-2">
                    <span className="text-slate-400">
                      reentry=<span className="text-emerald-300 font-semibold">{combResult.kernelReentry ?? 'none'}</span>
                      {' · '}least={combResult.least ?? '—'} · greatest={combResult.greatest ?? '—'}
                    </span>
                    <span className={combResult.certified ? 'text-emerald-400' : 'text-amber-400'}>
                      certified={String(combResult.certified)}
                    </span>
                  </div>
                  <div className="space-y-1 pt-2 border-t border-slate-800/80 text-[11px] text-slate-300 max-h-36 overflow-y-auto">
                    {combResult.steps?.map((st, idx) => (
                      <div key={idx}>
                        <span className="text-slate-500 mr-2">[{idx}]</span>
                        {st}
                      </div>
                    ))}
                  </div>
                </>
              )}
            </div>
          )}
        </section>

        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <div className="flex items-center justify-between mb-3">
            <h2 className="text-sm font-semibold text-slate-100">
              Canonical Lean Oracle Parity Check
            </h2>
            <button
              type="button"
              onClick={runOracle}
              className="inline-flex items-center gap-1.5 rounded border border-slate-700 bg-[#07090e] px-2.5 py-1 text-xs text-slate-200 hover:border-slate-500 cursor-pointer whitespace-nowrap"
            >
              <RefreshCw className="w-3 h-3" />
              Verify
            </button>
          </div>

          {oracle && (
            <div className="space-y-3">
              <div className="flex items-center justify-between rounded border border-emerald-500/30 bg-emerald-500/10 px-3 py-2 text-xs font-mono tabular-nums">
                <span className="inline-flex items-center gap-2 text-emerald-200">
                  <ShieldCheck className="w-4 h-4 text-emerald-400" />
                  {oracle.passed ? '256/256 pair rows match lean_oracle.txt' : 'MISMATCH'}
                </span>
                <span className="text-emerald-300">{oracle.totalRows} rows</span>
              </div>
              <div className="max-h-40 overflow-y-auto rounded border border-slate-800 bg-[#07090e]">
                <table className="w-full text-[11px] font-mono text-left tabular-nums">
                  <thead className="sticky top-0 bg-slate-900 text-slate-400 border-b border-slate-800">
                    <tr>
                      <th className="px-2 py-1">a,b</th>
                      <th className="px-2 py-1">∨<sub>i</sub>/∧<sub>i</sub></th>
                      <th className="px-2 py-1">∨<sub>t</sub>/∧<sub>t</sub></th>
                      <th className="px-2 py-1">∨<sub>f</sub>/∧<sub>f</sub></th>
                      <th className="px-2 py-1">≤<sub>t</sub> ≤<sub>f</sub> ≤<sub>i</sub></th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-800/60 text-slate-300">
                    {oracle.sampleRows.map((r) => (
                      <tr key={`${r.a}-${r.b}`}>
                        <td className="px-2 py-1 text-slate-400">{r.a},{r.b}</td>
                        <td className="px-2 py-1">{r.joinI}/{r.meetI}</td>
                        <td className="px-2 py-1">{r.joinT}/{r.meetT}</td>
                        <td className="px-2 py-1">{r.joinF}/{r.meetF}</td>
                        <td className="px-2 py-1">
                          {r.leT ? 'T' : '·'} {r.leF ? 'T' : '·'} {r.leI ? 'T' : '·'}
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          )}
        </section>
      </div>
    </div>
  );
};
