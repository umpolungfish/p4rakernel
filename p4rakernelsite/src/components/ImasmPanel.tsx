import React, { useEffect, useState } from 'react';
import { Play, Trash2 } from 'lucide-react';
import { StateChip } from './StateChip';
import { ImasmStackTimelineSvg } from './Infographics';
import type { ImasmEvaluationResult, ImasmOpcodeSpec } from '../types';
import { getImasmOpcodes, runImasmWord } from '../lib/workbenchApi';

const PRESETS = [
  { label: 'Full Protocol Word', word: '⊢∈≻⋈⊙⊤≻⋈⊥≺⋈⊞∋⊡⋈⊙⊣' },
  { label: 'Same-Region (2)', word: '∈⊤⊤≺∋' },
  { label: 'Sibling-Region (1)', word: '∈⊤∈⊤∋≺∋' },
  { label: 'Premature Fuse (0)', word: '∈⊤⊤∋≺∋' },
  { label: 'Isolated (⊙)', word: '⊙' },
];

export const ImasmPanel: React.FC = () => {
  const [opcodes, setOpcodes] = useState<ImasmOpcodeSpec[]>([]);
  const [word, setWord] = useState('⊢∈≻⋈⊙⊤≻⋈⊥≺⋈⊞∋⊡⋈⊙⊣');
  const [start, setStart] = useState(0);
  const [tick, setTick] = useState('1000000000000');
  const [result, setResult] = useState<ImasmEvaluationResult | null>(null);
  const [viewMode, setViewMode] = useState<'trace' | 'bijection'>('trace');

  useEffect(() => {
    setOpcodes(getImasmOpcodes());
  }, []);

  const evaluate = (w = word) => {
    setResult(runImasmWord(w, start, tick));
  };

  useEffect(() => {
    evaluate(word);
  }, [word, start, tick]);

  return (
    <div className="space-y-5">
      {/* Interactive Composer + Visual Stack Timeline */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              IMASM Banked-Weight Machine &amp; 12-Glyph Stack
            </h2>
            <p className="text-xs text-slate-400">
              BankedWeight.lean · OpcodeMapping.lean · Base-12 scalar execution
            </p>
          </div>
          <div className="flex flex-wrap gap-1.5">
            {PRESETS.map((p) => (
              <button
                key={p.label}
                type="button"
                onClick={() => setWord(p.word)}
                className={`px-2.5 py-1 rounded border text-xs cursor-pointer whitespace-nowrap ${
                  word === p.word
                    ? 'border-amber-500/60 bg-amber-500/15 text-amber-200'
                    : 'border-slate-700 bg-[#07090e] hover:border-amber-500/40 text-slate-300'
                }`}
              >
                {p.label}
              </button>
            ))}
          </div>
        </div>

        {/* 12-Glyph Keyboard */}
        <div className="grid grid-cols-4 sm:grid-cols-6 lg:grid-cols-12 gap-1.5 mb-4">
          {opcodes.map((op) => (
            <button
              key={op.glyph}
              type="button"
              onClick={() => setWord((prev) => prev + op.glyph)}
              className="rounded border border-slate-800 bg-[#07090e] hover:border-amber-500/60 p-2 text-left transition-colors cursor-pointer"
              title={`${op.opcode} (${op.primitive})`}
            >
              <div className="flex items-center justify-between">
                <span className="text-lg font-mono text-amber-300">{op.glyph}</span>
                <span className="text-[10px] font-mono text-slate-500 tabular-nums">{op.index}</span>
              </div>
              <div className="text-[10px] font-mono font-semibold text-slate-200 truncate">{op.opcode}</div>
              <div className="text-[10px] text-slate-400 truncate">{op.bankAction}</div>
            </button>
          ))}
        </div>

        {/* Input Bar */}
        <div className="grid grid-cols-1 sm:grid-cols-12 gap-3 mb-4">
          <div className="sm:col-span-6">
            <div className="flex gap-1.5">
              <input
                type="text"
                value={word}
                onChange={(e) => setWord(e.target.value)}
                aria-label="IMASM Word"
                className="flex-1 rounded border border-slate-700 bg-[#07090e] px-3 py-1.5 text-sm font-mono text-amber-200"
              />
              <button
                type="button"
                onClick={() => setWord('')}
                className="rounded border border-slate-700 bg-[#07090e] px-2.5 text-slate-400 hover:text-rose-300 cursor-pointer"
                title="Clear word"
              >
                <Trash2 className="w-3.5 h-3.5" />
              </button>
            </div>
          </div>
          <div className="sm:col-span-2">
            <input
              type="number"
              min={0}
              max={15}
              value={start}
              onChange={(e) => setStart(Number(e.target.value))}
              aria-label="Start State"
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
              title="Start State (0-15)"
            />
          </div>
          <div className="sm:col-span-2">
            <input
              type="text"
              value={tick}
              onChange={(e) => setTick(e.target.value)}
              aria-label="Orbit Tick"
              className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
              title="Orbit Tick"
            />
          </div>
          <div className="sm:col-span-2">
            <button
              type="button"
              onClick={() => evaluate(word)}
              className="w-full inline-flex items-center justify-center gap-1.5 rounded bg-amber-500/20 border border-amber-500/40 px-3 py-1.5 text-xs font-medium text-amber-200 hover:bg-amber-500/30 cursor-pointer whitespace-nowrap"
            >
              <Play className="w-3.5 h-3.5" />
              Run Word
            </button>
          </div>
        </div>

        {result && !result.valid && (
          <div className="rounded border border-rose-500/40 bg-rose-500/10 p-3 text-xs font-mono text-rose-300">
            {result.error}
          </div>
        )}

        {result && result.valid && (
          <div className="space-y-4">
            {/* KPI Readout Row */}
            <div className="grid grid-cols-2 sm:grid-cols-5 gap-2.5 text-xs tabular-nums">
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <div className="text-[11px] text-slate-400">Recovered Weight</div>
                <div className="font-mono text-lg font-semibold text-emerald-300">
                  {result.totalRecoveredWeight}
                </div>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <div className="text-[11px] text-slate-400">Open Frames</div>
                <div className="font-mono text-lg font-semibold text-slate-100">
                  {result.openFramesRemaining}
                </div>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <div className="text-[11px] text-slate-400">Base-12 Scalar</div>
                <div className="font-mono text-xs font-semibold text-amber-300 truncate mt-1" title={result.base12Scalar}>
                  {result.base12Scalar}
                </div>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <div className="text-[11px] text-slate-400">Fixed Points</div>
                <div className="font-mono text-slate-100 mt-1">
                  {result.sixteen3Analysis.certified
                    ? `${result.sixteen3Analysis.leastFixedPoint} … ${result.sixteen3Analysis.greatestFixedPoint}`
                    : 'unavailable'}
                </div>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <div className="text-[11px] text-slate-400 mb-1">Orbit Landing</div>
                <StateChip mask={result.orbit.value} highlight />
              </div>
            </div>

            {/* Visual Fork-Frame Stack & Register Timeline SVG */}
            <div className="rounded border border-slate-800 bg-[#07090e] p-3 overflow-x-auto">
              <ImasmStackTimelineSvg steps={result.bankedSteps} />
            </div>

            {/* Switchable Execution Trace / 12↔12 Bijection Table */}
            <div>
              <div className="flex items-center justify-between mb-2">
                <div className="inline-flex rounded border border-slate-800 bg-[#07090e] p-0.5 text-xs font-mono">
                  <button
                    type="button"
                    onClick={() => setViewMode('trace')}
                    className={`px-3 py-1 rounded cursor-pointer ${
                      viewMode === 'trace' ? 'bg-amber-500/20 text-amber-200' : 'text-slate-400 hover:text-slate-200'
                    }`}
                  >
                    Step Trace ({result.bankedSteps.length})
                  </button>
                  <button
                    type="button"
                    onClick={() => setViewMode('bijection')}
                    className={`px-3 py-1 rounded cursor-pointer ${
                      viewMode === 'bijection' ? 'bg-amber-500/20 text-amber-200' : 'text-slate-400 hover:text-slate-200'
                    }`}
                  >
                    12↔12 Primitive Bijection
                  </button>
                </div>
              </div>

              {viewMode === 'trace' ? (
                <div className="rounded border border-slate-800 bg-[#07090e] overflow-x-auto max-h-64 overflow-y-auto">
                  <table className="w-full text-xs font-mono text-left tabular-nums">
                    <thead className="sticky top-0 bg-slate-900 text-slate-400 border-b border-slate-800">
                      <tr>
                        <th className="px-3 py-1.5">#</th>
                        <th className="px-3 py-1.5">Glyph</th>
                        <th className="px-3 py-1.5">Opcode</th>
                        <th className="px-3 py-1.5">Action</th>
                        <th className="px-3 py-1.5">Depth</th>
                        <th className="px-3 py-1.5">Register</th>
                        <th className="px-3 py-1.5">Carrier</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-slate-800/70">
                      {result.bankedSteps.map((st) => {
                        const regStr =
                          Object.entries(st.register)
                            .map(([k, v]) => `${k}:${v}`)
                            .join(', ') || '∅';
                        return (
                          <tr key={st.step} className="hover:bg-slate-900/40">
                            <td className="px-3 py-1 text-slate-500">{st.step}</td>
                            <td className="px-3 py-1 text-amber-300 text-sm">{st.glyph}</td>
                            <td className="px-3 py-1 text-slate-200">{st.opcode}</td>
                            <td className="px-3 py-1">
                              <span
                                className={
                                  st.bankAction === 'split'
                                    ? 'text-cyan-300'
                                    : st.bankAction === 'fuse'
                                    ? 'text-emerald-300'
                                    : st.bankAction === 'clear'
                                    ? 'text-rose-300'
                                    : 'text-slate-400'
                                }
                              >
                                {st.bankAction}
                              </span>
                            </td>
                            <td className="px-3 py-1 text-slate-300">{st.frameDepth}</td>
                            <td className="px-3 py-1 text-slate-300">{regStr}</td>
                            <td className="px-3 py-1">
                              <StateChip mask={st.maskState} />
                            </td>
                          </tr>
                        );
                      })}
                    </tbody>
                  </table>
                </div>
              ) : (
                <div className="overflow-x-auto rounded border border-slate-800 bg-[#07090e] max-h-64 overflow-y-auto">
                  <table className="w-full text-xs text-left tabular-nums">
                    <thead className="sticky top-0 bg-slate-900 text-slate-400 border-b border-slate-800">
                      <tr>
                        <th className="px-3 py-1.5">Idx</th>
                        <th className="px-3 py-1.5">Glyph</th>
                        <th className="px-3 py-1.5">Opcode</th>
                        <th className="px-3 py-1.5">Family</th>
                        <th className="px-3 py-1.5">Primitive</th>
                        <th className="px-3 py-1.5">Role</th>
                      </tr>
                    </thead>
                    <tbody className="divide-y divide-slate-800/70">
                      {opcodes.map((op) => (
                        <tr key={op.index}>
                          <td className="px-3 py-1 font-mono text-slate-500">{op.index}</td>
                          <td className="px-3 py-1 font-mono text-amber-300 text-sm">{op.glyph}</td>
                          <td className="px-3 py-1 font-mono text-slate-200">{op.opcode}</td>
                          <td className="px-3 py-1 font-mono text-violet-300">{op.family}</td>
                          <td className="px-3 py-1 text-slate-200">{op.primitive}</td>
                          <td className="px-3 py-1 text-slate-400">{op.role}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              )}
            </div>
          </div>
        )}
      </section>
    </div>
  );
};
