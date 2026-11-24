import React, { useEffect, useState } from 'react';
import { CheckCircle2, ShieldAlert, ShieldCheck } from 'lucide-react';
import {
  ImscribingRadarSvg,
  IuttFlowSvg,
  FineStructureGaugeSvg,
  OuroboricChannelSvg,
} from './Infographics';
import {
  getImscribingMeta,
  runImscribingEvaluate,
  runIuttEvaluate,
  runOuroboricSimulate,
} from '../lib/workbenchApi';

interface PrimitiveAxis {
  key: string;
  symbol: string;
  name: string;
  values: string[];
}

interface PresetSpec {
  label: string;
  source: string;
  tuple: Record<string, string>;
}

interface FineStructure {
  d: number;
  dSq: number;
  cartanAxes: number;
  nonAbelianAxes: number;
  integerCore: number;
  tiltCorrection: number;
  broadcastTerm: number;
  computedAlphaInv: number;
  codata2022: number;
  residual: number;
  ppm: number;
}

interface TupleEvalResult {
  a: Record<string, string>;
  b: Record<string, string>;
  meet: Record<string, string>;
  join: Record<string, string>;
  tensor: Record<string, string>;
  conflicts: string[];
  hammingDistance: number;
  primitiveDistance: number;
  consciousnessA: { phiCGate: boolean; kSlowGate: boolean; score: number };
  consciousnessB: { phiCGate: boolean; kSlowGate: boolean; score: number };
  probA: number;
  probB: number;
  frobeniusLaws: {
    muDeltaA_id: boolean;
    muDeltaB_id: boolean;
    muDeltaD_id: boolean;
  };
}

interface IuttResult {
  input: { bigT: boolean; bigF: boolean; smallT: boolean; smallF: boolean };
  erased: { bigT: boolean; bigF: boolean; smallT: boolean; smallF: boolean };
  toFourLabel: string;
  booleanShadow: 'T' | 'F';
  ternaryDecomposition: {
    matchesInput: boolean;
  };
  erasureIdempotent: boolean;
  filtrationObstruction: {
    atOne: { vec: number[]; degree: number; blindScalar: number; weightedJ2: number };
    atTwo: { vec: number[]; degree: number; blindScalar: number; weightedJ2: number };
    sameBlindScalar: boolean;
    distinctWeightedValues: boolean;
  };
}

interface OuroboricResult {
  transmitted: 'N' | 'T' | 'F' | 'B';
  aliceInfoMass: number;
  eveCoreflected: 'T' | 'F';
  eveInfoMass: number;
  tamperDetected: boolean;
  bobAmbientRead: string;
  bobInfoMass: number;
  losslessForBob: boolean;
}

export const ImscribingPanel: React.FC = () => {
  const [axes, setAxes] = useState<PrimitiveAxis[]>([]);
  const [presets, setPresets] = useState<Record<string, PresetSpec>>({});
  const [fineStructure, setFineStructure] = useState<FineStructure | null>(null);

  const [tupleA, setTupleA] = useState<Record<string, string> | null>(null);
  const [tupleB, setTupleB] = useState<Record<string, string> | null>(null);
  const [evalRes, setEvalRes] = useState<TupleEvalResult | null>(null);

  const [iuttInput, setIuttInput] = useState({ bigT: true, bigF: true, smallT: true, smallF: true });
  const [iuttRes, setIuttRes] = useState<IuttResult | null>(null);

  const [keyState, setKeyState] = useState<'N' | 'T' | 'F' | 'B'>('B');
  const [ouroboric, setOuroboric] = useState<OuroboricResult | null>(null);

  useEffect(() => {
    const d = getImscribingMeta();
    setAxes(d.axes);
    setPresets(d.presets);
    setFineStructure(d.fineStructure);
    if (d.presets?.human_brain && d.presets?.replicative_core) {
      setTupleA(d.presets.human_brain.tuple);
      setTupleB(d.presets.replicative_core.tuple);
    }
  }, []);

  useEffect(() => {
    if (!tupleA || !tupleB) return;
    setEvalRes(runImscribingEvaluate(tupleA, tupleB));
  }, [tupleA, tupleB]);

  useEffect(() => {
    setIuttRes(runIuttEvaluate(iuttInput));
  }, [iuttInput]);

  useEffect(() => {
    setOuroboric(runOuroboricSimulate(keyState));
  }, [keyState]);

  const presetKeys = Object.keys(presets);

  return (
    <div className="space-y-5">
      {/* 1. 12-Primitive Radar & Tuple Algebra */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              12-Primitive Imscription Radar &amp; Frobenius Algebra
            </h2>
            <p className="text-xs text-slate-400">
              Algebra.lean · Frobenius.lean · Consciousness.lean · HowProbabilityArise.lean
            </p>
          </div>
          {evalRes && (
            <div className="flex items-center gap-3 text-xs font-mono text-emerald-300 tabular-nums">
              <span>μ<sub>A</sub>∘δ<sub>A</sub> = id ({String(evalRes.frobeniusLaws.muDeltaA_id)})</span>
              <span className="text-slate-600">·</span>
              <span>μ<sub>B</sub>∘δ<sub>B</sub> = id ({String(evalRes.frobeniusLaws.muDeltaB_id)})</span>
              <span className="text-slate-600">·</span>
              <span>μ<sub>D</sub>∘δ<sub>D</sub> = id ({String(evalRes.frobeniusLaws.muDeltaD_id)})</span>
            </div>
          )}
        </div>

        {tupleA && tupleB && (
          <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
            {/* Left: Radar Chart + 4 Metric Tiles */}
            <div className="lg:col-span-5 space-y-3">
              <div className="rounded border border-slate-800 bg-[#07090e] p-3">
                <ImscribingRadarSvg
                  axes={axes}
                  a={tupleA}
                  b={tupleB}
                  tensor={evalRes?.tensor ?? tupleA}
                />
              </div>

              {evalRes && (
                <div className="grid grid-cols-2 gap-2.5 text-xs font-mono tabular-nums">
                  <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                    <div className="text-[11px] text-slate-400">Hamming Conflicts</div>
                    <div className="text-slate-100 font-semibold mt-0.5">
                      {evalRes.hammingDistance}/12
                    </div>
                  </div>
                  <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                    <div className="text-[11px] text-slate-400">primitiveDistance</div>
                    <div className="text-amber-300 font-semibold mt-0.5">
                      {evalRes.primitiveDistance}
                    </div>
                  </div>
                  <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                    <div className="text-[11px] text-slate-400">Consciousness C(A/B)</div>
                    <div className="text-emerald-300 font-semibold mt-0.5">
                      {evalRes.consciousnessA.score} · {evalRes.consciousnessB.score}
                    </div>
                  </div>
                  <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                    <div className="text-[11px] text-slate-400">prob(A) · prob(B)</div>
                    <div className="text-slate-100 font-semibold mt-0.5">
                      {evalRes.probA} · {evalRes.probB}
                    </div>
                  </div>
                </div>
              )}
            </div>

            {/* Right: Presets + 12-Axis Interactive Matrix */}
            <div className="lg:col-span-7 space-y-3">
              <div className="grid grid-cols-1 sm:grid-cols-2 gap-3">
                <div>
                  <label className="block text-[11px] text-cyan-300 font-mono mb-1">Preset A</label>
                  <select
                    onChange={(e) => {
                      const p = presets[e.target.value];
                      if (p) setTupleA({ ...p.tuple });
                    }}
                    defaultValue="human_brain"
                    className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs text-slate-100"
                  >
                    {presetKeys.map((k) => (
                      <option key={k} value={k}>
                        {presets[k].label} — {presets[k].source}
                      </option>
                    ))}
                  </select>
                </div>
                <div>
                  <label className="block text-[11px] text-amber-300 font-mono mb-1">Preset B</label>
                  <select
                    onChange={(e) => {
                      const p = presets[e.target.value];
                      if (p) setTupleB({ ...p.tuple });
                    }}
                    defaultValue="replicative_core"
                    className="w-full rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs text-slate-100"
                  >
                    {presetKeys.map((k) => (
                      <option key={k} value={k}>
                        {presets[k].label} — {presets[k].source}
                      </option>
                    ))}
                  </select>
                </div>
              </div>

              <div className="overflow-x-auto rounded border border-slate-800 bg-[#07090e]">
                <table className="w-full text-xs font-mono text-left">
                  <thead className="bg-slate-900 text-slate-400 border-b border-slate-800">
                    <tr>
                      <th className="px-2.5 py-1.5">Axis</th>
                      <th className="px-2.5 py-1.5 text-cyan-300">A</th>
                      <th className="px-2.5 py-1.5 text-amber-300">B</th>
                      <th className="px-2.5 py-1.5">A∧B</th>
                      <th className="px-2.5 py-1.5">A∨B</th>
                      <th className="px-2.5 py-1.5 text-emerald-300">A⊗B</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-800/70">
                    {axes.map((ax) => {
                      const conflict = tupleA[ax.key] !== tupleB[ax.key];
                      const isBottleneck = ax.key === 'pol' || ax.key === 'fid';
                      return (
                        <tr key={ax.key} className={conflict ? 'bg-amber-500/5' : ''}>
                          <td className="px-2.5 py-1 text-slate-300 whitespace-nowrap">
                            <span className="text-amber-300 font-semibold mr-1">{ax.symbol}</span>
                            {ax.name}
                            {isBottleneck && <span className="ml-1 text-[10px] text-rose-400">min</span>}
                          </td>
                          <td className="px-2.5 py-1">
                            <select
                              value={tupleA[ax.key]}
                              onChange={(e) => setTupleA({ ...tupleA, [ax.key]: e.target.value })}
                              className="rounded border border-slate-700 bg-slate-900 px-2 py-0.5 text-base leading-tight text-cyan-300"
                            >
                              {ax.values.map((v) => (
                                <option key={v} value={v}>{v}</option>
                              ))}
                            </select>
                          </td>
                          <td className="px-2.5 py-1">
                            <select
                              value={tupleB[ax.key]}
                              onChange={(e) => setTupleB({ ...tupleB, [ax.key]: e.target.value })}
                              className="rounded border border-slate-700 bg-slate-900 px-2 py-0.5 text-base leading-tight text-amber-300"
                            >
                              {ax.values.map((v) => (
                                <option key={v} value={v}>{v}</option>
                              ))}
                            </select>
                          </td>
                          <td className="px-2.5 py-1 text-base text-slate-300">{evalRes?.meet[ax.key]}</td>
                          <td className="px-2.5 py-1 text-base text-slate-300">{evalRes?.join[ax.key]}</td>
                          <td className="px-2.5 py-1 text-base text-emerald-300 font-semibold">{evalRes?.tensor[ax.key]}</td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            </div>
          </div>
        )}
      </section>

      {/* 2. IUTT 4-Lane Schematic & Prop 18.1 Filtration Obstruction */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              IUTT 4-Lane Erasure &amp; Prop 18.1 j<sup>2</sup> Filtration
            </h2>
            <p className="text-xs text-slate-400">
              IUTT.lean · Reg16<sub>3</sub> → FOUR → BoolCentre · weighted evaluation obstruction
            </p>
          </div>
          <div className="flex flex-wrap gap-1.5 text-xs font-mono">
            {[
              { label: 'allLanes', s: { bigT: true, bigF: true, smallT: true, smallF: true } },
              { label: 'boundedDiscrepancy', s: { bigT: false, bigF: true, smallT: true, smallF: true } },
              { label: 'ambient', s: { bigT: false, bigF: false, smallT: true, smallF: true } },
              { label: 'both', s: { bigT: true, bigF: true, smallT: false, smallF: false } },
              { label: 'falsity', s: { bigT: false, bigF: true, smallT: false, smallF: false } },
            ].map((p) => (
              <button
                key={p.label}
                type="button"
                onClick={() => setIuttInput(p.s)}
                className="px-2.5 py-1 rounded border border-slate-700 bg-[#07090e] hover:border-amber-500/50 text-slate-200 cursor-pointer whitespace-nowrap"
              >
                {p.label}
              </button>
            ))}
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-center">
          <div className="lg:col-span-7 rounded border border-slate-800 bg-[#07090e] p-3">
            {iuttRes && (
              <IuttFlowSvg
                input={iuttInput}
                toFourLabel={iuttRes.toFourLabel}
                booleanShadow={iuttRes.booleanShadow}
              />
            )}
          </div>

          <div className="lg:col-span-5 space-y-3 text-xs font-mono">
            <div className="grid grid-cols-4 gap-2">
              {(
                [
                  ['bigT', 'T'],
                  ['bigF', 'F'],
                  ['smallT', 't'],
                  ['smallF', 'f'],
                ] as const
              ).map(([k, lbl]) => (
                <button
                  key={k}
                  type="button"
                  onClick={() => setIuttInput({ ...iuttInput, [k]: !iuttInput[k] })}
                  className={`rounded border px-2 py-2 text-center cursor-pointer transition-colors ${
                    iuttInput[k]
                      ? 'border-amber-400 bg-amber-500/15 text-amber-200'
                      : 'border-slate-800 bg-[#07090e] text-slate-500'
                  }`}
                >
                  <div className="text-sm font-bold">{lbl}</div>
                  <div className="text-[10px]">{iuttInput[k] ? '1' : '0'}</div>
                </button>
              ))}
            </div>

            {iuttRes && (
              <div className="rounded border border-slate-800 bg-[#07090e] p-3 space-y-2 tabular-nums">
                <div className="flex justify-between">
                  <span className="text-slate-400">eraseInformation → FOUR</span>
                  <span className="text-amber-300 font-semibold">{iuttRes.toFourLabel}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-slate-400">booleanShadow → Bool</span>
                  <span className="text-emerald-300 font-semibold">{iuttRes.booleanShadow}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-slate-400">ternary_recovery</span>
                  <span className="text-emerald-400">{String(iuttRes.ternaryDecomposition.matchesInput)}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-slate-400">erasure_idempotent</span>
                  <span className="text-emerald-400">{String(iuttRes.erasureIdempotent)}</span>
                </div>
                <div className="flex items-center gap-1.5 pt-2 border-t border-slate-800 text-emerald-400">
                  <CheckCircle2 className="w-3.5 h-3.5 shrink-0" />
                  <span>
                    weighted_does_not_factor ={' '}
                    {String(
                      iuttRes.filtrationObstruction.sameBlindScalar &&
                        iuttRes.filtrationObstruction.distinctWeightedValues
                    )}
                  </span>
                </div>
              </div>
            )}
          </div>
        </div>
      </section>

      {/* 3. Fine-Structure Constant Gauge & Ouroboric Key-Exchange Flow */}
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-5">
        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <h2 className="text-sm font-semibold text-slate-100 mb-3">
            Fine-Structure Constant Gauge (α<sup>−1</sup>, d = 12 SIC-POVM)
          </h2>
          {fineStructure && (
            <div className="rounded border border-slate-800 bg-[#07090e] p-3">
              <FineStructureGaugeSvg
                integerCore={fineStructure.integerCore}
                tiltCorrection={fineStructure.tiltCorrection}
                broadcastTerm={fineStructure.broadcastTerm}
                computedAlphaInv={fineStructure.computedAlphaInv}
                codata2022={fineStructure.codata2022}
                ppm={fineStructure.ppm}
              />
            </div>
          )}
        </section>

        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <div className="flex items-center justify-between gap-2 mb-3">
            <h2 className="text-sm font-semibold text-slate-100">
              Ouroboric Key-Exchange Channel
            </h2>
            <div className="flex gap-1">
              {(['N', 'T', 'F', 'B'] as const).map((s) => (
                <button
                  key={s}
                  type="button"
                  onClick={() => setKeyState(s)}
                  className={`px-2.5 py-1 rounded border text-xs font-mono cursor-pointer ${
                    keyState === s
                      ? 'border-amber-400 bg-amber-500/20 text-amber-200'
                      : 'border-slate-800 bg-[#07090e] text-slate-400 hover:text-slate-200'
                  }`}
                >
                  {s}
                </button>
              ))}
            </div>
          </div>

          {ouroboric && (
            <div className="space-y-2.5">
              <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                <OuroboricChannelSvg
                  transmitted={ouroboric.transmitted}
                  eveCoreflected={ouroboric.eveCoreflected}
                  aliceMass={ouroboric.aliceInfoMass}
                  eveMass={ouroboric.eveInfoMass}
                  tamperDetected={ouroboric.tamperDetected}
                />
              </div>
              <div
                className={`rounded border px-3 py-1.5 flex items-center gap-2 text-xs font-mono tabular-nums ${
                  ouroboric.tamperDetected
                    ? 'border-rose-500/40 bg-rose-500/10 text-rose-200'
                    : 'border-slate-800 bg-[#07090e] text-slate-300'
                }`}
              >
                {ouroboric.tamperDetected ? (
                  <>
                    <ShieldAlert className="w-3.5 h-3.5 text-rose-400 shrink-0" />
                    <span>
                      Tamper seal triggered: info_mass {ouroboric.aliceInfoMass} → {ouroboric.eveInfoMass}
                    </span>
                  </>
                ) : (
                  <>
                    <ShieldCheck className="w-3.5 h-3.5 text-slate-400 shrink-0" />
                    <span>Classical pole ({ouroboric.transmitted}) · send B or N to test intercept leak</span>
                  </>
                )}
              </div>
            </div>
          )}
        </section>
      </div>
    </div>
  );
};
