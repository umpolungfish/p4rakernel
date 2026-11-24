import React, { useEffect, useState } from 'react';
import { Play, RefreshCw } from 'lucide-react';
import { StateChip } from './StateChip';
import { OrganismCycleWheelSvg, ToroidalCosetWheelSvg } from './Infographics';
import { runOrganismCycle, runOrganismTorus } from '../lib/workbenchApi';

interface Compartment {
  id: string;
  depth: number;
  mask: number;
  label: string;
  phase: string;
  evidence: {
    support: 0 | 1;
    refutation: 0 | 1;
    belnap: 'N' | 'T' | 'F' | 'B';
  };
  parentMask: number;
}

interface CycleTrace {
  steps: number;
  initialMask: number;
  compartments: Compartment[];
  constitutiveSequence: number[];
  closedToB: boolean;
}

interface TorusReport {
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

export const OrganismPanel: React.FC = () => {
  const [steps, setSteps] = useState(6);
  const [startMask, setStartMask] = useState(8);
  const [trace, setTrace] = useState<CycleTrace | null>(null);
  const [selectedMask, setSelectedMask] = useState<number | undefined>(8);

  const [sourceN, setSourceN] = useState('1099511627779');
  const [torus, setTorus] = useState<TorusReport | null>(null);

  const runCycle = () => {
    const d = runOrganismCycle(steps, startMask);
    setTrace(d);
    setSelectedMask(d.compartments[0]?.mask ?? startMask);
  };

  const runTorus = (val = sourceN) => {
    setTorus(runOrganismTorus(val));
  };

  useEffect(() => {
    runCycle();
  }, [steps, startMask]);

  useEffect(() => {
    runTorus(sourceN);
  }, []);

  return (
    <div className="space-y-5">
      {/* Section 1: Organism Constitutive Cycle Wheel */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              Dialetheic Organism Constitutive Cycle
            </h2>
            <p className="text-xs text-slate-400 font-mono">
              8 (⌈B⌋) → 0 → 1 → 3 → 7 → 15 → 8 · [support, refutation] evidence rails
            </p>
          </div>
          <div className="flex items-center gap-2.5 text-xs">
            <input
              type="number"
              min={1}
              max={24}
              value={steps}
              onChange={(e) => setSteps(Number(e.target.value))}
              aria-label="Cycle steps"
              className="w-16 rounded border border-slate-700 bg-[#07090e] px-2 py-1 font-mono text-slate-100 tabular-nums"
            />
            <select
              value={startMask}
              onChange={(e) => setStartMask(Number(e.target.value))}
              className="rounded border border-slate-700 bg-[#07090e] px-2 py-1 font-mono text-slate-100"
            >
              <option value={8}>8 (⌈B⌋)</option>
              <option value={0}>0 (∅)</option>
              <option value={1}>1 (N)</option>
              <option value={3}>3 (N,T)</option>
              <option value={7}>7 (N,T,F)</option>
              <option value={15}>15 (N,T,F,B)</option>
            </select>
            <button
              type="button"
              onClick={runCycle}
              className="inline-flex items-center gap-1.5 rounded bg-amber-500/20 border border-amber-500/40 px-3 py-1 text-xs font-medium text-amber-200 hover:bg-amber-500/30 cursor-pointer whitespace-nowrap"
            >
              <RefreshCw className="w-3 h-3" />
              Grow
            </button>
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
          <div className="lg:col-span-5 rounded border border-slate-800 bg-[#07090e] p-3">
            <OrganismCycleWheelSvg activeMask={selectedMask} />
          </div>

          <div className="lg:col-span-7 grid grid-cols-1 sm:grid-cols-2 gap-2.5">
            {trace?.compartments.map((c, idx) => {
              const active = selectedMask === c.mask;
              return (
                <button
                  key={c.id}
                  type="button"
                  onClick={() => setSelectedMask(c.mask)}
                  onMouseEnter={() => setSelectedMask(c.mask)}
                  className={`rounded border p-3 text-left flex flex-col justify-between gap-2 transition-colors cursor-pointer ${
                    active
                      ? 'border-amber-500/60 bg-amber-500/10'
                      : 'border-slate-800 bg-[#07090e] hover:border-slate-700'
                  }`}
                >
                  <div className="flex items-center justify-between w-full">
                    <span className="text-[11px] font-mono text-slate-400 tabular-nums">
                      step {idx + 1} · d={c.depth}
                    </span>
                    <StateChip mask={c.mask} />
                  </div>
                  <div className="text-xs font-medium text-slate-200">{c.phase}</div>
                  <div className="flex items-center justify-between w-full text-[11px] font-mono pt-1.5 border-t border-slate-800/80 tabular-nums">
                    <span className="text-slate-400">
                      rail [{c.evidence.support},{c.evidence.refutation}]
                    </span>
                    <span className="text-amber-300">{c.evidence.belnap}</span>
                  </div>
                </button>
              );
            })}
          </div>
        </div>
      </section>

      {/* Section 2: Toroidal Division & Odd-Coset Wheel */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              Toroidal Division &amp; Odd-Coset Modular Wheel
            </h2>
            <p className="text-xs text-slate-400 font-mono">
              pq ≡ N (mod 2<sup>m</sup>) across all 4 odd coset representatives
            </p>
          </div>
          <div className="flex flex-wrap gap-1.5">
            {[
              { label: '32-bit', val: '3221225473' },
              { label: '41-bit', val: '1099511627779' },
              { label: '128-bit', val: '340282366920938463463374607431768211297' },
            ].map((p) => (
              <button
                key={p.label}
                type="button"
                onClick={() => {
                  setSourceN(p.val);
                  runTorus(p.val);
                }}
                className="px-2.5 py-1 rounded border border-slate-700 bg-[#07090e] hover:border-amber-500/50 text-xs font-mono text-slate-300 cursor-pointer whitespace-nowrap"
              >
                {p.label}
              </button>
            ))}
          </div>
        </div>

        <div className="flex gap-2 mb-4">
          <input
            type="text"
            value={sourceN}
            onChange={(e) => setSourceN(e.target.value)}
            className="flex-1 rounded border border-slate-700 bg-[#07090e] px-3 py-1.5 text-xs font-mono text-slate-100 tabular-nums"
            placeholder="Odd integer N ≥ 3"
          />
          <button
            type="button"
            onClick={() => runTorus(sourceN)}
            className="inline-flex items-center gap-1.5 rounded bg-amber-500/20 border border-amber-500/40 px-3 py-1.5 text-xs font-medium text-amber-200 hover:bg-amber-500/30 cursor-pointer whitespace-nowrap"
          >
            <Play className="w-3.5 h-3.5" />
            Analyze
          </button>
        </div>

        {torus && !torus.valid && (
          <div className="rounded border border-rose-500/40 bg-rose-500/10 p-3 text-xs font-mono text-rose-300">
            {torus.error}
          </div>
        )}

        {torus && torus.valid && (
          <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
            <div className="lg:col-span-5 rounded border border-slate-800 bg-[#07090e] p-3">
              <ToroidalCosetWheelSvg
                modulus2m={torus.modulus2m}
                nMod2m={torus.nMod2m}
                cosets={torus.cosets}
              />
            </div>

            <div className="lg:col-span-7 space-y-3">
              <div className="grid grid-cols-2 sm:grid-cols-4 gap-2.5 text-xs font-mono tabular-nums">
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400">Width</div>
                  <div className="text-slate-100 font-semibold mt-0.5">{torus.bitWidth} bits</div>
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400">Modulus 2<sup>m</sup></div>
                  <div className="text-slate-100 font-semibold mt-0.5">2<sup>{torus.m}</sup> = {torus.modulus2m}</div>
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400">N mod 2<sup>m</sup></div>
                  <div className="text-cyan-300 font-semibold mt-0.5">{torus.nMod2m}</div>
                </div>
                <div className="rounded border border-slate-800 bg-[#07090e] p-2.5">
                  <div className="text-[11px] text-slate-400">Factor Check</div>
                  <div className="text-emerald-300 font-semibold mt-0.5">
                    {torus.trialFactor
                      ? `${torus.trialFactor.p}×${torus.trialFactor.q}`
                      : torus.bitWidth <= 40
                      ? 'prime'
                      : '>40b'}
                  </div>
                </div>
              </div>

              <div className="overflow-x-auto rounded border border-slate-800 bg-[#07090e]">
                <table className="w-full text-xs font-mono text-left tabular-nums">
                  <thead className="bg-slate-900 text-slate-400 border-b border-slate-800">
                    <tr>
                      <th className="px-3 py-1.5">p mod 2<sup>m</sup></th>
                      <th className="px-3 py-1.5">q ≡ N·p<sup>−1</sup> mod 2<sup>m</sup></th>
                      <th className="px-3 py-1.5">(p·q) mod 2<sup>m</sup></th>
                      <th className="px-3 py-1.5">Status</th>
                    </tr>
                  </thead>
                  <tbody className="divide-y divide-slate-800/70">
                    {torus.cosets.map((c) => (
                      <tr key={c.pResidue}>
                        <td className="px-3 py-1.5 text-slate-200">{c.pResidue}</td>
                        <td className="px-3 py-1.5 text-amber-300">{c.qResidue}</td>
                        <td className="px-3 py-1.5 text-slate-300">{c.productMod2m}</td>
                        <td className="px-3 py-1.5">
                          <span className={c.matchesNMod2m ? 'text-emerald-400' : 'text-rose-400'}>
                            {c.matchesNMod2m ? 'exact' : 'mismatch'}
                          </span>
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          </div>
        )}
      </section>
    </div>
  );
};
