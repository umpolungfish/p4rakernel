import React, { useEffect, useState } from 'react';
import { CheckCircle2, AlertTriangle } from 'lucide-react';
import { BelnapDiamondSvg } from './Infographics';
import { getBelnapAudit } from '../lib/workbenchApi';

type Belnap = 'N' | 'T' | 'F' | 'B';

interface BelnapAudit {
  frobeniusClosureHolds: boolean;
  frobeniusWitnesses: { s: Belnap; incS: Belnap; incIncS: Belnap; equal: boolean }[];
  excludedMiddleResults: {
    v: Belnap;
    notV: Belnap;
    tjoinVNotV: Belnap;
    inCentre: boolean;
    isClassical: boolean;
  }[];
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

const VALS: Belnap[] = ['N', 'T', 'F', 'B'];

function valClass(v: Belnap): string {
  switch (v) {
    case 'T':
      return 'text-emerald-300 bg-emerald-500/15 border-emerald-500/40';
    case 'F':
      return 'text-rose-300 bg-rose-500/15 border-rose-500/40';
    case 'B':
      return 'text-amber-300 bg-amber-500/15 border-amber-500/40';
    case 'N':
      return 'text-slate-300 bg-slate-800/80 border-slate-600/50';
  }
}

export const BelnapPanel: React.FC = () => {
  const [audit, setAudit] = useState<BelnapAudit | null>(null);
  const [diagramMode, setDiagramMode] = useState<'frobenius' | 'classical' | 'centre'>('frobenius');
  const [selectedTable, setSelectedTable] = useState<'tjoin' | 'tmeet' | 'band' | 'bor'>('tjoin');

  useEffect(() => {
    setAudit(getBelnapAudit());
  }, []);

  if (!audit) {
    return (
      <div className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-6 text-xs text-slate-400">
        Loading Belnap FOUR verification…
      </div>
    );
  }

  const table = audit.tables[selectedTable];

  return (
    <div className="space-y-5">
      {/* Section 1: Interactive Bilattice Diamond + Theorem Witnesses */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div>
            <h2 className="text-base font-semibold text-slate-100">
              Belnap FOUR Bilattice · Frobenius Closure &amp; Cuts
            </h2>
            <p className="text-xs text-slate-400">
              Inc<sup>2</sup> = Inc · ClassicalRestriction (v ≠ B) · DeMorganBooleanCentre (v ∨ ¬v = T)
            </p>
          </div>
          <div className="inline-flex rounded border border-slate-700 bg-[#07090e] p-0.5 text-xs font-mono">
            {(
              [
                ['frobenius', <>Inc<sup>2</sup> = Inc</>],
                ['classical', 'Classical Cut'],
                ['centre', 'Boolean Centre'],
              ] as const
            ).map(([m, lbl]) => (
              <button
                key={m}
                type="button"
                onClick={() => setDiagramMode(m)}
                className={`px-3 py-1 rounded cursor-pointer whitespace-nowrap ${
                  diagramMode === m ? 'bg-amber-500/20 text-amber-200' : 'text-slate-400 hover:text-slate-200'
                }`}
              >
                {lbl}
              </button>
            ))}
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-start">
          {/* Interactive Diamond SVG */}
          <div className="lg:col-span-5 rounded border border-slate-800 bg-[#07090e] p-3">
            <BelnapDiamondSvg mode={diagramMode} />
          </div>

          {/* Right: Compact Matrices */}
          <div className="lg:col-span-7 space-y-4">
            <div className="grid grid-cols-2 sm:grid-cols-4 gap-2">
              {audit.frobeniusWitnesses.map((w) => (
                <div
                  key={w.s}
                  className="rounded border border-slate-800 bg-[#07090e] p-2.5 text-xs font-mono flex flex-col gap-1.5"
                >
                  <div className="flex items-center justify-between">
                    <span className={`px-1.5 py-0.5 rounded border ${valClass(w.s)}`}>{w.s}</span>
                    <CheckCircle2 className="w-3.5 h-3.5 text-emerald-400" />
                  </div>
                  <div className="text-[11px] text-slate-400">
                    Inc={w.incS} · Inc<sup>2</sup>={w.incIncS}
                  </div>
                </div>
              ))}
            </div>

            <div className="overflow-x-auto rounded border border-slate-800 bg-[#07090e]">
              <table className="w-full text-xs font-mono text-left">
                <thead className="bg-slate-900 text-slate-400 border-b border-slate-800">
                  <tr>
                    <th className="px-3 py-1.5">v</th>
                    <th className="px-3 py-1.5">¬v</th>
                    <th className="px-3 py-1.5">v ∨<sub>t</sub> ¬v</th>
                    <th className="px-3 py-1.5">v ≠ B</th>
                    <th className="px-3 py-1.5">inCentre</th>
                  </tr>
                </thead>
                <tbody className="divide-y divide-slate-800/70">
                  {audit.excludedMiddleResults.map((row) => (
                    <tr key={row.v} className={row.v === 'N' ? 'bg-amber-500/5' : ''}>
                      <td className="px-3 py-1.5">
                        <span className={`px-1.5 py-0.5 rounded border ${valClass(row.v)}`}>{row.v}</span>
                      </td>
                      <td className="px-3 py-1.5 text-slate-300">{row.notV}</td>
                      <td className="px-3 py-1.5 text-slate-300">{row.tjoinVNotV}</td>
                      <td className="px-3 py-1.5">
                        <span className={row.isClassical ? 'text-emerald-400' : 'text-rose-400'}>
                          {String(row.isClassical)}
                        </span>
                      </td>
                      <td className="px-3 py-1.5">
                        <span className={row.inCentre ? 'text-emerald-400' : 'text-rose-400'}>
                          {String(row.inCentre)}
                        </span>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>

            <div className="grid grid-cols-1 sm:grid-cols-2 gap-2 text-xs font-mono">
              <div className="rounded border border-slate-800 bg-[#07090e] px-3 py-2 flex justify-between">
                <span className="text-slate-400">the_two_cuts_differ (N)</span>
                <span className="text-amber-300">{String(audit.theTwoCutsDifferAtN)}</span>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] px-3 py-2 flex justify-between">
                <span className="text-slate-400">inclClassical ⊣ switch</span>
                <span className="text-emerald-400">{String(audit.classicalRestrictionAdjunctionHolds)}</span>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] px-3 py-2 flex justify-between">
                <span className="text-slate-400">inclCentre ⊣ boolSwitch</span>
                <span className="text-emerald-400">{String(audit.booleanCentreAdjunctionHolds)}</span>
              </div>
              <div className="rounded border border-slate-800 bg-[#07090e] px-3 py-2 flex justify-between">
                <span className="text-slate-400">infoLE adjunction fails</span>
                <span className="inline-flex items-center gap-1 text-amber-300">
                  <AlertTriangle className="w-3 h-3" />
                  {String(audit.infoAdjunctionFails)}
                </span>
              </div>
            </div>
          </div>
        </div>
      </section>

      {/* Section 2: Color-Coded 4x4 Cayley Matrix */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <h2 className="text-sm font-semibold text-slate-100">
            Belnap FOUR Cayley Heatmap
          </h2>
          <div className="flex gap-1.5">
            {(
              [
                ['tjoin', <>tjoin (∨<sub>t</sub>)</>],
                ['tmeet', <>tmeet (∧<sub>t</sub>)</>],
                ['band', 'band (dom)'],
                ['bor', 'bor (dom)'],
              ] as const
            ).map(([key, label]) => (
              <button
                key={key}
                type="button"
                onClick={() => setSelectedTable(key)}
                className={`px-3 py-1 rounded border text-xs font-mono cursor-pointer whitespace-nowrap ${
                  selectedTable === key
                    ? 'border-amber-500/60 bg-amber-500/15 text-amber-200'
                    : 'border-slate-800 bg-[#07090e] text-slate-400 hover:text-slate-200'
                }`}
              >
                {label}
              </button>
            ))}
          </div>
        </div>

        <div className="overflow-x-auto rounded border border-slate-800 bg-[#07090e] max-w-md">
          <table className="w-full text-xs font-mono text-center">
            <thead className="bg-slate-900 text-slate-400 border-b border-slate-800">
              <tr>
                <th className="px-3 py-2 text-left">{selectedTable}</th>
                {VALS.map((v) => (
                  <th key={v} className="px-3 py-2">{v}</th>
                ))}
              </tr>
            </thead>
            <tbody className="divide-y divide-slate-800/70">
              {VALS.map((row) => (
                <tr key={row}>
                  <td className="px-3 py-2 text-left font-semibold text-slate-300 bg-slate-900/50">{row}</td>
                  {VALS.map((col) => {
                    const cell = table[row][col];
                    return (
                      <td key={col} className="px-3 py-2">
                        <span className={`inline-block w-8 py-1 rounded border font-semibold ${valClass(cell)}`}>
                          {cell}
                        </span>
                      </td>
                    );
                  })}
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>
    </div>
  );
};
