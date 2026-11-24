import React, { useEffect, useMemo, useState } from 'react';
import { FileCode2, Search, CheckCircle2, AlertCircle } from 'lucide-react';
import {
  SubsystemBarChartSvg,
  ImportHubRadialSvg,
  MsaComparativeChartSvg,
  AbcEnclosureChartSvg,
} from './CorpusInfographics';
import {
  fetchCorpusDocument,
  fetchCorpusOverview,
  queryCorpusDocs,
} from '../lib/workbenchApi';

interface MsaEntry {
  seq_len: number;
  aa_sequence: string;
  winding: number;
  contacts: number;
  subunits: number;
  frobenius: boolean;
  confidence: number;
  primitives_activated: string[];
  num_activated: number;
}

interface MsaFamily {
  conserved_primitives: string[];
  variable_primitives: string[];
  conservation_rate: number;
  [species: string]: MsaEntry | string[] | number;
}

interface CorpusDoc {
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

interface CorpusStats {
  totalFiles: number;
  leanFiles: number;
  sorryFreeLeanFiles: number;
  openConjectureLeanFiles: number;
  totalTheorems: number;
  totalDefs: number;
  categories: { category: string; files: number; theorems: number; sorryFree: number }[];
  topImportedModules: { module: string; count: number }[];
}

interface AbcReadings {
  method?: string;
  terms?: number;
  readings?: {
    c_max: number;
    lean_window_index: number;
    ordered_triples: number;
    epsilon: string;
    lower: string;
    upper: string;
    lower_witness: number[];
  }[];
}

export const CorpusPanel: React.FC = () => {
  const [stats, setStats] = useState<CorpusStats | null>(null);
  const [msa, setMsa] = useState<Record<string, MsaFamily>>({});
  const [abc, setAbc] = useState<AbcReadings | null>(null);
  const [docs, setDocs] = useState<CorpusDoc[]>([]);
  const [query, setQuery] = useState('');
  const [category, setCategory] = useState('all');
  const [onlyVerified, setOnlyVerified] = useState(false);

  const [activeDoc, setActiveDoc] = useState<CorpusDoc | null>(null);
  const [docContent, setDocContent] = useState<string>('');
  const [importedBy, setImportedBy] = useState<string[]>([]);

  useEffect(() => {
    fetchCorpusOverview()
      .then((data) => {
        if (!data) return;
        setStats(data.stats);
        setMsa(data.msa as Record<string, MsaFamily>);
        setAbc(data.abc as AbcReadings);
      })
      .catch(() => {});
  }, []);

  useEffect(() => {
    const timer = setTimeout(() => {
      queryCorpusDocs(query, category, onlyVerified)
        .then((list) => {
          setDocs(list);
          if (!activeDoc && list.length > 0) {
            selectDoc(list[0]);
          }
        })
        .catch(() => {});
    }, 60);
    return () => clearTimeout(timer);
  }, [query, category, onlyVerified]);

  const selectDoc = (doc: CorpusDoc) => {
    setActiveDoc(doc);
    fetchCorpusDocument(doc.relPath)
      .then((d) => {
        setDocContent(d.content ?? d.error ?? '');
        setImportedBy(d.importedBy ?? []);
      })
      .catch(() => {});
  };

  const openModuleByImport = (mod: string) => {
    const targetRel = `p4ramill/${mod.replace(/\./g, '/')}.lean`;
    const match = docs.find((d) => d.relPath === targetRel);
    if (match) {
      selectDoc(match);
    } else {
      fetchCorpusDocument(targetRel)
        .then((d) => {
          if (d.ok && d.meta) {
            setActiveDoc(d.meta);
            setDocContent(d.content ?? '');
            setImportedBy(d.importedBy ?? []);
          }
        })
        .catch(() => {});
    }
  };

  const msaChartRows = useMemo(() => {
    const rows: { label: string; winding: number; contacts: number; activated: number }[] = [];
    for (const [familyName, family] of Object.entries(msa)) {
      const shortFam = familyName.slice(0, 6);
      for (const [sp, val] of Object.entries(family)) {
        if (
          sp !== 'conserved_primitives' &&
          sp !== 'variable_primitives' &&
          sp !== 'conservation_rate' &&
          typeof val === 'object' &&
          val !== null &&
          !Array.isArray(val)
        ) {
          const entry = val as MsaEntry;
          rows.push({
            label: `${shortFam}·${sp.slice(0, 8)}`,
            winding: entry.winding,
            contacts: entry.contacts,
            activated: entry.num_activated,
          });
        }
      }
    }
    return rows;
  }, [msa]);

  return (
    <div className="space-y-5">
      {/* 1. Visual Subsystem Bar Chart & Radial Import Hub Graph */}
      {stats && (
        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
            <div>
              <h2 className="text-base font-semibold text-slate-100">
                p4ramill / Imscribing Formalization Corpus Topology
              </h2>
              <p className="text-xs text-slate-400 font-mono tabular-nums">
                {stats.leanFiles} Lean modules · {stats.sorryFreeLeanFiles} zero-sorry · {stats.openConjectureLeanFiles} threshold · {stats.totalTheorems.toLocaleString()} theorems
              </p>
            </div>
            {category !== 'all' && (
              <button
                type="button"
                onClick={() => setCategory('all')}
                className="px-2.5 py-1 rounded border border-amber-500/50 bg-amber-500/15 text-xs font-mono text-amber-200 cursor-pointer"
              >
                Clear filter: {category}
              </button>
            )}
          </div>

          <div className="grid grid-cols-1 lg:grid-cols-12 gap-5 items-center">
            <div className="lg:col-span-7 rounded border border-slate-800 bg-[#07090e] p-3">
              <SubsystemBarChartSvg
                categories={stats.categories}
                activeCategory={category}
                onSelectCategory={setCategory}
              />
            </div>
            <div className="lg:col-span-5 rounded border border-slate-800 bg-[#07090e] p-3">
              <ImportHubRadialSvg
                hubs={stats.topImportedModules}
                onSelectHub={openModuleByImport}
              />
            </div>
          </div>
        </section>
      )}

      {/* 2. Searchable Lean 4 Code & Import-Graph Explorer */}
      <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
        <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
          <div className="flex items-center gap-3">
            <h2 className="text-sm font-semibold text-slate-100 tabular-nums">
              Module &amp; Theorem Explorer ({docs.length} matching)
            </h2>
            <label className="inline-flex items-center gap-1.5 text-xs text-slate-300 cursor-pointer">
              <input
                type="checkbox"
                checked={onlyVerified}
                onChange={(e) => setOnlyVerified(e.target.checked)}
                className="accent-amber-400"
              />
              Zero-sorry only
            </label>
          </div>
          <div className="flex gap-2 w-full sm:w-auto">
            <select
              value={category}
              onChange={(e) => setCategory(e.target.value)}
              className="rounded border border-slate-700 bg-[#07090e] px-2.5 py-1.5 text-xs text-slate-200"
            >
              <option value="all">All subsystems</option>
              {stats?.categories.map((c) => (
                <option key={c.category} value={c.category}>
                  {c.category} ({c.files})
                </option>
              ))}
            </select>
            <div className="relative flex-1 sm:w-72">
              <Search className="w-3.5 h-3.5 text-slate-500 absolute left-2.5 top-2.5" />
              <input
                type="text"
                value={query}
                onChange={(e) => setQuery(e.target.value)}
                placeholder="Search file, namespace, theorem…"
                className="w-full rounded border border-slate-700 bg-[#07090e] pl-8 pr-3 py-1.5 text-xs text-slate-100"
              />
            </div>
          </div>
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-4">
          <div className="lg:col-span-4 max-h-[460px] overflow-y-auto rounded border border-slate-800 bg-[#07090e] divide-y divide-slate-800/60">
            {docs.map((doc) => {
              const active = activeDoc?.relPath === doc.relPath;
              return (
                <button
                  key={doc.relPath}
                  type="button"
                  onClick={() => selectDoc(doc)}
                  className={`w-full text-left px-3 py-2 text-xs transition-colors cursor-pointer ${
                    active ? 'bg-amber-500/15 text-amber-200' : 'hover:bg-slate-900 text-slate-300'
                  }`}
                >
                  <div className="flex items-center justify-between gap-2">
                    <span className="inline-flex items-center gap-1.5 font-mono truncate">
                      <FileCode2 className="w-3.5 h-3.5 shrink-0 text-slate-500" />
                      {doc.title}
                    </span>
                    <span
                      className={`text-[10px] font-mono shrink-0 ${
                        doc.sorryCount === 0 ? 'text-emerald-400' : 'text-amber-300'
                      }`}
                    >
                      {doc.sorryCount === 0 ? '0 sorry' : `${doc.sorryCount} sorry`}
                    </span>
                  </div>
                  <div className="text-[10px] font-mono text-slate-500 mt-0.5 flex justify-between tabular-nums">
                    <span>{doc.category}</span>
                    <span>
                      {doc.theorems.length} thms · {doc.lines}L
                    </span>
                  </div>
                </button>
              );
            })}
          </div>

          <div className="lg:col-span-8 rounded border border-slate-800 bg-[#07090e] flex flex-col max-h-[460px]">
            <div className="px-3 py-2 border-b border-slate-800 text-xs font-mono text-slate-400 flex flex-wrap items-center justify-between gap-2 tabular-nums">
              <span className="text-slate-200">{activeDoc?.relPath ?? 'Select a module'}</span>
              {activeDoc && (
                <div className="flex items-center gap-2.5">
                  {activeDoc.namespaceName && (
                    <span className="text-amber-300">ns {activeDoc.namespaceName}</span>
                  )}
                  <span className="inline-flex items-center gap-1">
                    {activeDoc.sorryCount === 0 ? (
                      <CheckCircle2 className="w-3.5 h-3.5 text-emerald-400" />
                    ) : (
                      <AlertCircle className="w-3.5 h-3.5 text-amber-400" />
                    )}
                    {activeDoc.sorryCount} sorry
                  </span>
                  <span>{(activeDoc.bytes / 1024).toFixed(1)} KB</span>
                </div>
              )}
            </div>

            {activeDoc && (activeDoc.imports.length > 0 || activeDoc.theorems.length > 0 || importedBy.length > 0) && (
              <div className="px-3 py-2 border-b border-slate-800/80 bg-slate-900/40 text-[11px] font-mono space-y-1">
                {activeDoc.imports.length > 0 && (
                  <div className="flex flex-wrap items-center gap-1">
                    <span className="text-slate-500 mr-1">imports:</span>
                    {activeDoc.imports.slice(0, 10).map((imp) => (
                      <button
                        key={imp}
                        type="button"
                        onClick={() => imp.startsWith('Imscribing.') && openModuleByImport(imp)}
                        className={`px-1.5 py-0.5 rounded border ${
                          imp.startsWith('Imscribing.')
                            ? 'border-cyan-500/30 bg-cyan-500/10 text-cyan-200 hover:border-cyan-400 cursor-pointer'
                            : 'border-slate-800 text-slate-400'
                        }`}
                      >
                        {imp}
                      </button>
                    ))}
                  </div>
                )}
                {importedBy.length > 0 && (
                  <div className="text-slate-400 truncate">
                    <span className="text-slate-500 mr-1">used by ({importedBy.length}):</span>
                    {importedBy
                      .slice(0, 5)
                      .map((p) => p.replace(/^p4ramill\/Imscribing\//, ''))
                      .join(' · ')}
                  </div>
                )}
                {activeDoc.theorems.length > 0 && (
                  <div className="text-slate-400 truncate">
                    <span className="text-slate-500 mr-1">theorems ({activeDoc.theorems.length}):</span>
                    {activeDoc.theorems.slice(0, 10).join(', ')}
                  </div>
                )}
              </div>
            )}

            <pre className="p-3 text-[11px] font-mono text-slate-300 overflow-auto leading-relaxed whitespace-pre-wrap">
              {docContent}
            </pre>
          </div>
        </div>
      </section>

      {/* 3. Biological MSA & ABC Rational Log Enclosure Charts */}
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-5">
        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <h2 className="text-sm font-semibold text-slate-100 mb-3">
            Protein MSA Winding &amp; Contact Topology
          </h2>
          <div className="rounded border border-slate-800 bg-[#07090e] p-3 mb-3">
            <MsaComparativeChartSvg rows={msaChartRows} />
          </div>
          <div className="flex flex-wrap gap-3 text-[11px] font-mono text-slate-400 tabular-nums">
            {Object.entries(msa).map(([protein, family]) => (
              <span key={protein}>
                {protein.replace(/_/g, ' ')}: <strong className="text-emerald-400">{(family.conservation_rate * 100).toFixed(1)}%</strong>
              </span>
            ))}
          </div>
        </section>

        <section className="rounded-lg border border-slate-800/80 bg-[#0c1017] p-5">
          <h2 className="text-sm font-semibold text-slate-100 mb-3">
            ABC Spectral Log Enclosures ({abc?.readings?.length ?? 0} windows)
          </h2>
          {abc?.readings && (
            <div className="rounded border border-slate-800 bg-[#07090e] p-3">
              <AbcEnclosureChartSvg readings={abc.readings} />
            </div>
          )}
        </section>
      </div>
    </div>
  );
};
