import React, { useState } from 'react';
import { Grid3X3, Terminal, Scale, Orbit, BookOpen, Layers, ExternalLink } from 'lucide-react';
import { Sixteen3Panel } from './components/Sixteen3Panel';
import { ImasmPanel } from './components/ImasmPanel';
import { BelnapPanel } from './components/BelnapPanel';
import { OrganismPanel } from './components/OrganismPanel';
import { CorpusPanel } from './components/CorpusPanel';
import { ImscribingPanel } from './components/ImscribingPanel';

type TabId = 'imscribing' | 'sixteen3' | 'imasm' | 'belnap' | 'organism' | 'corpus';

const TABS: { id: TabId; label: React.ReactNode; icon: React.ComponentType<{ className?: string }> }[] = [
  { id: 'imscribing', label: 'Imscribing', icon: Layers },
  { id: 'sixteen3', label: <>SIXTEEN<sub>3</sub></>, icon: Grid3X3 },
  { id: 'imasm', label: 'IMASM', icon: Terminal },
  { id: 'belnap', label: 'Belnap FOUR', icon: Scale },
  { id: 'organism', label: 'Organism', icon: Orbit },
  { id: 'corpus', label: 'Corpus', icon: BookOpen },
];

export function App() {
  const [activeTab, setActiveTab] = useState<TabId>('imscribing');

  return (
    <div className="min-h-screen bg-[#07090e] text-slate-100 flex flex-col">
      <header className="sticky top-0 z-30 border-b border-slate-800/80 bg-[#0b0e15]/95 backdrop-blur">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 h-14 flex items-center justify-between gap-4">
          <div className="flex items-center gap-2.5 shrink-0">
            <span className="w-7 h-7 rounded border border-amber-500/40 bg-amber-500/10 flex items-center justify-center font-mono text-amber-300 font-bold text-sm">
              ⊙
            </span>
            <span className="text-sm font-semibold tracking-tight text-slate-100 whitespace-nowrap">
              p4rakernel
            </span>
          </div>

          <nav className="flex items-center gap-1 overflow-x-auto" aria-label="Primary workbench views">
            {TABS.map((tab) => {
              const Icon = tab.icon;
              const active = activeTab === tab.id;
              return (
                <button
                  key={tab.id}
                  type="button"
                  onClick={() => setActiveTab(tab.id)}
                  className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded text-xs font-medium whitespace-nowrap shrink-0 transition-colors cursor-pointer ${
                    active
                      ? 'bg-amber-500/15 text-amber-200 border border-amber-500/40'
                      : 'text-slate-400 hover:text-slate-100 border border-transparent hover:bg-slate-800/50'
                  }`}
                >
                  <Icon className="w-3.5 h-3.5 shrink-0" />
                  <span>{tab.label}</span>
                </button>
              );
            })}
          </nav>

          <div className="hidden sm:flex items-center gap-2 shrink-0">
            <button
              type="button"
              onClick={() => setActiveTab('corpus')}
              className="inline-flex items-center gap-1.5 px-3 py-1.5 rounded border border-cyan-500/40 bg-cyan-500/10 text-cyan-200 hover:bg-cyan-500/20 text-xs font-mono whitespace-nowrap cursor-pointer tabular-nums"
            >
              <span>564 Lean Modules</span>
            </button>
            <a
              href="https://github.com/umpolungfish/p4rakernel"
              target="_blank"
              rel="noreferrer"
              aria-label="umpolungfish/p4rakernel on GitHub"
              className="inline-flex items-center gap-1 px-2.5 py-1.5 rounded border border-slate-700/80 bg-[#07090e] text-slate-300 hover:text-amber-200 hover:border-amber-500/40 text-xs font-mono whitespace-nowrap transition-colors"
            >
              <span>GitHub</span>
              <ExternalLink className="w-3 h-3" />
            </a>
          </div>
        </div>
      </header>

      <main className="flex-1 max-w-7xl w-full mx-auto px-4 sm:px-6 py-5">
        {activeTab === 'imscribing' && <ImscribingPanel />}
        {activeTab === 'sixteen3' && <Sixteen3Panel />}
        {activeTab === 'imasm' && <ImasmPanel />}
        {activeTab === 'belnap' && <BelnapPanel />}
        {activeTab === 'organism' && <OrganismPanel />}
        {activeTab === 'corpus' && <CorpusPanel />}
      </main>
    </div>
  );
}

export default App;
