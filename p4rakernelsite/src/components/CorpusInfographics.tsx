import React from 'react';

interface CategoryStat {
  category: string;
  files: number;
  theorems: number;
  sorryFree: number;
}

export const SubsystemBarChartSvg: React.FC<{
  categories: CategoryStat[];
  activeCategory: string;
  onSelectCategory: (cat: string) => void;
}> = ({ categories, activeCategory, onSelectCategory }) => {
  if (categories.length === 0) return null;
  const maxFiles = Math.max(...categories.map((c) => c.files), 1);
  const rowH = 26;
  const height = categories.length * rowH + 34;

  return (
    <svg viewBox={`0 0 560 ${height}`} className="w-full h-auto select-none" role="img" aria-label="p4ramill/Imscribing Subsystem File Distribution">
      <text x={8} y={16} fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
        SUBSYSTEM DISTRIBUTION (click bar) · EMERALD = 0 SORRY · AMBER = THRESHOLD
      </text>
      {categories.map((c, idx) => {
        const y = 28 + idx * rowH;
        const totalW = Math.max(6, (c.files / maxFiles) * 260);
        const cleanW = (c.sorryFree / Math.max(c.files, 1)) * totalW;
        const openW = Math.max(0, totalW - cleanW);
        const active = activeCategory === c.category;

        return (
          <g
            key={c.category}
            onClick={() => onSelectCategory(active ? 'all' : c.category)}
            className="cursor-pointer"
            role="button"
            aria-label={`Filter subsystem ${c.category}`}
          >
            <rect
              x={4}
              y={y - 2}
              width={552}
              height={rowH - 4}
              rx={4}
              fill={active ? '#1e293b' : 'transparent'}
            />
            <text
              x={10}
              y={y + 13}
              fill={active ? '#fde68a' : '#cbd5e1'}
              fontSize={10.5}
              fontWeight={active ? 700 : 500}
              fontFamily="JetBrains Mono, monospace"
            >
              {c.category}
            </text>
            <rect x={115} y={y + 3} width={cleanW} height={14} rx={2} fill="#10b981" opacity={0.85} />
            {openW > 0 && (
              <rect x={115 + cleanW} y={y + 3} width={openW} height={14} rx={2} fill="#f59e0b" opacity={0.9} />
            )}
            <text
              x={124 + totalW}
              y={y + 13.5}
              fill="#94a3b8"
              fontSize={10}
              fontFamily="JetBrains Mono, monospace"
            >
              {c.files} files · {c.theorems} thms
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export const ImportHubRadialSvg: React.FC<{
  hubs: { module: string; count: number }[];
  onSelectHub: (mod: string) => void;
}> = ({ hubs, onSelectHub }) => {
  const top = hubs.slice(0, 8);
  if (top.length === 0) return null;
  const cx = 240;
  const cy = 152;
  const r = 92;
  const maxC = Math.max(...top.map((h) => h.count), 1);

  return (
    <svg viewBox="0 0 480 304" className="w-full h-auto select-none" role="img" aria-label="Top Imscribing Import Hub Graph">
      <circle cx={cx} cy={cy} r={32} fill="#0f141d" stroke="#f59e0b" strokeWidth={2} />
      <text x={cx} y={cy - 2} textAnchor="middle" fill="#fde68a" fontSize={10.5} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        564
      </text>
      <text x={cx} y={cy + 10} textAnchor="middle" fill="#94a3b8" fontSize={8.5} fontFamily="JetBrains Mono, monospace">
        MODULES
      </text>

      {top.map((h, i) => {
        const ang = (i / top.length) * Math.PI * 2 - Math.PI / 2;
        const cosA = Math.cos(ang);
        const sinA = Math.sin(ang);
        const x = cx + r * cosA;
        const y = cy + r * sinA;
        const nodeR = 13 + (h.count / maxC) * 9;
        const short = h.module.replace(/^Imscribing\./, '').replace(/^Primitives\./, '');

        const anchor = cosA > 0.35 ? 'start' : cosA < -0.35 ? 'end' : 'middle';
        const lx = cosA > 0.35 ? x + nodeR + 7 : cosA < -0.35 ? x - nodeR - 7 : x;
        const ly = Math.abs(sinA) > 0.7 ? (sinA < 0 ? y - nodeR - 7 : y + nodeR + 13) : y + 3;

        return (
          <g
            key={h.module}
            onClick={() => onSelectHub(h.module)}
            className="cursor-pointer"
            role="button"
            aria-label={`Open hub module ${h.module}`}
          >
            <line
              x1={cx}
              y1={cy}
              x2={x}
              y2={y}
              stroke="#06b6d4"
              strokeWidth={1 + (h.count / maxC) * 2.5}
              opacity={0.55}
            />
            <circle cx={x} cy={y} r={nodeR} fill="#083344" stroke="#06b6d4" strokeWidth={1.5} />
            <text x={x} y={y + 3.5} textAnchor="middle" fill="#a5f3fc" fontSize={10} fontWeight={700} fontFamily="JetBrains Mono, monospace">
              {h.count}
            </text>
            <text
              x={lx}
              y={ly}
              textAnchor={anchor}
              fill="#cbd5e1"
              fontSize={9.5}
              fontFamily="JetBrains Mono, monospace"
            >
              {short.slice(0, 14)}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export const MsaComparativeChartSvg: React.FC<{
  rows: { label: string; winding: number; contacts: number; activated: number }[];
}> = ({ rows }) => {
  if (rows.length === 0) return null;
  const maxVal = Math.max(...rows.map((r) => Math.max(r.winding, r.contacts)), 1);
  const rowH = 24;
  const height = rows.length * rowH + 38;

  return (
    <svg viewBox={`0 0 480 ${height}`} className="w-full h-auto select-none" role="img" aria-label="Protein MSA Winding and Contacts Chart">
      <g transform="translate(10, 14)" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
        <rect x={0} y={-8} width={10} height={10} rx={2} fill="#06b6d4" />
        <text x={14} y={0} fill="#a5f3fc">Winding</text>
        <rect x={80} y={-8} width={10} height={10} rx={2} fill="#f59e0b" />
        <text x={94} y={0} fill="#fde68a">Contacts</text>
        <rect x={165} y={-8} width={10} height={10} rx={2} fill="#10b981" />
        <text x={179} y={0} fill="#a7f3d0">Primitives (/12)</text>
      </g>

      {rows.map((r, i) => {
        const y = 30 + i * rowH;
        const wW = (r.winding / maxVal) * 230;
        const cW = (r.contacts / maxVal) * 230;
        return (
          <g key={r.label}>
            <text x={10} y={y + 11} fill="#cbd5e1" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
              {r.label}
            </text>
            <rect x={145} y={y + 1} width={wW} height={7} rx={1.5} fill="#06b6d4" />
            <rect x={145} y={y + 10} width={cW} height={7} rx={1.5} fill="#f59e0b" />
            <text x={385} y={y + 11} fill="#94a3b8" fontSize={9} fontFamily="JetBrains Mono, monospace">
              {r.winding}w · {r.contacts}c · {r.activated}/12
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export const AbcEnclosureChartSvg: React.FC<{
  readings: {
    c_max: number;
    epsilon: string;
    lower: string;
    upper: string;
    lower_witness: number[];
  }[];
}> = ({ readings }) => {
  if (readings.length === 0) return null;
  const rowH = 24;
  const height = readings.length * rowH + 34;

  return (
    <svg viewBox={`0 0 480 ${height}`} className="w-full h-auto select-none" role="img" aria-label="ABC Rational Log Enclosure Chart">
      <text x={10} y={16} fill="#94a3b8" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
        ABC RATIONAL LOG ENCLOSURES [0.0 → 1.0]
      </text>
      {readings.map((r, i) => {
        const y = 28 + i * rowH;
        const lo = Math.max(0, Math.min(1, parseFloat(r.lower) || 0));
        const hi = Math.max(lo, Math.min(1, parseFloat(r.upper) || lo));
        const x1 = 120 + lo * 220;
        const x2 = 120 + hi * 220;

        return (
          <g key={i}>
            <text x={10} y={y + 12} fill="#cbd5e1" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
              c≤{r.c_max} ε={r.epsilon}
            </text>
            <line x1={120} y1={y + 9} x2={340} y2={y + 9} stroke="#1e293b" strokeWidth={2} />
            <line x1={120} y1={y + 9} x2={x1} y2={y + 9} stroke="#10b981" strokeWidth={4} />
            <rect x={x1 - 2} y={y + 3} width={Math.max(5, x2 - x1)} height={12} rx={2} fill="#f59e0b" />
            <text x={350} y={y + 12} fill="#94a3b8" fontSize={9} fontFamily="JetBrains Mono, monospace">
              {lo.toFixed(4)} ({r.lower_witness.join(',')})
            </text>
          </g>
        );
      })}
    </svg>
  );
};
