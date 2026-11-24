import React from 'react';
import type { BankedStep, OrbitResult } from '../types';

const MASK_MEMBERS = (m: number): string => {
  if (m === 0) return '∅';
  const p: string[] = [];
  if (m & 1) p.push('N');
  if (m & 2) p.push('T');
  if (m & 4) p.push('F');
  if (m & 8) p.push('B');
  return p.join('');
};

// 1. SIXTEEN_3 4D Hypercube / Hasse Lattice SVG
const HASSE_RANKS: number[][] = [
  [0],
  [1, 2, 4, 8],
  [3, 5, 9, 6, 10, 12],
  [7, 11, 13, 14],
  [15],
];

function getHassePos(mask: number): { x: number; y: number } {
  for (let r = 0; r < HASSE_RANKS.length; r++) {
    const row = HASSE_RANKS[r];
    const idx = row.indexOf(mask);
    if (idx !== -1) {
      const y = 305 - r * 66;
      const span = 390;
      const x = row.length === 1 ? 240 : 45 + (idx / (row.length - 1)) * span;
      return { x, y };
    }
  }
  return { x: 240, y: 180 };
}

export const Sixteen3HasseSvg: React.FC<{
  a: number;
  b: number;
  joinI: number;
  meetI: number;
  clickTarget: 'A' | 'B';
  onSelectState: (mask: number) => void;
}> = ({ a, b, joinI, meetI, clickTarget, onSelectState }) => {
  const edges: [number, number][] = [];
  for (let x = 0; x < 16; x++) {
    for (let bit = 0; bit < 4; bit++) {
      const y = x | (1 << bit);
      if (y !== x) edges.push([x, y]);
    }
  }

  return (
    <svg viewBox="0 0 480 340" className="w-full h-auto select-none" role="img" aria-label="SIXTEEN₃ 4D Hypercube Hasse Diagram">
      {/* Rank guide lines */}
      {HASSE_RANKS.map((_, r) => {
        const y = 305 - r * 66;
        return (
          <g key={r}>
            <line x1={28} y1={y} x2={458} y2={y} stroke="#1e293b" strokeWidth={1} strokeDasharray="2 4" />
            <text x={10} y={y + 3} fill="#64748b" fontSize={9} fontFamily="JetBrains Mono, monospace">
              |{r}|
            </text>
          </g>
        );
      })}

      {/* Hypercube covering edges */}
      {edges.map(([u, v]) => {
        const pu = getHassePos(u);
        const pv = getHassePos(v);
        const isPathToJoin =
          ((u === a || u === b) && v === joinI) ||
          ((u & a) === a && (v & joinI) === v && (a & joinI) === a);
        const isActive = (u === a && v === joinI) || (u === b && v === joinI) || (u === meetI && (v === a || v === b));
        return (
          <line
            key={`${u}-${v}`}
            x1={pu.x}
            y1={pu.y}
            x2={pv.x}
            y2={pv.y}
            stroke={isActive ? '#f59e0b' : isPathToJoin ? '#334155' : '#172030'}
            strokeWidth={isActive ? 2 : 1}
            opacity={isActive ? 0.95 : 0.85}
          />
        );
      })}

      {/* Direct join_i / meet_i relation arcs */}
      {a !== joinI && (
        <line
          x1={getHassePos(a).x}
          y1={getHassePos(a).y}
          x2={getHassePos(joinI).x}
          y2={getHassePos(joinI).y}
          stroke="#10b981"
          strokeWidth={1.75}
          strokeDasharray="4 3"
        />
      )}
      {b !== joinI && (
        <line
          x1={getHassePos(b).x}
          y1={getHassePos(b).y}
          x2={getHassePos(joinI).x}
          y2={getHassePos(joinI).y}
          stroke="#06b6d4"
          strokeWidth={1.75}
          strokeDasharray="4 3"
        />
      )}

      {/* 16 State Nodes */}
      {Array.from({ length: 16 }, (_, m) => {
        const { x, y } = getHassePos(m);
        const isA = m === a;
        const isB = m === b;
        const isJoin = m === joinI;
        const isMeet = m === meetI;

        let fill = '#0f141d';
        let stroke = '#334155';
        let textFill = '#cbd5e1';
        if (isA && isB) {
          fill = '#451a03';
          stroke = '#f59e0b';
          textFill = '#fde68a';
        } else if (isA) {
          fill = '#064e3b';
          stroke = '#10b981';
          textFill = '#a7f3d0';
        } else if (isB) {
          fill = '#083344';
          stroke = '#06b6d4';
          textFill = '#a5f3fc';
        } else if (isJoin) {
          fill = '#451a03';
          stroke = '#f59e0b';
          textFill = '#fcd34d';
        } else if (isMeet) {
          fill = '#2e1065';
          stroke = '#a78bfa';
          textFill = '#ddd6fe';
        }

        return (
          <g
            key={m}
            onClick={() => onSelectState(m)}
            className="cursor-pointer"
            role="button"
            aria-label={`Set ${clickTarget} to mask ${m} ${MASK_MEMBERS(m)}`}
          >
            <circle cx={x} cy={y} r={17} fill={fill} stroke={stroke} strokeWidth={isA || isB || isJoin || isMeet ? 2 : 1.2} />
            <text
              x={x}
              y={y - 1}
              textAnchor="middle"
              fill={textFill}
              fontSize={10}
              fontWeight={700}
              fontFamily="JetBrains Mono, monospace"
            >
              {m}
            </text>
            <text
              x={x}
              y={y + 9}
              textAnchor="middle"
              fill="#94a3b8"
              fontSize={8}
              fontFamily="JetBrains Mono, monospace"
            >
              {MASK_MEMBERS(m)}
            </text>
          </g>
        );
      })}

      {/* Legend */}
      <g transform="translate(30, 12)" fontSize={10} fontFamily="JetBrains Mono, monospace">
        <circle cx={0} cy={0} r={4} fill="#10b981" />
        <text x={8} y={3} fill="#94a3b8">A ({a})</text>
        <circle cx={68} cy={0} r={4} fill="#06b6d4" />
        <text x={76} y={3} fill="#94a3b8">B ({b})</text>
        <circle cx={136} cy={0} r={4} fill="#f59e0b" />
        <text x={144} y={3} fill="#94a3b8">
          A∨<tspan dy="2.5" fontSize={7.5}>i</tspan><tspan dy="-2.5">B ({joinI})</tspan>
        </text>
        <circle cx={232} cy={0} r={4} fill="#a78bfa" />
        <text x={240} y={3} fill="#94a3b8">
          A∧<tspan dy="2.5" fontSize={7.5}>i</tspan><tspan dy="-2.5">B ({meetI})</tspan>
        </text>
      </g>
    </svg>
  );
};

// 2. Orbit Phase Ring SVG
export const OrbitPhaseRingSvg: React.FC<{
  orbit: OrbitResult;
  fixedPoints: number[];
}> = ({ orbit, fixedPoints }) => {
  const cx = 175;
  const cy = 148;
  const r = 108;

  const pos = (m: number) => {
    const angle = (m / 16) * Math.PI * 2 - Math.PI / 2;
    return { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
  };

  const traj = orbit.trajectory;
  const cycleSet = new Set(orbit.cycle);

  return (
    <svg viewBox="0 0 350 296" className="w-full h-auto select-none" role="img" aria-label="Finite Clock Orbit Phase Ring">
      <defs>
        <marker id="arrow-amber" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#f59e0b" />
        </marker>
        <marker id="arrow-cyan" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#06b6d4" />
        </marker>
      </defs>

      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#1e293b" strokeWidth={1} strokeDasharray="3 3" />

      {/* Center Readout */}
      <text x={cx} y={cy - 12} textAnchor="middle" fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
        PERIOD {orbit.period} · TRANS {orbit.transient}
      </text>
      <text x={cx} y={cy + 8} textAnchor="middle" fill="#f59e0b" fontSize={18} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        {orbit.value} ({MASK_MEMBERS(orbit.value)})
      </text>
      <text x={cx} y={cy + 24} textAnchor="middle" fill="#64748b" fontSize={9} fontFamily="JetBrains Mono, monospace">
        @ tick {orbit.tick.length > 10 ? `${orbit.tick.slice(0, 7)}…` : orbit.tick}
      </text>

      {/* Transition edges along trajectory + closing cycle edge */}
      {traj.map((from, i) => {
        const to = i + 1 < traj.length ? traj[i + 1] : orbit.cycle[0];
        if (to === undefined) return null;
        const p1 = pos(from);
        const p2 = pos(to);
        const isCycleEdge = i >= orbit.transient;
        if (from === to) {
          return (
            <circle
              key={`self-${from}`}
              cx={p1.x}
              cy={p1.y}
              r={18}
              fill="none"
              stroke="#f59e0b"
              strokeWidth={1.8}
              strokeDasharray="3 2"
            />
          );
        }
        return (
          <line
            key={`${i}-${from}-${to}`}
            x1={p1.x}
            y1={p1.y}
            x2={p2.x}
            y2={p2.y}
            stroke={isCycleEdge ? '#f59e0b' : '#06b6d4'}
            strokeWidth={isCycleEdge ? 2.2 : 1.6}
            strokeDasharray={isCycleEdge ? undefined : '4 3'}
            markerEnd={isCycleEdge ? 'url(#arrow-amber)' : 'url(#arrow-cyan)'}
          />
        );
      })}

      {/* 16 Clock Nodes */}
      {Array.from({ length: 16 }, (_, m) => {
        const { x, y } = pos(m);
        const isLanding = m === orbit.value;
        const isStart = m === orbit.start;
        const inCycle = cycleSet.has(m);
        const isFixed = fixedPoints.includes(m);

        return (
          <g key={m}>
            {isLanding && <circle cx={x} cy={y} r={17} fill="none" stroke="#f59e0b" strokeWidth={1.5} opacity={0.7} />}
            <circle
              cx={x}
              cy={y}
              r={12}
              fill={isLanding ? '#451a03' : isStart ? '#083344' : inCycle ? '#1e1b4b' : '#0f141d'}
              stroke={isLanding ? '#f59e0b' : isStart ? '#06b6d4' : isFixed ? '#10b981' : '#334155'}
              strokeWidth={isLanding || isStart || isFixed ? 1.8 : 1}
            />
            <text
              x={x}
              y={y + 3.5}
              textAnchor="middle"
              fill={isLanding ? '#fde68a' : '#cbd5e1'}
              fontSize={9.5}
              fontWeight={600}
              fontFamily="JetBrains Mono, monospace"
            >
              {m}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

// 3. IMASM Fork-Frame Stack & Register Timeline SVG
export const ImasmStackTimelineSvg: React.FC<{ steps: BankedStep[] }> = ({ steps }) => {
  if (steps.length === 0) return null;
  const colW = Math.max(36, Math.min(62, 680 / steps.length));
  const width = Math.max(700, steps.length * colW + 40);
  const height = 220;

  return (
    <svg viewBox={`0 0 ${width} ${height}`} className="w-full h-auto" role="img" aria-label="IMASM Register and Fork-Frame Stack Timeline">
      <line x1={20} y1={140} x2={width - 20} y2={140} stroke="#334155" strokeWidth={1} />
      <text x={20} y={18} fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
        OPEN FORK FRAMES (stacked ↑) · REGISTER WEIGHT BAR (below ↓)
      </text>

      {steps.map((st, idx) => {
        const cx = 28 + idx * colW + colW / 2;
        const regTotal = Object.values(st.register).reduce((s, v) => s + v, 0);
        const topTotal = st.topFrame ? Object.values(st.topFrame).reduce((s, v) => s + v, 0) : 0;
        const barH = Math.min(48, regTotal * 12);

        const actionColor =
          st.bankAction === 'split'
            ? '#06b6d4'
            : st.bankAction === 'fuse'
            ? '#10b981'
            : st.bankAction === 'clear'
            ? '#f43f5e'
            : '#f59e0b';

        return (
          <g key={st.step}>
            {/* Frame depth boxes above baseline */}
            {Array.from({ length: Math.min(4, st.frameDepth) }, (_, fIdx) => {
              const boxY = 112 - fIdx * 20;
              return (
                <rect
                  key={fIdx}
                  x={cx - 12}
                  y={boxY}
                  width={24}
                  height={16}
                  rx={3}
                  fill="#083344"
                  stroke="#06b6d4"
                  strokeWidth={1.2}
                />
              );
            })}
            {st.frameDepth > 0 && (
              <text
                x={cx}
                y={123 - Math.min(3, st.frameDepth - 1) * 20}
                textAnchor="middle"
                fill="#a5f3fc"
                fontSize={9}
                fontFamily="JetBrains Mono, monospace"
              >
                {topTotal}
              </text>
            )}

            {/* Glyph node on axis */}
            <circle cx={cx} cy={140} r={11} fill="#0f141d" stroke={actionColor} strokeWidth={1.6} />
            <text x={cx} y={144} textAnchor="middle" fill="#fde68a" fontSize={11} fontFamily="JetBrains Mono, monospace">
              {st.glyph}
            </text>

            {/* Open Register weight bar below axis */}
            <rect
              x={cx - 8}
              y={156}
              width={16}
              height={Math.max(4, barH)}
              rx={2}
              fill={st.bankAction === 'clear' ? '#f43f5e' : regTotal > 0 ? '#10b981' : '#1e293b'}
              opacity={0.85}
            />
            <text
              x={cx}
              y={166 + Math.max(4, barH)}
              textAnchor="middle"
              fill="#cbd5e1"
              fontSize={9}
              fontFamily="JetBrains Mono, monospace"
            >
              {regTotal}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

// 4. 12-Axis Imscription Radar Chart SVG
export const ImscribingRadarSvg: React.FC<{
  axes: { key: string; symbol: string; name: string; values: string[] }[];
  a: Record<string, string>;
  b: Record<string, string>;
  tensor: Record<string, string>;
}> = ({ axes, a, b, tensor }) => {
  if (axes.length === 0) return null;
  const cx = 210;
  const cy = 185;
  const maxR = 128;

  const norm = (ax: { key: string; values: string[] }, val: string) => {
    const idx = ax.values.indexOf(val);
    if (ax.values.length <= 1) return 1;
    return 0.2 + 0.8 * (Math.max(0, idx) / (ax.values.length - 1));
  };

  const pt = (i: number, frac: number) => {
    const ang = (i / axes.length) * Math.PI * 2 - Math.PI / 2;
    return { x: cx + maxR * frac * Math.cos(ang), y: cy + maxR * frac * Math.sin(ang) };
  };

  const poly = (tuple: Record<string, string>) =>
    axes
      .map((ax, i) => {
        const p = pt(i, norm(ax, tuple[ax.key]));
        return `${p.x.toFixed(1)},${p.y.toFixed(1)}`;
      })
      .join(' ');

  return (
    <svg viewBox="0 0 420 375" className="w-full h-auto select-none" role="img" aria-label="12-Primitive Imscription Radar Chart">
      {/* Concentric rings */}
      {[0.25, 0.5, 0.75, 1].map((ring) => (
        <polygon
          key={ring}
          points={axes
            .map((_, i) => {
              const p = pt(i, ring);
              return `${p.x.toFixed(1)},${p.y.toFixed(1)}`;
            })
            .join(' ')}
          fill="none"
          stroke="#1e293b"
          strokeWidth={1}
        />
      ))}

      {/* Axes & Labels */}
      {axes.map((ax, i) => {
        const outer = pt(i, 1);
        const lbl = pt(i, 1.18);
        return (
          <g key={ax.key}>
            <line x1={cx} y1={cy} x2={outer.x} y2={outer.y} stroke="#1e293b" strokeWidth={1} />
            <text
              x={lbl.x}
              y={lbl.y + 3}
              textAnchor="middle"
              fill="#cbd5e1"
              fontSize={10}
              fontWeight={600}
              fontFamily="JetBrains Mono, monospace"
            >
              {ax.symbol}·{ax.name.slice(0, 4)}
            </text>
          </g>
        );
      })}

      {/* Polygons */}
      <polygon points={poly(a)} fill="#06b6d4" fillOpacity={0.18} stroke="#06b6d4" strokeWidth={2} />
      <polygon points={poly(b)} fill="#f59e0b" fillOpacity={0.16} stroke="#f59e0b" strokeWidth={2} />
      <polygon points={poly(tensor)} fill="none" stroke="#10b981" strokeWidth={2} strokeDasharray="5 3" />

      {/* Legend */}
      <g transform="translate(24, 16)" fontSize={10} fontFamily="JetBrains Mono, monospace">
        <line x1={0} y1={0} x2={14} y2={0} stroke="#06b6d4" strokeWidth={2.5} />
        <text x={18} y={3} fill="#a5f3fc">Tuple A</text>
        <line x1={84} y1={0} x2={98} y2={0} stroke="#f59e0b" strokeWidth={2.5} />
        <text x={102} y={3} fill="#fde68a">Tuple B</text>
        <line x1={170} y1={0} x2={184} y2={0} stroke="#10b981" strokeWidth={2.5} strokeDasharray="4 2" />
        <text x={188} y={3} fill="#a7f3d0">Tensor A⊗B</text>
      </g>
    </svg>
  );
};

// 5. IUTT 4-Lane Schematic + Filtration Bar Chart SVGs
export const IuttFlowSvg: React.FC<{
  input: { bigT: boolean; bigF: boolean; smallT: boolean; smallF: boolean };
  toFourLabel: string;
  booleanShadow: 'T' | 'F';
}> = ({ input, toFourLabel, booleanShadow }) => {
  const lanes = [
    { label: 'T', active: input.bigT, y: 30, kept: true, color: '#10b981' },
    { label: 'F', active: input.bigF, y: 68, kept: true, color: '#f43f5e' },
    { label: 't', active: input.smallT, y: 106, kept: false, color: '#06b6d4' },
    { label: 'f', active: input.smallF, y: 144, kept: false, color: '#a78bfa' },
  ];

  return (
    <svg viewBox="0 0 520 245" className="w-full h-auto select-none" role="img" aria-label="IUTT 4-Lane Erasure Schematic">
      {/* Input Lanes */}
      {lanes.map((ln) => (
        <g key={ln.label}>
          <rect
            x={16}
            y={ln.y - 13}
            width={44}
            height={26}
            rx={4}
            fill={ln.active ? '#111827' : '#0a0d12'}
            stroke={ln.active ? ln.color : '#1e293b'}
            strokeWidth={1.5}
          />
          <text
            x={38}
            y={ln.y + 4}
            textAnchor="middle"
            fill={ln.active ? ln.color : '#475569'}
            fontSize={12}
            fontWeight={700}
            fontFamily="JetBrains Mono, monospace"
          >
            {ln.label}
          </text>
          <line
            x1={60}
            y1={ln.y}
            x2={ln.kept ? 175 : 155}
            y2={ln.y}
            stroke={ln.active ? ln.color : '#1e293b'}
            strokeWidth={ln.active ? 2 : 1}
            strokeDasharray={ln.kept ? undefined : '4 3'}
          />
          {!ln.kept && (
            <text x={108} y={ln.y - 6} textAnchor="middle" fill="#64748b" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
              erased
            </text>
          )}
        </g>
      ))}

      {/* eraseInformation block */}
      <rect x={175} y={16} width={132} height={70} rx={6} fill="#0f141d" stroke="#f59e0b" strokeWidth={1.5} />
      <text x={241} y={38} textAnchor="middle" fill="#fde68a" fontSize={10.5} fontWeight={600} fontFamily="JetBrains Mono, monospace">
        eraseInformation
      </text>
      <text x={241} y={58} textAnchor="middle" fill="#f59e0b" fontSize={16} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        → {toFourLabel}
      </text>
      <text x={241} y={76} textAnchor="middle" fill="#94a3b8" fontSize={9} fontFamily="JetBrains Mono, monospace">
        FOUR = {'{N,T,F,B}'}
      </text>

      {/* Connector to booleanShadow */}
      <line x1={307} y1={51} x2={364} y2={51} stroke="#f59e0b" strokeWidth={2} />

      {/* booleanShadow block */}
      <rect x={364} y={16} width={138} height={70} rx={6} fill="#0f141d" stroke="#10b981" strokeWidth={1.5} />
      <text x={433} y={38} textAnchor="middle" fill="#a7f3d0" fontSize={10.5} fontWeight={600} fontFamily="JetBrains Mono, monospace">
        booleanShadow
      </text>
      <text x={433} y={58} textAnchor="middle" fill={booleanShadow === 'T' ? '#10b981' : '#f43f5e'} fontSize={16} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        → {booleanShadow}
      </text>
      <text x={433} y={76} textAnchor="middle" fill="#94a3b8" fontSize={9} fontFamily="JetBrains Mono, monospace">
        BoolCentre {'{T,F}'}
      </text>

      {/* Filtration Bar Chart in clean lower zone */}
      <line x1={16} y1={170} x2={504} y2={170} stroke="#1e293b" strokeWidth={1} />
      <g transform="translate(16, 184)">
        <text x={0} y={10} fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
          Prop 18.1 Filtration: Blind Scalar Sum vs j<tspan dy="-3.5" fontSize={7.5}>2</tspan><tspan dy="3.5">-Weight</tspan>
        </text>
        <rect x={0} y={20} width={72} height={16} rx={2} fill="#334155" />
        <text x={82} y={32} fill="#cbd5e1" fontSize={10} fontFamily="JetBrains Mono, monospace">
          atOne (0,1,0): blind=1 · j<tspan dy="-3.5" fontSize={7.5}>2</tspan><tspan dy="3.5">=1</tspan>
        </text>
        <rect x={0} y={42} width={72} height={16} rx={2} fill="#334155" />
        <rect x={0} y={42} width={270} height={16} rx={2} fill="#f59e0b" fillOpacity={0.28} stroke="#f59e0b" strokeWidth={1} />
        <text x={280} y={54} fill="#fde68a" fontSize={10} fontFamily="JetBrains Mono, monospace">
          atTwo (0,0,1): blind=1 · j<tspan dy="-3.5" fontSize={7.5}>2</tspan><tspan dy="3.5">=4</tspan>
        </text>
      </g>
    </svg>
  );
};

// 6. Fine-Structure Constant Gauge & Ouroboric Key-Exchange Diagrams
export const FineStructureGaugeSvg: React.FC<{
  integerCore: number;
  tiltCorrection: number;
  broadcastTerm: number;
  computedAlphaInv: number;
  codata2022: number;
  ppm: number;
}> = ({ integerCore, tiltCorrection, broadcastTerm, computedAlphaInv, codata2022, ppm }) => (
  <svg viewBox="0 0 480 120" className="w-full h-auto select-none" role="img" aria-label="Fine Structure Constant Decomposition">
    <text x={8} y={18} fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
      α<tspan dy="-3.5" fontSize={7.5}>−1</tspan><tspan dy="3.5"> DECOMPOSITION (d=12 SIC-POVM)</tspan>
    </text>
    <text x={472} y={18} textAnchor="end" fill="#10b981" fontSize={10.5} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      Δ = {ppm} ppm vs CODATA
    </text>

    {/* Segmented bar (not proportional to 137 vs 0.035; log-like schematic widths with exact labels) */}
    <rect x={8} y={32} width={250} height={32} rx={4} fill="#1e293b" stroke="#334155" />
    <text x={133} y={52} textAnchor="middle" fill="#e2e8f0" fontSize={12} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      d<tspan dy="-3.5" fontSize={8.5}>2</tspan><tspan dy="3.5">−7 = {integerCore}</tspan>
    </text>

    <rect x={262} y={32} width={118} height={32} rx={4} fill="#083344" stroke="#06b6d4" />
    <text x={321} y={52} textAnchor="middle" fill="#a5f3fc" fontSize={10.5} fontWeight={600} fontFamily="JetBrains Mono, monospace">
      +{tiltCorrection.toFixed(6)}
    </text>

    <rect x={384} y={32} width={88} height={32} rx={4} fill="#451a03" stroke="#f59e0b" />
    <text x={428} y={52} textAnchor="middle" fill="#fde68a" fontSize={10.5} fontWeight={600} fontFamily="JetBrains Mono, monospace">
      +{broadcastTerm.toFixed(6)}
    </text>

    <text x={8} y={88} fill="#cbd5e1" fontSize={11} fontFamily="JetBrains Mono, monospace">
      Derived: <tspan fill="#f59e0b" fontWeight={700}>{computedAlphaInv}</tspan>
    </text>
    <text x={472} y={88} textAnchor="end" fill="#94a3b8" fontSize={11} fontFamily="JetBrains Mono, monospace">
      CODATA 2022: <tspan fill="#10b981" fontWeight={700}>{codata2022}</tspan>
    </text>
    <text x={8} y={108} fill="#64748b" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
      7 Cartan E<tspan dy="2.5" fontSize={7}>7</tspan><tspan dy="-2.5"> commuting axes · Horn torus tilt arctan(1/4)/(4√3) · CLINK L8 α</tspan><tspan dy="-3" fontSize={7}>2</tspan><tspan dy="3">·12</tspan>
    </text>
  </svg>
);

export const OuroboricChannelSvg: React.FC<{
  transmitted: 'N' | 'T' | 'F' | 'B';
  eveCoreflected: 'T' | 'F';
  aliceMass: number;
  eveMass: number;
  tamperDetected: boolean;
}> = ({ transmitted, eveCoreflected, aliceMass, eveMass, tamperDetected }) => (
  <svg viewBox="0 0 480 175" className="w-full h-auto select-none" role="img" aria-label="Ouroboric Key Exchange Channel Diagram">
    <defs>
      <marker id="arr-e" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="6" markerHeight="6" orient="auto">
        <path d="M 0 1 L 10 5 L 0 9 z" fill="#10b981" />
      </marker>
      <marker id="arr-r" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="6" markerHeight="6" orient="auto">
        <path d="M 0 1 L 10 5 L 0 9 z" fill="#f43f5e" />
      </marker>
    </defs>

    {/* Alice */}
    <rect x={14} y={56} width={96} height={60} rx={6} fill="#0f141d" stroke="#f59e0b" strokeWidth={1.6} />
    <text x={62} y={78} textAnchor="middle" fill="#fde68a" fontSize={11} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      ALICE
    </text>
    <text x={62} y={96} textAnchor="middle" fill="#f59e0b" fontSize={12} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      {transmitted} · m={aliceMass}
    </text>

    {/* Upper wire to Eve */}
    <path d="M 110 74 C 170 38, 220 38, 275 40" fill="none" stroke={tamperDetected ? '#f43f5e' : '#64748b'} strokeWidth={2} markerEnd="url(#arr-r)" />
    <rect x={282} y={14} width={184} height={54} rx={6} fill="#0f141d" stroke={tamperDetected ? '#f43f5e' : '#334155'} strokeWidth={1.6} />
    <text x={374} y={34} textAnchor="middle" fill={tamperDetected ? '#fda4af' : '#cbd5e1'} fontSize={10.5} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      EVE (β-shear coreflect)
    </text>
    <text x={374} y={52} textAnchor="middle" fill={tamperDetected ? '#f43f5e' : '#94a3b8'} fontSize={11} fontFamily="JetBrains Mono, monospace">
      {eveCoreflected} · mass {aliceMass}→{eveMass} {tamperDetected ? '(LEAK)' : ''}
    </text>

    {/* Lower wire to Bob */}
    <path d="M 110 98 C 170 134, 220 134, 275 132" fill="none" stroke="#10b981" strokeWidth={2} markerEnd="url(#arr-e)" />
    <rect x={282} y={104} width={184} height={54} rx={6} fill="#0f141d" stroke="#10b981" strokeWidth={1.6} />
    <text x={374} y={124} textAnchor="middle" fill="#a7f3d0" fontSize={10.5} fontWeight={700} fontFamily="JetBrains Mono, monospace">
      BOB (ambient read)
    </text>
    <text x={374} y={142} textAnchor="middle" fill="#10b981" fontSize={11} fontFamily="JetBrains Mono, monospace">
      {transmitted} · mass {aliceMass} (lossless)
    </text>
  </svg>
);

// 7. Belnap Bilattice Diamond & Cuts Venn Diagrams
export const BelnapDiamondSvg: React.FC<{
  mode: 'frobenius' | 'classical' | 'centre';
}> = ({ mode }) => {
  const pts = {
    T: { x: 200, y: 42 },
    N: { x: 88, y: 155 },
    B: { x: 312, y: 155 },
    F: { x: 200, y: 268 },
  };

  return (
    <svg viewBox="0 0 400 310" className="w-full h-auto select-none" role="img" aria-label="Belnap FOUR Bilattice Diamond">
      <defs>
        <marker id="arr-b" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#f59e0b" />
        </marker>
      </defs>

      {/* Axis Labels */}
      <text x={200} y={16} textAnchor="middle" fill="#64748b" fontSize={10} fontFamily="JetBrains Mono, monospace">
        ↑ TRUTH ORDER (≤<tspan dy="2.5" fontSize={7.5}>t</tspan><tspan dy="-2.5">)</tspan>
      </text>
      <text x={392} y={159} textAnchor="end" fill="#64748b" fontSize={9.5} fontFamily="JetBrains Mono, monospace">
        INFO →
      </text>

      {/* Diamond edges */}
      <line x1={pts.T.x} y1={pts.T.y} x2={pts.N.x} y2={pts.N.y} stroke="#334155" strokeWidth={1.6} />
      <line x1={pts.T.x} y1={pts.T.y} x2={pts.B.x} y2={pts.B.y} stroke="#334155" strokeWidth={1.6} />
      <line x1={pts.F.x} y1={pts.F.y} x2={pts.N.x} y2={pts.N.y} stroke="#334155" strokeWidth={1.6} />
      <line x1={pts.F.x} y1={pts.F.y} x2={pts.B.x} y2={pts.B.y} stroke="#334155" strokeWidth={1.6} />

      {/* Mode overlays */}
      {mode === 'frobenius' && (
        <g>
          <path d="M 200 62 Q 268 85 300 138" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <path d="M 110 155 Q 200 120 289 155" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <path d="M 200 248 Q 268 225 300 172" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <circle cx={pts.B.x} cy={pts.B.y} r={29} fill="none" stroke="#f59e0b" strokeWidth={1.5} strokeDasharray="4 3" />
          <text x={200} y={298} textAnchor="middle" fill="#fde68a" fontSize={10.5} fontFamily="JetBrains Mono, monospace">
            Inc(s) = B · Universal Dialetheic Fixed Point
          </text>
        </g>
      )}

      {mode === 'classical' && (
        <g>
          <ellipse cx={155} cy={155} rx={108} ry={130} fill="#10b981" fillOpacity={0.07} stroke="#10b981" strokeWidth={1.5} strokeDasharray="5 3" />
          <path d="M 298 172 Q 268 225 222 258" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <text x={200} y={298} textAnchor="middle" fill="#a7f3d0" fontSize={10.5} fontFamily="JetBrains Mono, monospace">
            ClassicalRestriction: {'{N, T, F}'} · classicalSwitch(B) = F
          </text>
        </g>
      )}

      {mode === 'centre' && (
        <g>
          <rect x={166} y={14} width={68} height={276} rx={34} fill="#06b6d4" fillOpacity={0.08} stroke="#06b6d4" strokeWidth={1.5} strokeDasharray="5 3" />
          <path d="M 108 170 Q 138 225 182 258" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <path d="M 296 172 Q 268 225 220 258" fill="none" stroke="#f59e0b" strokeWidth={2} markerEnd="url(#arr-b)" />
          <text x={200} y={298} textAnchor="middle" fill="#a5f3fc" fontSize={10.5} fontFamily="JetBrains Mono, monospace">
            BooleanCentre: {'{T, F}'} · N &amp; B excluded (N ∨ ¬N = N ≠ T)
          </text>
        </g>
      )}

      {/* Nodes */}
      {(
        [
          ['T', pts.T, '#10b981', '#064e3b'],
          ['N', pts.N, '#94a3b8', '#1e293b'],
          ['B', pts.B, '#f59e0b', '#451a03'],
          ['F', pts.F, '#f43f5e', '#4c0519'],
        ] as const
      ).map(([lbl, p, stroke, fill]) => (
        <g key={lbl}>
          <circle cx={p.x} cy={p.y} r={22} fill={fill} stroke={stroke} strokeWidth={2} />
          <text x={p.x} y={p.y + 5} textAnchor="middle" fill="#f8fafc" fontSize={15} fontWeight={700} fontFamily="JetBrains Mono, monospace">
            {lbl}
          </text>
        </g>
      ))}
    </svg>
  );
};

// 8. Organism Constitutive Cycle Ring + Toroidal Coset Wheel SVGs
export const OrganismCycleWheelSvg: React.FC<{
  activeMask?: number;
}> = ({ activeMask }) => {
  const nodes = [
    { mask: 8, label: '⌈B⌋', sub: '[1,1]', color: '#f59e0b' },
    { mask: 0, label: '∅', sub: '[0,0]', color: '#64748b' },
    { mask: 1, label: 'N', sub: '[0,0]', color: '#94a3b8' },
    { mask: 3, label: 'N,T', sub: '[1,0]', color: '#10b981' },
    { mask: 7, label: 'N,T,F', sub: '[1,1]', color: '#06b6d4' },
    { mask: 15, label: 'N,T,F,B', sub: '[1,1]', color: '#a78bfa' },
  ];
  const cx = 190;
  const cy = 152;
  const r = 104;

  const pos = (i: number) => {
    const ang = (i / nodes.length) * Math.PI * 2 - Math.PI / 2;
    return { x: cx + r * Math.cos(ang), y: cy + r * Math.sin(ang) };
  };

  return (
    <svg viewBox="0 0 380 305" className="w-full h-auto select-none" role="img" aria-label="Organism Constitutive Cycle">
      <defs>
        <marker id="arr-cyc" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M 0 1 L 10 5 L 0 9 z" fill="#f59e0b" />
        </marker>
      </defs>

      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#1e293b" strokeWidth={1.5} />
      <text x={cx} y={cy - 6} textAnchor="middle" fill="#cbd5e1" fontSize={11} fontWeight={600} fontFamily="JetBrains Mono, monospace">
        CONSTITUTIVE
      </text>
      <text x={cx} y={cy + 10} textAnchor="middle" fill="#f59e0b" fontSize={11} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        B-TO-B CYCLE
      </text>

      {nodes.map((n, i) => {
        const p1 = pos(i);
        const p2 = pos((i + 1) % nodes.length);
        const mx = (p1.x + p2.x) / 2;
        const my = (p1.y + p2.y) / 2;
        return (
          <line
            key={`edge-${n.mask}`}
            x1={p1.x}
            y1={p1.y}
            x2={mx}
            y2={my}
            stroke="#f59e0b"
            strokeWidth={1.6}
            markerEnd="url(#arr-cyc)"
          />
        );
      })}

      {nodes.map((n, i) => {
        const { x, y } = pos(i);
        const active = activeMask === n.mask;
        return (
          <g key={n.mask}>
            <circle
              cx={x}
              cy={y}
              r={26}
              fill={active ? '#451a03' : '#0f141d'}
              stroke={active ? '#f59e0b' : n.color}
              strokeWidth={active ? 2.5 : 1.5}
            />
            <text x={x} y={y - 2} textAnchor="middle" fill="#f8fafc" fontSize={10.5} fontWeight={700} fontFamily="JetBrains Mono, monospace">
              {n.mask}:{n.label}
            </text>
            <text x={x} y={y + 11} textAnchor="middle" fill="#94a3b8" fontSize={8.5} fontFamily="JetBrains Mono, monospace">
              {n.sub}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export const ToroidalCosetWheelSvg: React.FC<{
  modulus2m: string;
  nMod2m: string;
  cosets: { pResidue: string; qResidue: string; matchesNMod2m: boolean }[];
}> = ({ modulus2m, nMod2m, cosets }) => {
  const cx = 190;
  const cy = 152;
  const r = 104;
  const modNum = Math.max(4, Number(modulus2m) || 16);

  const angleFor = (valStr: string) => {
    const v = Number(BigInt(valStr) % BigInt(modNum));
    return (v / modNum) * Math.PI * 2 - Math.PI / 2;
  };

  return (
    <svg viewBox="0 0 380 305" className="w-full h-auto select-none" role="img" aria-label="Toroidal Odd-Coset Modular Wheel">
      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#1e293b" strokeWidth={2} />
      <circle cx={cx} cy={cy} r={r * 0.54} fill="none" stroke="#1e293b" strokeWidth={1} strokeDasharray="3 3" />

      <text x={cx} y={cy - 8} textAnchor="middle" fill="#94a3b8" fontSize={10} fontFamily="JetBrains Mono, monospace">
        TORUS mod {modulus2m}
      </text>
      <text x={cx} y={cy + 10} textAnchor="middle" fill="#06b6d4" fontSize={13} fontWeight={700} fontFamily="JetBrains Mono, monospace">
        N ≡ {nMod2m}
      </text>

      {cosets.map((c, idx) => {
        const ap = (idx / Math.max(1, cosets.length)) * Math.PI * 2 - Math.PI * 0.75;
        const aq = angleFor(c.qResidue);
        const cosP = Math.cos(ap);
        const sinP = Math.sin(ap);
        const px = cx + r * cosP;
        const py = cy + r * sinP;
        const qx = cx + r * 0.54 * Math.cos(aq);
        const qy = cy + r * 0.54 * Math.sin(aq);
        const colors = ['#10b981', '#06b6d4', '#f59e0b', '#a78bfa'];
        const col = colors[idx % colors.length];
        const anchor = cosP > 0.25 ? 'start' : cosP < -0.25 ? 'end' : 'middle';
        const lx = cx + (r + 14) * cosP;
        const ly = cy + (r + 14) * sinP + (sinP > 0 ? 7 : -1);

        return (
          <g key={c.pResidue}>
            <line x1={px} y1={py} x2={qx} y2={qy} stroke={col} strokeWidth={1.7} opacity={0.85} />
            <circle cx={px} cy={py} r={6} fill={col} />
            <circle cx={qx} cy={qy} r={5} fill="#0f141d" stroke={col} strokeWidth={2} />
            <text
              x={lx}
              y={ly}
              textAnchor={anchor}
              fill={col}
              fontSize={9.5}
              fontWeight={600}
              fontFamily="JetBrains Mono, monospace"
            >
              p≡{c.pResidue} → q={c.qResidue}
            </text>
          </g>
        );
      })}
    </svg>
  );
};
