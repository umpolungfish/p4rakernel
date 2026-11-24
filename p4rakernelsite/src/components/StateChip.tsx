import React from 'react';

const LABELS = ['N', 'T', 'F', 'B'] as const;

export function formatMaskLabel(mask: number): string {
  const m = mask & 15;
  if (m === 0) return '∅';
  const parts: string[] = [];
  if (m & 1) parts.push('N');
  if (m & 2) parts.push('T');
  if (m & 4) parts.push('F');
  if (m & 8) parts.push('B');
  return `{${parts.join(',')}}`;
}

export const StateChip: React.FC<{
  mask: number;
  size?: 'sm' | 'md';
  highlight?: boolean;
}> = ({ mask, size = 'sm', highlight = false }) => {
  const m = mask & 15;
  const hasB = (m & 8) !== 0;
  const hasT = (m & 2) !== 0;
  const hasF = (m & 4) !== 0;

  let border = 'border-slate-700/80 bg-slate-900/90 text-slate-200';
  if (highlight) {
    border = 'border-amber-400/70 bg-amber-500/15 text-amber-200';
  } else if (m === 8) {
    border = 'border-amber-500/50 bg-amber-500/10 text-amber-300';
  } else if (m === 2) {
    border = 'border-emerald-500/50 bg-emerald-500/10 text-emerald-300';
  } else if (m === 4) {
    border = 'border-rose-500/50 bg-rose-500/10 text-rose-300';
  } else if (hasB && hasT && hasF) {
    border = 'border-violet-500/50 bg-violet-500/10 text-violet-200';
  }

  return (
    <span
      className={`inline-flex items-center gap-1.5 rounded border font-mono ${border} ${
        size === 'sm' ? 'px-2 py-0.5 text-xs' : 'px-2.5 py-1 text-sm'
      }`}
    >
      <span className="font-semibold">{m}</span>
      <span className="text-slate-400">{formatMaskLabel(m)}</span>
      <span className="inline-flex gap-0.5 ml-0.5">
        {LABELS.map((lbl, idx) => {
          const active = (m & (1 << idx)) !== 0;
          const dotColor = !active
            ? 'bg-slate-800'
            : lbl === 'N'
            ? 'bg-slate-400'
            : lbl === 'T'
            ? 'bg-emerald-400'
            : lbl === 'F'
            ? 'bg-rose-400'
            : 'bg-amber-400';
          return <span key={lbl} className={`w-1.5 h-1.5 rounded-full ${dotColor}`} title={lbl} />;
        })}
      </span>
    </span>
  );
};
