export interface Sixteen3StateInfo {
  mask: number;
  members: ('N' | 'T' | 'F' | 'B')[];
  label: string;
  hasN: boolean;
  hasT: boolean;
  hasF: boolean;
  hasB: boolean;
}

export interface FixedPointAnalysis {
  table: number[];
  monotoneInfo: boolean;
  monotoneTruth: boolean;
  monotoneFalsity: boolean;
  fixedPoints: number[];
  leastFixedPoint: number | null;
  greatestFixedPoint: number | null;
  certified: boolean;
}

export interface OrbitResult {
  start: number;
  tick: string;
  value: number;
  transient: number;
  period: number;
  trajectory: number[];
  cycle: number[];
  cycleCertified: boolean;
}

export interface ImasmOpcodeSpec {
  glyph: string;
  index: number;
  opcode: string;
  family: '𝓕₃' | '𝓕₄' | '𝓕₅';
  primitive: string;
  role: string;
  bankAction: 'split' | 'fuse' | 'clear' | 'touch';
}

export interface BankedStep {
  step: number;
  glyph: string;
  opcode: string;
  bankAction: string;
  register: Record<string, number>;
  frameDepth: number;
  topFrame: Record<string, number> | null;
  maskState: number;
}

export interface ImasmEvaluationResult {
  valid: boolean;
  error?: string;
  word: string;
  tokens: ImasmOpcodeSpec[];
  bankedSteps: BankedStep[];
  finalRegister: Record<string, number>;
  totalRecoveredWeight: number;
  openFramesRemaining: number;
  base12Scalar: string;
  sixteen3Analysis: FixedPointAnalysis;
  orbit: OrbitResult;
}
