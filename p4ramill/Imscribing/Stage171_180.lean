import Std

namespace Stage171_180

inductive Order6 where
  | T_F_tf
  | T_tf_F
  | F_T_tf
  | F_tf_T
  | tf_T_F
  | tf_F_T
deriving DecidableEq, Repr

inductive Ladder6 where
  | tf_Ftf_A
  | F_Ftf_A
  | tf_Ttf_A
  | T_Ttf_A
  | F_TF_A
  | T_TF_A
deriving DecidableEq, Repr

inductive Pos3 where
  | outer
  | middle
  | inner
deriving DecidableEq, Repr

inductive Traffic3 where
  | seven
  | eight
  | nine
deriving DecidableEq, Repr

inductive Endpoint1 where
  | A
deriving DecidableEq, Repr

inductive Control1 where
  | four
deriving DecidableEq, Repr

inductive Aggregate1 where
  | norm112
deriving DecidableEq, Repr

def ladder : Order6 → Ladder6
  | .T_F_tf  => .tf_Ftf_A
  | .T_tf_F  => .F_Ftf_A
  | .F_T_tf  => .tf_Ttf_A
  | .F_tf_T  => .T_Ttf_A
  | .tf_T_F  => .F_TF_A
  | .tf_F_T  => .T_TF_A

def decodeLadder : Ladder6 → Order6
  | .tf_Ftf_A => .T_F_tf
  | .F_Ftf_A  => .T_tf_F
  | .tf_Ttf_A => .F_T_tf
  | .T_Ttf_A  => .F_tf_T
  | .F_TF_A   => .tf_T_F
  | .T_TF_A   => .tf_F_T

def tfPos : Order6 → Pos3
  | .T_F_tf  => .inner
  | .T_tf_F  => .middle
  | .F_T_tf  => .inner
  | .F_tf_T  => .middle
  | .tf_T_F  => .outer
  | .tf_F_T  => .outer

def traffic : Order6 → Traffic3
  | .T_F_tf  => .nine
  | .T_tf_F  => .eight
  | .F_T_tf  => .nine
  | .F_tf_T  => .eight
  | .tf_T_F  => .seven
  | .tf_F_T  => .seven

def codePos : Pos3 → Traffic3
  | .outer  => .seven
  | .middle => .eight
  | .inner  => .nine

def decodeTraffic : Traffic3 → Pos3
  | .seven => .outer
  | .eight => .middle
  | .nine  => .inner

def swapTF : Order6 → Order6
  | .T_F_tf => .F_T_tf
  | .F_T_tf => .T_F_tf
  | .T_tf_F => .F_tf_T
  | .F_tf_T => .T_tf_F
  | .tf_T_F => .tf_F_T
  | .tf_F_T => .tf_T_F

def endpoint (_ : Order6) : Endpoint1 := .A
def control  (_ : Order6) : Control1 := .four
def aggregate (_ : Order6) : Aggregate1 := .norm112

theorem decode_ladder_left (o : Order6) :
    decodeLadder (ladder o) = o := by
  cases o <;> rfl

theorem ladder_decode_right (l : Ladder6) :
    ladder (decodeLadder l) = l := by
  cases l <;> rfl

theorem ladder_injective : Function.Injective ladder :=
  (show Function.LeftInverse decodeLadder ladder from decode_ladder_left).injective

theorem traffic_factors (o : Order6) :
    traffic o = codePos (tfPos o) := by
  cases o <;> rfl

theorem decode_traffic_position (p : Pos3) :
    decodeTraffic (codePos p) = p := by
  cases p <;> rfl

theorem swap_involution (o : Order6) :
    swapTF (swapTF o) = o := by
  cases o <;> rfl

theorem swap_preserves_position (o : Order6) :
    tfPos (swapTF o) = tfPos o := by
  cases o <;> rfl

theorem swap_preserves_traffic (o : Order6) :
    traffic (swapTF o) = traffic o := by
  cases o <;> rfl

theorem swap_changes_order (o : Order6) :
    swapTF o ≠ o := by
  cases o <;> decide

theorem endpoint_constant (o : Order6) :
    endpoint o = .A := rfl

theorem control_constant (o : Order6) :
    control o = .four := rfl

theorem aggregate_constant (o : Order6) :
    aggregate o = .norm112 := rfl

theorem traffic_eq_iff_position_eq (a b : Order6) :
    traffic a = traffic b ↔ tfPos a = tfPos b := by
  cases a <;> cases b <;> decide

theorem traffic_fibre_is_swap_orbit (a b : Order6) :
    traffic a = traffic b ↔ (b = a ∨ b = swapTF a) := by
  cases a <;> cases b <;> decide

theorem ladder_eq_iff_order_eq (a b : Order6) :
    ladder a = ladder b ↔ a = b := by
  constructor
  · exact fun h => ladder_injective h
  · exact fun h => congrArg ladder h

end Stage171_180
