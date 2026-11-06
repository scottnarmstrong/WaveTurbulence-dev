/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractedGraph
public import WaveTurbulenceVineParam.VineParamSpliceOrientation
public import WaveTurbulenceVineParam.VineParamBalancedCutOrientation
public import WaveTurbulenceVineParam.VineParamLiftedCap
import Mathlib.Tactic

/-! # Actual six-edge source cells before orientation normalization -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V]

/-- The six undirected geometric cell ports, before choosing directions. -/
@[expose] def sourceCellPorts (p q c d : V) : Fin 6 → (V ⊕ Fin 2)×(V ⊕ Fin 2) :=
  ![(.inl p,.inr 0),(.inl q,.inr 1),(.inr 0,.inr 1),(.inr 0,.inr 1),
    (.inr 0,.inl c),(.inr 1,.inl d)]

/-- The six actual directions are initially independent source data. -/
@[expose] def rawSourceCellEnds (rest : β → V×V) (p q c d : V) (s : Fin 6 → ℤ) :
    β ⊕ Fin 6 → (V ⊕ Fin 2)×(V ⊕ Fin 2)
  | .inl e => (.inl (rest e).1,.inl (rest e).2)
  | .inr j => orientPair (s j) (sourceCellPorts p q c d j).1 (sourceCellPorts p q c d j).2

/-- The integer degree contribution of a signed actual edge. -/
theorem degree_orientPair (s : ℤ) (hs : s=1 ∨ s= -1) (u w v : V) :
    -energySign (fun _ : Unit => orientPair s u w) v ()=
      s*((if u=v then 1 else 0)-(if w=v then 1 else 0)) := by
  rcases hs with rfl | rfl <;> simp [energySign,orientPair]

omit [DecidableEq V] in
/-- Once classified from the source rows, the raw cell is exactly the
normalized source cell used by contraction. -/
theorem rawSourceCell_normalized (rest : β → V×V) (p q c d : V) (P : RungPattern) :
    rawSourceCellEnds rest p q c d
      ![P.signs 2,-P.signs 2,P.signs 0,P.signs 1,P.signs 3,-P.signs 3]=
      sourceCellEnds rest p q c d P := by
  funext e
  cases e with
  | inl e => rfl
  | inr j => fin_cases j <;> rfl

end WaveTurbulence.Vine.Param
