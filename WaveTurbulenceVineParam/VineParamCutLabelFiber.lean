/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceFlowTransport
import Mathlib.Tactic

/-! # The full old-label fiber at a marked two-edge source cut -/

public section
namespace WaveTurbulence.Vine.Param
variable {β E : Type*} [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- Restore both individually marked occurrences, retaining every other label. -/
@[expose] def assembleCutLabels (i j : β) (rest : {e : β // e ≠ i ∧ e ≠ j} → E)
    (c d : E) (e : β) : E :=
  if hi : e=i then c else if hj : e=j then d else rest ⟨e,hi,hj⟩

omit [Fintype β] [AddCommGroup E] in
/-- The first marked occurrence keeps its own restored label. -/
theorem assembleCutLabels_first (i j : β) (rest : {e : β // e ≠ i ∧ e ≠ j} → E) (c d : E) :
    assembleCutLabels i j rest c d i=c := by simp [assembleCutLabels]

omit [Fintype β] [AddCommGroup E] in
/-- The second marked occurrence keeps its own restored label. -/
theorem assembleCutLabels_second (i j : β) (hij : i ≠ j)
    (rest : {e : β // e ≠ i ∧ e ≠ j} → E) (c d : E) :
    assembleCutLabels i j rest c d j=d := by simp [assembleCutLabels,Ne.symm hij]

omit [Fintype β] [AddCommGroup E] in
/-- Every uncut occurrence keeps its exact original label. -/
theorem assembleCutLabels_rest (i j : β) (rest : {e : β // e ≠ i ∧ e ≠ j} → E) (c d : E)
    (e : {e : β // e ≠ i ∧ e ≠ j}) :
    assembleCutLabels i j rest c d e.1=rest e := by
  simp [assembleCutLabels,e.2.1,e.2.2]

/-- Old cut labels with their physical oriented rail gap. -/
@[expose] def CutLabelFiber (i j : β) (P : RungPattern) (r : E) :=
  {k : β → E // k i=P.upperBefore r (k j)}

/-- The entire old-label cut fiber consists of the unrestricted remaining
occurrences and one actual preceding rail label. Parallel bonds stay distinct. -/
@[expose] def cutLabelChart (i j : β) (hij : i ≠ j) (P : RungPattern) (r : E) :
    CutLabelFiber i j P r ≃ (({e : β // e ≠ i ∧ e ≠ j} → E)×E) where
  toFun := fun k => (fun e => k.1 e.1,k.1 j)
  invFun := fun q => ⟨assembleCutLabels i j q.1 (P.upperBefore r q.2) q.2,by
    rw [assembleCutLabels_first,assembleCutLabels_second i j hij]⟩
  left_inv := by
    intro k
    apply Subtype.ext
    funext e
    change assembleCutLabels i j (fun e => k.1 e.1) (P.upperBefore r (k.1 j)) (k.1 j) e=k.1 e
    by_cases hi : e=i
    · subst e
      rw [assembleCutLabels_first]
      exact k.2.symm
    · by_cases hj : e=j
      · subst e
        exact assembleCutLabels_second i j hij _ _ _
      · simp [assembleCutLabels,hi,hj]
  right_inv := by
    intro q
    apply Prod.ext
    · funext e
      exact assembleCutLabels_rest i j q.1 _ _ e
    · exact assembleCutLabels_second i j hij _ _ _

end WaveTurbulence.Vine.Param
