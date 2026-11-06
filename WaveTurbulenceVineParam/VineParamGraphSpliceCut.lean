/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSplice
public import WaveTurbulenceVineParam.VineParamGraphCutFlow
public import WaveTurbulenceVineParam.VineParamRungGapTransport
import Mathlib.Tactic

/-! # Exact physical cut flux of the inserted cap

Only the two following rails cross the lifted old cap. Its flux is therefore
the negative oriented following gap, independently of all remaining labels.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- The same old cap, embedded among the old vertices after insertion. -/
@[expose] def spliceCap (C : Finset V) : Finset (V ⊕ Fin 2) := C.image Sum.inl

omit [Fintype β] [DecidableEq β] [AddCommGroup E] in
/-- Old atom membership in the cap is unchanged. -/
theorem mem_spliceCap_inl (C : Finset V) (v : V) : Sum.inl v ∈ spliceCap C ↔ v ∈ C := by
  simp [spliceCap]

omit [Fintype β] [DecidableEq β] [AddCommGroup E] in
/-- Both fresh rung atoms lie outside the fixed old cap. -/
theorem not_mem_spliceCap_inr (C : Finset V) (v : Fin 2) : Sum.inr v ∉ spliceCap C := by
  simp [spliceCap]

omit [Fintype β] [DecidableEq β] in
/-- No remaining old occurrence crosses the lifted cap. -/
theorem rungSpliceCut_rest (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) (C : Finset V)
    (hσ : ∀ v,σ v ∈ C ↔ v ∈ C)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (e : {e : β // e ≠ i ∧ e ≠ j}) :
    cutSign (rungSpliceEnds ends i j σ p q c d P) (spliceCap C) (.inl e)=0 := by
  have he := hrest e.1 e.2.1 e.2.2
  simp only [cutSign,rungSpliceEnds,mem_spliceCap_inl,hσ,he,sub_self]

/-- The exact new cap flux has only its following upper/lower rail labels. -/
theorem rungSpliceCut_flux (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) (C : Finset V)
    (hσ : ∀ v,σ v ∈ C ↔ v ∈ C)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) :
    (∑ e : SpliceEdge i j,cutSign (rungSpliceEnds ends i j σ p q c d P) (spliceCap C) e •
      rungSpliceLabels i j old z e)= -(P.signs 3) • z 4+P.signs 3 • z 5 := by
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j} ⊕ Fin 6,
    cutSign (rungSpliceEnds ends i j σ p q c d P) (spliceCap C) e • rungSpliceLabels i j old z e)=_
  rw [Fintype.sum_sum_type]
  simp only [rungSpliceCut_rest ends i j σ p q c d P C hσ hrest,zero_zsmul,sum_const_zero,zero_add]
  cases P
  all_goals simp [cutSign,rungSpliceEnds,rungSpliceLabels,orientPair,RungPattern.signs,
    mem_spliceCap_inl,not_mem_spliceCap_inr,hp,hq,hc,hd,Fin.sum_univ_succ]

end WaveTurbulence.Vine.Param
