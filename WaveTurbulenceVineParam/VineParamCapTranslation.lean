/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamDirectedTransport
import Mathlib.Tactic

/-! # Component translations after removing a cap's two crossing bonds

On a cut-free remainder every bond has both endpoints on the same side.
Translation there is uniform at each incident atom. The exact laws below
therefore apply to the pinned caps after their two marked occurrences are
erased, with no new resonance hypothesis.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β]

section Additive
variable [AddCommGroup E]

/-- Translate exactly the physical bond labels in a cap component. -/
@[expose] def capTranslate (ends : β → V×V) (C : Finset V) (k : β → E) (t : E) : β → E :=
  fun j => k j+(if (ends j).1 ∈ C then t else 0)

omit [Fintype β] in
/-- At either endpoint of an uncut bond, the shift is that of its atom. -/
theorem capTranslate_incident (ends : β → V×V) (C : Finset V)
    (hC : ∀ j,(ends j).1 ∈ C ↔ (ends j).2 ∈ C) (k : β → E) (t : E) (v : V) (j : β)
    (hj : (ends j).1=v ∨ (ends j).2=v) :
    capTranslate ends C k t j=k j+(if v ∈ C then t else 0) := by
  rcases hj with h | h
  · simp only [capTranslate,h]
  · have hm : (ends j).1 ∈ C ↔ v ∈ C := (hC j).trans (by rw [h])
    simp only [capTranslate,hm]

/-- Component translation acts on flow like uniform translation at the atom. -/
theorem capTranslate_flow (ends : β → V×V) (C : Finset V)
    (hC : ∀ j,(ends j).1 ∈ C ↔ (ends j).2 ∈ C) (k : β → E) (t : E) (v : V) :
    directedFlow ends v (capTranslate ends C k t)=
      directedFlow ends v k+(∑ j,-energySign ends v j) • (if v ∈ C then t else 0) := by
  rw [← directedFlow_translate]
  apply sum_congr rfl
  intro j _hj
  by_cases hi : (ends j).1=v ∨ (ends j).2=v
  · rw [capTranslate_incident ends C hC k t v j hi]
  · have ht := not_or.mp hi
    simp only [energySign,ht.1,ht.2,ite_false,sub_zero,neg_zero,zero_zsmul]

end Additive

section Inner
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact molecular energy law on an uncut cap component. Its balanced
interior specialization follows by zero source flow and signed degree. -/
theorem capTranslate_energy (ends : β → V×V) (C : Finset V)
    (hC : ∀ j,(ends j).1 ∈ C ↔ (ends j).2 ∈ C) (k : β → E) (t : E) (v : V) :
    directedEnergy ends v (capTranslate ends C k t)=directedEnergy ends v k+
      2*inner ℝ (∑ j,(energySign ends v j : ℝ) • k j) (if v ∈ C then t else 0)+
      (∑ j,(energySign ends v j : ℝ))*‖(if v ∈ C then t else 0)‖^2 := by
  unfold directedEnergy
  rw [← signed_energy_translate]
  apply sum_congr rfl
  intro j _hj
  by_cases hi : (ends j).1=v ∨ (ends j).2=v
  · rw [capTranslate_incident ends C hC k t v j hi]
  · have ht := not_or.mp hi
    simp only [energySign,ht.1,ht.2,ite_false,sub_zero,Int.cast_zero,zero_mul]

end Inner
end WaveTurbulence.Vine.Param
