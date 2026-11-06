/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCutLabelFiber
public import WaveTurbulenceVineParam.VineParamGraphSpliceGap
import Mathlib.Tactic

/-! # Exact full six-label local conservation fiber -/

public section
namespace WaveTurbulence.Vine.Param
variable {E : Type*} [AddCommGroup E]

/-- All six actual local labels, constrained only by their preceding gap
and the two actual source momentum rows. -/
@[expose] def SixLabelFiber (P : RungPattern) (r : E) :=
  {z : Fin 6 → E // z 0=P.upperBefore r (z 1) ∧
    P.signs 0 • z 2+P.signs 1 • z 3+P.signs 3 • z 4-P.signs 2 • z 0=0 ∧
    P.signs 0 • z 2+P.signs 1 • z 3+P.signs 3 • z 5-P.signs 2 • z 1=0}

/-- The full local conservation fiber is parametrized by the preceding
lower rail and the two actual differences, over every additive group. -/
@[expose] def sixLabelChart (P : RungPattern) (r : E) : SixLabelFiber P r ≃ (E×(E×E)) where
  toFun := fun z => (z.1 1,P.encode (z.1 1) (z.1 2,z.1 3))
  invFun := fun q => ⟨spliceChartLabels P r q.1 q.2,by
    change P.upperBefore r q.1=P.upperBefore r q.1 ∧ _ ∧ _
    exact ⟨rfl,P.momentum_additive r q.1 q.2⟩⟩
  left_inv := by
    intro z
    apply Subtype.ext
    funext i
    have hdec := P.decode_encode (z.1 1) (z.1 2,z.1 3)
    have hupper := P.upperAfter_of_conservation r (z.1 2) (z.1 3) (z.1 1) (z.1 4)
      (by rw [← z.2.1]; exact z.2.2.1)
    have hlower := P.lowerAfter_of_conservation (z.1 2) (z.1 3) (z.1 1) (z.1 5) z.2.2.2
    fin_cases i
    · exact z.2.1.symm
    · rfl
    · exact congrArg Prod.fst hdec
    · exact congrArg Prod.snd hdec
    · exact hupper
    · exact hlower
  right_inv := by
    intro q
    apply Prod.ext
    · rfl
    · change P.encode q.1 (P.decode q.1 q.2)=q.2
      exact P.encode_decode q.1 q.2

/-- A globally source-conserving inserted graph yields precisely the complete
local fiber. Its gap is forced by cap conservation, not an extra assumption. -/
@[expose] def sixLabelFiberOfSource {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
    (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d a b : V) (hab : a ≠ b) (P : RungPattern) (C : Finset V)
    (hσ : ∀ v,σ v ∈ C ↔ v ∈ C)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) (r : E)
    (ha : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl a) (rungSpliceLabels i j old z)= -r)
    (hb : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl b) (rungSpliceLabels i j old z)=r)
    (hzero : ∀ v,v ≠ .inl a → v ≠ .inl b →
      directedFlow (rungSpliceEnds ends i j σ p q c d P) v (rungSpliceLabels i j old z)=0) :
    SixLabelFiber P (spliceGap C a b r) := by
  refine ⟨z,rungSplice_preceding_gap ends i j σ p q c d a b hab P C hσ hrest hp hq hc hd old z r ha hb hzero,?_,?_⟩
  · simpa only [rungSpliceFlow_upper] using hzero (.inr 0) (by simp) (by simp)
  · have h := hzero (.inr 1) (by simp) (by simp)
    rw [rungSpliceFlow_lower] at h
    exact neg_eq_zero.mp h

end WaveTurbulence.Vine.Param
