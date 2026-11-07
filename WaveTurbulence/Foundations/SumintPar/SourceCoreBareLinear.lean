/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreNormalMass

/-!
# Distinguished linear cores without a normal or special pair companion

Case-(b) and case-(d) cores retain precisely their actual distinguished
linear mass and their literal external momentum multiplier.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- A non-normal linear core without a special pair has just its original linear factor. -/
theorem prod_sourceCore_bare_linear_fiber {d : ℕ} (D : SumintDatum d) {M : Type*} [CommMonoid M]
    (i : Fin D.S.I) (hnor : D.S.nor i = false)
    (hpair : ∀ a : Σ j : Fin D.S.I, Fin (D.S.m j), a.1 = i → ¬ (caseAPair D a ∨ caseCPair D a))
    [Fintype {a : FactorIdx D.S // sourceCoreGroup D a = .inl i}]
    (f : FactorIdx D.S → M) :
    (∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = .inl i}, f a.1) = f (.inl i) := by
  have hp (a : Σ j : Fin D.S.I, Fin (D.S.m j)) : sourceCoreGroup D (.inr (.inl a)) ≠ .inl i := by
    intro h
    by_cases ha : caseAPair D a ∨ caseCPair D a
    · have hi : a.1 = i := Sum.inl.inj (by simpa only [sourceCoreGroup,ite_eq_left ha] using h)
      exact hpair a hi ha
    · simp only [sourceCoreGroup,ite_eq_right ha] at h
      cases h
  have hn (j : {j : Fin D.S.I // D.S.nor j = true}) : sourceCoreGroup D (.inr (.inr j)) ≠ .inl i := by
    intro h
    have hi : j.1 = i := Sum.inl.inj h
    have ht : D.S.nor i = true := hi ▸ j.2
    rw [hnor] at ht
    cases ht
  rw [prod_fiber_subtype_eq_ite,Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp_rw [ite_eq_right (hp _),ite_eq_right (hn _)]
  simp [sourceCoreGroup]

/-- The concrete bare linear core mass retains its actual source linear mass and case-(b) multiplier. -/
theorem lintegral_sourceCore_bare_linear_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : Fin D.S.I) (hnor : D.S.nor i = false)
    (hpair : ∀ a : Σ j : Fin D.S.I, Fin (D.S.m j), a.1 = i → ¬ (caseAPair D a ∨ caseCPair D a)) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inl i) z) ≤
      caseBMultiplier D r i*linearFactorMass D L γ δ p ν r t c h i := by
  have he := lintegral_sourceCore_le_unordered D hL γ δ η p ν r t c h (.inl i)
  rw [prod_sourceCore_bare_linear_fiber D i hnor hpair,oldFactorWindowMass_linear] at he
  exact he

/-- A non-fixed coarse label has no old factors and therefore no coordinates. -/
theorem sourceCoreArity_eq_zero_of_not_fixed {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S)
    (hb : sourceCoreGroup D b ≠ b) : sourceCoreArity D b = 0 := by
  have hempty : IsEmpty (SourceCoreCoordinate D b) := ⟨fun z => hb
    ((congrArg (sourceCoreGroup D) z.1.2).symm.trans
      ((sourceCoreGroup_idempotent D z.1.1).trans z.1.2))⟩
  exact Fintype.card_eq_zero

end WaveTurbulence.SumintPar
