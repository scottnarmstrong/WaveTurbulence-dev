/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreFiberProducts
public import WaveTurbulence.Foundations.Sumint.OldPairMassIdentity

/-!
# Actual normal coarse cores retain the established four-input mass

A normal core is bounded by exactly its distinguished linear mass times
its native three-time normal mass. Thus its oscillatory four-input gain
survives unchanged whenever the core is untouched by fixed coordinates.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual normal core mass is bounded by the literal linear-normal source mass product. -/
theorem lintegral_sourceCore_normal_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inl i.1) z) ≤
      linearFactorMass D L γ δ p ν r t c h i.1 *
        normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i := by
  have he := lintegral_sourceCore_le_unordered D hL γ δ η p ν r t c h (.inl i.1)
  rw [prod_sourceCore_normal_fiber,oldFactorWindowMass_linear,oldFactorWindowMass_normal] at he
  have hm : sourceCoreMultiplier D r (.inl i.1) = 1 := by
    change caseBMultiplier D r i.1 = 1
    simp only [caseBMultiplier,i.2,Bool.true_eq_false,false_and,ite_false]
  simpa only [hm,one_mul] using he

/-- The actual noncollapsed pair core mass is bounded by its literal source pair mass. -/
theorem lintegral_sourceCore_pair_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i))
    (ha : ¬ (caseAPair D a ∨ caseCPair D a)) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inr (.inl a)) z) ≤
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a := by
  have he := lintegral_sourceCore_le_unordered D hL γ δ η p ν r t c h (.inr (.inl a))
  rw [prod_sourceCore_pair_fiber D a ha,oldFactorWindowMass_pair D L γ δ η p ν r t c h u a
    (fun hh => ha (Or.inl hh))] at he
  simpa only [sourceCoreMultiplier,one_mul] using he

end WaveTurbulence.Sumint
