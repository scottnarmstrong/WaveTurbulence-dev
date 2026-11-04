/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourcePairEnvelopes
public import WaveTurbulence.Foundations.Sumint.PairProductPower

/-!
# Ordinary pair envelopes fit the two-input block budget

The beta/2 source gain is weakened to beta/20 only after its exact
indicator has been retained. A common constant G at least one and at
least the ordinary pair constant provides G squared for each pair.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- An ordinary pair envelope fits the common two-input power budget. -/
theorem sourcePairEnvelope_le_ordinary_budget {d : ℕ} (D : SumintDatum d)
    {L δ β C G : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hβ : 0 ≤ β)
    (hG : 1 ≤ G) (hCG : C ≤ G) (γ η τstar CsA CmA CsC CmC : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (hna : ¬ caseAPair D a) (hnc : ¬ caseCPair D a) :
    sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC a ≤
      ENNReal.ofReal (G^2*δ⁻¹*L^(2*((d:ℝ)-γ)-(β/20)*(if pairIncoherent D a then (1:ℝ) else 0))) := by
  rw [sourcePairEnvelope,ite_eq_right hna,ite_eq_right hnc]
  apply ENNReal.ofReal_le_ofReal
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hC2 : C ≤ G^2 := hCG.trans (by nlinarith only [hG])
  have he : L^(2*((d:ℝ)-γ)-(if pairIncoherent D a then β/2 else 0)) ≤
      L^(2*((d:ℝ)-γ)-(β/20)*(if pairIncoherent D a then (1:ℝ) else 0)) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    split_ifs <;> linarith only [hβ]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hC2 (inv_nonneg.mpr hδ.le)) he
    (Real.rpow_nonneg hLp.le _) (by positivity)

/-- Nonzero pair positions are never the exceptional first case-(a)/(c) positions. -/
theorem not_special_pair_of_ne_zero {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : (a.2:ℕ) ≠ 0) :
    ¬ caseAPair D a ∧ ¬ caseCPair D a := by
  constructor
  · rintro ⟨_,_,h⟩
    exact ha h
  · rintro ⟨_,_,h⟩
    exact ha h

/-- Every pair in a normal block is ordinary. -/
theorem not_special_pair_of_normal {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : D.S.nor a.1 = true) :
    ¬ caseAPair D a ∧ ¬ caseCPair D a := by
  constructor <;> rintro ⟨h,_,_⟩ <;> simp only [ha,Bool.true_eq_false] at h

end WaveTurbulence.Sumint
