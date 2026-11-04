/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.FirstPairRescale
public import WaveTurbulence.Foundations.Sumint.FirstPairLinearPower
public import WaveTurbulence.Foundations.Sumint.SourceLinearBranch

/-!
# Pairing a literal first-pair envelope with the actual source linear mass

The envelope has separate stationary and Weyl contributions. Its constants
are fixed as L varies, but may depend on delta and Dsteps. This helper
proves the combined bound for the actual distinguished linear mass;
separate source lemmas insert the actual ordered first-pair masses.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The physical stationary/Weyl envelope of a first bad pair. -/
@[expose] noncomputable def firstPairEnvelope (d : ℕ) (L γ δ η p Cs Cm K : ℝ) : ℝ :=
  (16*sourceHalfScale L γ δ)⁻¹*
    ((16*sourceHalfScale L γ δ)^(-p)*Cs*(4*L)^(2*d)+
      K*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))

/-- The literal envelope is nonnegative for the source coefficient signs. -/
theorem firstPairEnvelope_nonneg (d : ℕ) {L δ Cs Cm K : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (γ η p : ℝ) :
    0 ≤ firstPairEnvelope d L γ δ η p Cs Cm K := by
  unfold firstPairEnvelope sourceHalfScale
  positivity

/-- Actual distinguished linear mass times the first-pair envelope has a uniform bad-block gain. -/
theorem exists_source_first_pair_envelope_linear_bound (d : ℕ) (hd : 3 ≤ d) {γ η p : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : η ≤ gammaBase γ) (hp : 7/8 ≤ p)
    (δ Cs Cm K : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16)
    (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d), γ+η ≤ 1 →
      ∀ (q : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c h : ℝ) (i : Fin D.S.I), h ∈ Icc (0:ℝ) 1 →
      linearFactorMass D L γ δ q ν r t c h i *
        ENNReal.ofReal (firstPairEnvelope d L γ δ η p Cs Cm K) ≤
      ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/2)) := by
  let Ks := Cs*(8:ℝ)^(-(1+p))*δ^(-(1+p))*4^(2*d)
  let Kw := K*Cm*(8:ℝ)⁻¹*δ⁻¹*4^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)
  have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
  have hKw : 0 ≤ Kw := by dsimp [Kw]; positivity
  obtain ⟨R,hR,hbound⟩ := exists_first_pair_linear_power_bound d hd hγ hη hp
    (3*(12:ℝ)^d) (sourceLinearBranchConstant d*δ⁻¹) Ks Kw hKs hKw
  refine ⟨R,hR,?_⟩
  intro L hL D hγη q ν r hr hrupper t c h i hh
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  let J := ∫ s in Icc (enlargedTimeLower D c h (.inl ⟨i,0⟩))
    (enlargedTimeUpper D c h (.inl ⟨i,0⟩)), ‖linearTimeSum D L γ δ q ν r t i s‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  have hJ₀ : J ≤ (3*(12:ℝ)^d)*L^(d:ℝ) := by
    have hb := linearFactorMass_le_trivial D hL1 hδ γ q ν r t c hh i
    rw [linearFactorMass_eq_ofReal_integral D hLp] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hJ₁ : J ≤ (sourceLinearBranchConstant d*δ⁻¹)*L^((d:ℝ)-γ+gammaBase γ) := by
    have hb := linearFactorMass_le_best_branch D hL1 hδ hδsmall hγη q ν r hr hrupper t c hh i
    rw [linearFactorMass_eq_ofReal_integral D hLp] at hb
    have hconst : 0 ≤ sourceLinearBranchConstant d :=
      (by positivity : 0 ≤ 3*(12:ℝ)^d).trans (le_max_left _ _)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  rw [linearFactorMass_eq_ofReal_integral D hLp,← ENNReal.ofReal_mul hJ]
  apply ENNReal.ofReal_le_ofReal
  unfold firstPairEnvelope
  rw [first_pair_source_rescale d hLp hδ]
  exact hbound L hL J hJ₀ hJ₁

end WaveTurbulence.Sumint
