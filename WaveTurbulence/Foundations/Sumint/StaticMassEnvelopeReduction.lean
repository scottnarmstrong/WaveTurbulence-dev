/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceLinearMass
public import WaveTurbulence.Foundations.Sumint.SourceFactorMasses
public import WaveTurbulence.Foundations.Sumint.MassProductBound
public import WaveTurbulence.Foundations.Sumint.BlockMassProducts

/-!
# Inserting uniform pair envelopes into the actual static-domain mass

This is an explicitly conditional reduction, used after proving the
uniform source envelope bounds. The output retains the actual linear
and normal masses, grouped by the original source blocks. No oscillatory
estimate is assumed for the entire source integral.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- Uniform local pair envelopes reduce the literal source static mass to the original block product. -/
theorem static_mass_uniform_pair_envelope_reduction {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N) (hL : 0 < L)
    (δ : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (B : (Σ i : Fin D.S.I, Fin (D.S.m i)) → ℝ≥0∞)
    (hB : ∀ (u : Fin D.S.I → ℝ) a,
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤ B a) :
    (∫⁻ τ in Icc (enlargedTimeLower D c h) (enlargedTimeUpper D c h) ∩ staticTimeDomain D,
      ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) ≤
      ∏ i : Fin D.S.I, linearFactorMass D L γ δ p ν r t c h i *
        (∏ j : Fin (D.S.m i), B ⟨i,j⟩)*
        normalMassInBlock D.S
          (normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h)) i := by
  let lo := enlargedTimeLower D c h
  let hi := enlargedTimeUpper D c h
  let F : Fin D.S.I → ℝ → ℝ≥0∞ := fun i s => ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i s‖
  let P : (Fin D.S.I → ℝ) → (Σ i : Fin D.S.I, Fin (D.S.m i)) → ℝ≥0∞ :=
    fun u a => orderedPairMass D L γ δ η p ν r t lo hi u a
  let Q : {i : Fin D.S.I // D.S.nor i = true} → ℝ≥0∞ :=
    normalFactorMass D L γ δ p ν r t lo hi
  have hF (i : Fin D.S.I) : Measurable (F i) :=
    (continuous_linearTimeSum D hL γ δ p ν r t i).norm.measurable.ennreal_ofReal
  have hb := lintegral_linear_family_product_le D.S lo hi F hF P B Q Q
    (fun u _ a => hB u a) (fun _ => le_rfl)
  apply (lintegral_static_box_cutoffPhaseSum_le_factor_masses D hD hL δ p ν r t lo hi).trans
  apply hb.trans_eq
  exact prod_block_masses D.S (linearFactorMass D L γ δ p ν r t c h) B Q

end WaveTurbulence.Sumint
