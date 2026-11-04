/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceLinearMass
public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryMassBounds
public import WaveTurbulence.Foundations.Sumint.NormalBlockPower

/-!
# A genuine source normal block in the F23 range

The actual linear and normal masses are paired before their exponents
are weakened. For gamma greater than one half the second linear bound
leaves a strict reserve, which pays its extra delta loss at the later
lattice threshold uniformly in every datum and every block.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: actual normal-block cancellation for gamma greater than one half. -/
theorem exists_high_gamma_source_normal_block_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (1/2:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar)
    (ε : ℝ) (hε : ε < min (2*γ-1) (1-γ)) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1/16 → ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N → γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c h : ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      linearFactorMass D L γ δ p ν r t c h i.1 *
        normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i ≤
      ENNReal.ofReal (δ^(-2:ℝ)*L^(4*((d:ℝ)-γ)-ε)) := by
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_normalFactorMass_bound d hd γ ⟨by linarith [hγ.1],hγ.2⟩ τstar hτstar
  intro δ hδ hδsmall
  obtain ⟨R',hR',hnum⟩ := exists_high_gamma_normal_block_power_bound d hγ
    (scaledLinearConstant d*C) δ ε hδ hε
  refine ⟨max R R',hR.trans (le_max_left _ _),?_⟩
  intro L hL D N hτ A η hD hγη p ν r hr hrupper t c h i hh
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLR' : R' ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hl := linearFactorMass_le_f23 D hL1 hδ hδsmall hγη p ν r hr hrupper t c hh i.1
  have hn := hbound L hLR D δ N ⟨hδ,by linarith⟩ hτ A η hD p ν r t c h i hh
  have he : δ⁻¹*scaledLinearConstant d*L^((d:ℝ)+1-2*γ)*
      (C*δ^(-2:ℝ)*(L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L)) =
      (scaledLinearConstant d*C)*δ^(-3:ℝ)*L^((d:ℝ)+1-2*γ)*
        (L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*gammaBase γ)*Real.log L) := by
    have hpow : δ⁻¹*δ^(-2:ℝ) = δ^(-3:ℝ) := by
      rw [← Real.rpow_neg_one δ,← Real.rpow_add hδ]
      norm_num
    dsimp [gammaBase]
    calc
      _ = (scaledLinearConstant d*C)*(δ⁻¹*δ^(-2:ℝ))*L^((d:ℝ)+1-2*γ)*
        (L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L) := by ring
      _ = _ := by rw [hpow]
  calc
    _ ≤ ENNReal.ofReal (δ⁻¹*scaledLinearConstant d*L^((d:ℝ)+1-2*γ))*
        ENNReal.ofReal (C*δ^(-2:ℝ)*(L^(3*(d:ℝ)-4*γ)+
          L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L)) := mul_le_mul' hl hn
    _ = ENNReal.ofReal ((scaledLinearConstant d*C)*δ^(-3:ℝ)*L^((d:ℝ)+1-2*γ)*
        (L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*gammaBase γ)*Real.log L)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδ.le) (scaledLinearConstant_nonneg d)) (Real.rpow_nonneg hLp.le _)),he]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hnum L hLR')

end WaveTurbulence.Sumint
