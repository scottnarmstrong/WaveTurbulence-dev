/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceLinearMass
public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryMassBounds
public import WaveTurbulence.Foundations.Sumint.NormalBlockPower

/-!
# A genuine source normal block in the low-gamma range

The trivial distinguished linear bound pairs with the cubic stationary
contribution exactly at the four-input scale. The cubic Weyl contribution
has a strict reserve. Constants and the lattice threshold precede delta,
so this branch preserves the required delta power without absorption.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: actual low-gamma normal-block cancellation with constants before delta. -/
theorem exists_low_gamma_source_normal_block_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioc (0:ℝ) (1/2)) (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C R : ℝ, 1 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
        (i : {i : Fin D.S.I // D.S.nor i = true}), h ∈ Icc (0:ℝ) 1 →
      linearFactorMass D L γ δ p ν r t c h i.1 *
        normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i ≤
      ENNReal.ofReal (C*δ^(-2:ℝ)*L^(4*((d:ℝ)-γ))) := by
  obtain ⟨C,R,hC,hR,hbound⟩ := exists_normalFactorMass_bound d hd γ ⟨hγ.1,by linarith [hγ.2]⟩ τstar hτstar
  obtain ⟨R',hR',hnum⟩ := exists_low_gamma_normal_block_power_bound d hγ
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hC' : 1 ≤ 6*(12:ℝ)^d*C := by
    have hp : 1 ≤ (12:ℝ)^d := one_le_pow₀ (by norm_num)
    nlinarith
  refine ⟨6*(12:ℝ)^d*C,max R R',hC',hR.trans (le_max_left _ _),?_⟩
  intro L hL D δ N hδ hτ A η hD p ν r t c h i hh
  have hδp : 0 < δ := hδ.1
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLR' : R' ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hl := linearFactorMass_le_trivial D hL1 hδ.1 γ p ν r t c hh i.1
  have hn := hbound L hLR D δ N hδ hτ A η hD p ν r t c h i hh
  calc
    _ ≤ ENNReal.ofReal (3*(12:ℝ)^d*L^(d:ℝ))*
        ENNReal.ofReal (C*δ^(-2:ℝ)*(L^(3*(d:ℝ)-4*γ)+
          L^(3*(d:ℝ)-3*γ-2*min γ (1-γ))*Real.log L)) := mul_le_mul' hl hn
    _ = ENNReal.ofReal ((3*(12:ℝ)^d*C*δ^(-2:ℝ))*
        (L^(d:ℝ)*(L^(3*(d:ℝ)-4*γ)+L^(3*(d:ℝ)-3*γ-2*gammaBase γ)*Real.log L))) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3*(12:ℝ)^d*L^(d:ℝ))]
      congr 1
      dsimp [gammaBase]
      ring
    _ ≤ ENNReal.ofReal ((3*(12:ℝ)^d*C*δ^(-2:ℝ))*(2*L^(4*((d:ℝ)-γ)))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hnum L hLR') (by positivity))
    _ = _ := by congr 1; ring

end WaveTurbulence.Sumint
