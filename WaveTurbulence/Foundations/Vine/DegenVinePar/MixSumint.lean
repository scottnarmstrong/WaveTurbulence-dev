/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixRecomb
public import WaveTurbulence.Foundations.SumintPar.SourceSumintBound
public import WaveTurbulence.Foundations.SumintPar.SmallParameterThreshold

/-! # `sumint` for sums weighted by a character mixture (DEGEN-VINE)

The `sumint` bound (`SumintPar.sumint`) holds for the lattice sum weighted by a character mixture `m(E, x)`
of mass `K`, with the constant multiplied by `K`.  The kernel estimate is the one of `sumint`, uniform in the
input modulation; only the recombination (`DegenVine.XNorm00Restr_mix_of_kernel_bound`) is redone.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

/-- TARGET sumint Steps 1--3 for a multiplied sum, before numerical absorption. -/
theorem exists_mix_restriction_interpolated_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : SumintSmallness d γ η)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (A : ℝ),
      1 ≤ A → D.Admissible A L γ η N → ∀ M : CharMix D.S d,
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => exprMix M hI L γ δ η t v) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M)*
        (ENNReal.ofReal M.mass *
        (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
          (ENNReal.ofReal (4^(2*η^8))*
            (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
              (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
              ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
                L^((D.S.M:ℝ)*((d:ℝ)-γ)-
                  (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
                  (1-interpolationWeight η)*(partitionExponent η/20)*(D.M₀:ℝ)+
                  14*(d:ℝ)*interpolationWeight η)))))) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_kernel_interpolated_bound d hd γ hγ η hη.eta_pos hη.eta_base
    hη.eta_small hη.gamma_eta hη.sqrt_base τstar hτstar (partitionExponent η)
    (partitionExponent_pos hη.eta_pos) hη.beta_linear hη.beta_pair hη.beta_normal hη.beta_high hη.eight_lt
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D hI A hA hD M
  have hLp : 0 < L := by linarith only [hR,hL]
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hh : L^(-partitionExponent η) ∈ Ioc (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hLp _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      linarith only [partitionExponent_pos hη.eta_pos])⟩
  have hθ : 2*η^8 ∈ Icc (0:ℝ) 1 := ⟨by positivity,by linarith only [hη.eight_lt]⟩
  let : Fintype (sourceOutputSet D L γ η) := (finite_sourceOutputSet D hLp γ η).fintype
  apply XNorm00Restr_mix_of_kernel_bound (by omega) M hI hA hLp
    (by linarith only [hη.eta_small]) hD hh hθ _ ENNReal.ofReal_lt_top
  intro p ν c
  exact hbound L hL D A hD p ν (sourceOutputSet D L γ η) (fun v => v.1 0-v.1 1)
    (sourceOutputSet_momentum_bounds D hLp γ η) (card_sourceOutputSet_le D hL1 γ η) hI c

/-- **`sumint` for multiplied sums**: the exact restriction estimate, with `C₁` independent of `δ`
and the step count, and the mass of the mixture as a factor. -/
theorem exists_mix_sumint_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0:ℝ) 1)
    (η : ℝ) (hη : SumintSmallness d γ η) (A : ℝ) (hA : 1 ≤ A)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I),
      D.Admissible A L γ η N → ∀ M : CharMix D.S d,
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => exprMix M hI L γ δ η t v) ≤
      ENNReal.ofReal (M.mass * (C1*parameterMaximum D^(η^6)*(C1*δ^(-(1:ℝ)/2))^D.S.M*
        L^(sourceTargetExponent D γ η))) := by
  obtain ⟨G,hG,hbound⟩ := exists_mix_restriction_interpolated_bound d hd γ hγ η hη τstar hτstar
  let C1 := sourceAssemblyConstant d A G
  refine ⟨C1,one_le_sourceAssemblyConstant _ _ _,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  have hηpos := hη.eta_pos
  obtain ⟨Rstep,hRstep,hstep⟩ := exists_constant_le_rpow
    (cellMultiplierRealConstant N*((N:ℝ)+5)) (show 0 < η^7/2 by positivity)
  refine ⟨max R Rstep,hR.trans (le_max_left _ _),?_⟩
  intro L hL D hI hD M
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLS : Rstep ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hR,hLR]
  have hL1 : 1 ≤ L := by linarith only [hR,hLR]
  have hS : 0 ≤ sourceCoefficientBase d A := sourceCoefficientBase_nonneg d hA
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hP : 0 < parameterMaximum D := zero_lt_one.trans_le (one_le_parameterMaximum D hI)
  have hcell : 0 < cellMultiplierRealConstant N := zero_lt_one.trans_le (one_le_cellMultiplierRealConstant N)
  apply (hbound L hLR D hI A hA hD M).trans
  have hbudget := source_real_budget_le D hI hA hG hL1 hδ.1 hη N (hstep L hLS)
  change ENNReal.ofReal (sourceCoefficientBase d A^D.S.M)*
    (ENNReal.ofReal M.mass *
    (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
      (ENNReal.ofReal (4^(2*η^8))*
        (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
          (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
          ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^(sourceKernelExponent D γ η)))))) ≤ _
  rw [mul_left_comm]
  have hm := M.mass_nonneg
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc _ = M.mass * (sourceCoefficientBase d A ^ D.S.M * (2 ^ (2 * η ^ 8) * ((((D.S.M : ℝ) + 1) * parameterMaximum D) ^ (2 * η ^ 8)) *
        (4 ^ (2 * η ^ 8) * (cellMultiplierRealConstant N * ((N : ℝ) + 5) * (L ^ (-partitionExponent η))⁻¹ * (L ^ (-partitionExponent η))⁻¹ *
          (G ^ D.S.M * δ ^ (-(D.S.M : ℝ) / 2) * L ^ sourceKernelExponent D γ η))))) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hm
      convert hbudget using 1; ring

end WaveTurbulence.DegenVinePar
