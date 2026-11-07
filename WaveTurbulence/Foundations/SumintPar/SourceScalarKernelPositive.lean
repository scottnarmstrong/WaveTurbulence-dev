/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.KernelPositiveFrequency
public import WaveTurbulence.Foundations.SumintPar.SourceSparseEndpointPower

/-!
# Actual scalar source kernel positive Fourier endpoint

The sparse L2 masses are proved from the original source coefficients.
Summing their two endpoint families costs exactly twice the literal M.
The explicit kernel satisfies the genuine time-integrability guard.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 3: the actual scalar localized kernel has its positive quarter-weight Fourier endpoint. -/
theorem exists_source_scalar_kernel_positive_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (hI : 0 < D.S.I) (c : ℝ),
      Fourier.timeFourierNorm ((1:ℝ)/4)
        (kernelExtension D hI c (L^(-β)) (weightedCutoffInput D L γ δ η p ν r)) ≤
        sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ))*
          ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_sparse_endpoint_L2_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r hr hrupper hI c
  have hLp : 0 < L := by linarith only [hR,hL]
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  let F := weightedCutoffInput D L γ δ η p ν r
  let B := ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ)
  have hFm : Measurable F := measurable_weightedCutoffInput D hLp γ δ η p ν r
  have hFi : IntegrableOn F (localInputTimeDomain D c (L^(-β))) :=
    integrableOn_weightedCutoffInput D hLp γ δ η hηthird p ν r c (L^(-β))
  have hmass (upper : Bool) (v : D.S.TVar) : sourceExitL2Mass D hI F c (L^(-β)) upper v ≤ B := by
    obtain ⟨htwo,hone⟩ := hbound L hL D A hD p ν r hr hrupper hI c upper
    by_cases hv : v = firstTime D hI
    · simp only [sourceExitL2Mass,ite_eq_left hv]
      exact hone
    · simp only [sourceExitL2Mass,ite_eq_right hv]
      exact htwo v hv
  rw [Fourier.timeFourierNorm_eq_lintegral (integrable_kernelExtension D hI c (L^(-β)) F hFm hFi)]
  apply (lintegral_timeFourier_kernelExtension_quarter_le D hI c (L^(-β)) F hFm hFi).trans
  calc
    _ ≤ sourceExitKernelConstant*((∑ _v : D.S.TVar, B)+(∑ _v : D.S.TVar, B)) :=
      mul_le_mul' le_rfl (add_le_add (Finset.sum_le_sum (fun v _ => hmass true v))
        (Finset.sum_le_sum (fun v _ => hmass false v)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,card_time_index,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_natCast]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

end WaveTurbulence.SumintPar
