/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PositiveEndpointCost
public import WaveTurbulence.Foundations.Sumint.SourceOutputSet

/-!
# Actual finite-output positive kernel endpoint with the reserved 14d loss

The absolute endpoint constants and the polynomial M-factor are absorbed
into a constant to the literal input count. Its choice precedes delta
and the number of time steps. The output lattice count and actual trace
cost fit the explicit positive-endpoint L^(14d) allowance.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- An explicit absolute real majorant of the finite one- and two-exit kernel constant. -/
@[expose] noncomputable def sourceExitKernelRealConstant : ℝ := max 1 sourceExitKernelConstant.toReal

/-- The real majorant bounds the actual extended nonnegative endpoint constant. -/
theorem sourceExitKernelConstant_le_ofReal : sourceExitKernelConstant ≤ ENNReal.ofReal sourceExitKernelRealConstant := by
  rw [← ENNReal.ofReal_toReal sourceExitKernelConstant_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- TARGET sumint Step 3: the actual finite-output kernel positive endpoint has the common exponential-in-M constant and 14d loss. -/
theorem exists_source_kernel_positive_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d),
      ∀ (V : Type*) [Fintype V] (r : V → Mom d), (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) →
      (Fintype.card V:ℝ) ≤ (3*L)^(4*d) → ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 ((1:ℝ)/4) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p ν (r v)) z) ≤
        ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
          L^((D.S.M:ℝ)*((d:ℝ)-γ)-
            (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))+14*(d:ℝ))) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_finite_kernel_positive_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  let C := sourceExitKernelRealConstant
  let H := 12*C*3^(4*d)*G
  have hC : 1 ≤ C := le_max_left _ _
  have hCn : 0 ≤ C := zero_le_one.trans hC
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hC)
      (one_le_pow₀ (by norm_num))) hG
  refine ⟨H,hH,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν V _ r hr hcard hI c
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hM : 0 < D.S.M := size_pos D.S hI
  have hcost : 0 ≤ 2*(D.S.M:ℝ)*(Fintype.card V:ℝ) := by positivity
  calc
    _ ≤ sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      hbound L hL D A hD p ν V r hr hI c
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      mul_le_mul' (mul_le_mul' sourceExitKernelConstant_le_ofReal le_rfl) le_rfl
    _ = ENNReal.ofReal (C*(2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ)) := by
      rw [← ENNReal.ofReal_mul hCn,← ENNReal.ofReal_mul (mul_nonneg hCn hcost)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (finite_positive_endpoint_cost_le hC hG hL1 hδ.1 hM hcard)

end WaveTurbulence.Sumint
