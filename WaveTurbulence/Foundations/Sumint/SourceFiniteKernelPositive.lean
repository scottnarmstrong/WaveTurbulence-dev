/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceScalarKernelPositive
public import WaveTurbulence.Foundations.Sumint.FiniteOutputNorm

/-!
# Actual positive Fourier endpoint for finite output families

Only this positive endpoint pays the finite output cardinality. The
negative endpoint retains its output supremum inside the frequency
integral, so interpolation incurs only the small positive-endpoint
fraction of this cardinality loss.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 3: the actual finite-output localized kernel has its positive quarter-weight endpoint. -/
theorem exists_source_finite_kernel_positive_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
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
      ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 ((1:ℝ)/4) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p ν (r v)) z) ≤
        sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
          ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_scalar_kernel_positive_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν V _ r hr hI c
  have hLp : 0 < L := by linarith only [hR,hL]
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  have hFi (v : V) : Integrable (kernelExtension D hI c (L^(-β))
      (weightedCutoffInput D L γ δ η p ν (r v))) :=
    integrable_kernelExtension D hI c (L^(-β)) _ (measurable_weightedCutoffInput D hLp γ δ η p ν (r v))
      (integrableOn_weightedCutoffInput D hLp γ δ η hηthird p ν (r v) c (L^(-β)))
  calc
    _ ≤ ∑ v : V, Fourier.timeFourierNorm ((1:ℝ)/4) (kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p ν (r v))) :=
      XNorm00_le_sum_scalar ((1:ℝ)/4) _ hFi
    _ ≤ ∑ _v : V, sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      Finset.sum_le_sum (fun v _ => hbound L hL D A hD p ν (r v) (hr v).1 (hr v).2 hI c)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(D.S.M:ℝ)),ENNReal.ofReal_natCast]
      ring

end WaveTurbulence.Sumint
