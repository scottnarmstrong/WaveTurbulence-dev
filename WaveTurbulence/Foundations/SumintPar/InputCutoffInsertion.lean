/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputCutoffs
import Mathlib.Tactic

/-!
# Exact insertion of the independent input cutoffs

Hypothesis (iii) chooses cutoff centers using only the localization labels
and the prescribed output-ball centers. The product is identically one
on the support of the localized weight product, so inserting it before
Fourier expansion is an exact global identity in every lattice input.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The source cutoff at fixed scale four, with plain coordinate centers. -/
@[expose] noncomputable def inputCutoff {d : ℕ} (a : Fin d → ℝ) (x : Mom d) : ℝ :=
  Fourier.chi0Tensor (fun j => (x j-a j)/4)

/-- The fixed centers give exact cutoff insertion for the entire localized source weight product. -/
theorem exists_inputCutoff_insertion {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∃ p : D.S.VIdx → Fin d → ℝ,
      ∀ (E : Fin 4 → Mom d), (∀ c, ‖E c-D.centre c‖ ≤ 1) →
      ∀ x : D.S.VIdx → Fin d → ℤ,
      (∏ v, localizedWeight (a v) (D.wK v (E 0 - E 1)) (D.kVec L x E v) *
        localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)) =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ) *
      (∏ v, localizedWeight (a v) (D.wK v (E 0 - E 1)) (D.kVec L x E v) *
        localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)) := by
  classical
  choose z w hz using fun v => input_cutoff_eq_one D hD a b v
  let p : D.S.VIdx → Fin d → ℝ := fun v j =>
    choiceCenter D a b (z v) j-choiceCenter D a b (w v) j
  refine ⟨p, ?_⟩
  intro E hE x
  by_cases hP : (∏ v, localizedWeight (a v) (D.wK v (E 0 - E 1)) (D.kVec L x E v) *
      localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)) = 0
  · rw [hP, mul_zero]
  have hk (v : D.S.VIdx) : localizationProfile (a v) (D.kVec L x E v) ≠ 0 := by
    intro hv
    apply hP
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [localizedWeight, hv, zero_smul, zero_mul]
  have hl (v : D.S.VIdx) : localizationProfile (b v) (D.ℓVec L x E v) ≠ 0 := by
    intro hv
    apply hP
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp only [localizedWeight, hv, zero_smul, mul_zero]
  have hp (v : D.S.VIdx) : inputCutoff (p v) (latticePoint L (x v)) = 1 := hz v x E hk hl hE
  rw [show (∏ v, inputCutoff (p v) (latticePoint L (x v))) = 1 from
    Finset.prod_eq_one (fun v _ => hp v), Complex.ofReal_one, one_mul]

end WaveTurbulence.SumintPar
