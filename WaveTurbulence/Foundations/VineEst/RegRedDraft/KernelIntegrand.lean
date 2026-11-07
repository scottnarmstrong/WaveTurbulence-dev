/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.PhaseContinuity

/-! # The actual KG summand before its time integration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory Finset Set

noncomputable def kernelIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1))
      (LG.garden.extendTime s τ) *
    ∏ ℓ ∈ inputLeaves LG.garden,
      (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem integral_kernelIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, kernelIntegrand L γ δ F LG up s k₀ κ τ) =
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
      ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
  unfold kernelIntegrand phaseIntegral
  rw [integral_mul_const,integral_const_mul]

theorem aestronglyMeasurable_kernelIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    AEStronglyMeasurable (kernelIntegrand L γ δ F LG up s k₀ κ) :=
  ((LGSpine.aestronglyMeasurable_phaseIntegrand L γ δ LG up s
    (cosetDecoration LG.garden L k₀ κ.1)).const_mul _).mul_const _

theorem norm_kernelIntegrand_le {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) :
    ‖kernelIntegrand L γ δ F LG up s k₀ κ τ‖ ≤ LGSpine.inputLeafMajorant L F LG k₀ κ *
      (LGSpine.freeTimeBox LG).indicator (fun _ => (1 : ℝ)) τ := by
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := LGSpine.norm_phaseIntegrand_le_box L γ δ LG up s
    (cosetDecoration LG.garden L k₀ κ.1) τ
  have hprod : 0 ≤ LGSpine.inputLeafMajorant L F LG k₀ κ := prod_nonneg fun _ _ => abs_nonneg _
  unfold kernelIntegrand
  rw [norm_mul,norm_mul,norm_prod]
  simp only [Complex.norm_real,Real.norm_eq_abs]
  change |epsDec LG.garden κ.1| * ‖_‖ * LGSpine.inputLeafMajorant L F LG k₀ κ ≤ _
  have hm := (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    (by simpa only [one_mul] using hp)
  exact (mul_le_mul_of_nonneg_right hm hprod).trans_eq (mul_comm _ _)

theorem integrable_kernelIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelIntegrand L γ δ F LG up s k₀ κ) :=
  ((LGSpine.integrable_freeTimeBox LG).const_mul (LGSpine.inputLeafMajorant L F LG k₀ κ)).mono'
    (aestronglyMeasurable_kernelIntegrand L γ δ F LG up s k₀ κ)
    (Filter.Eventually.of_forall (norm_kernelIntegrand_le L γ δ F LG up s k₀ κ))

end WaveTurbulence.RegRed
