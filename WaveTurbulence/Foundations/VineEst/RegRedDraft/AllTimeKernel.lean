/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelFubini
public import WaveTurbulence.Foundations.VineEst.UnmarkedPhaseIntegral

/-! # Actual kernels on full branching-time coordinates when there are no flowers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory TTree

noncomputable def allTimeEquiv {w : ℕ} (G : Garden w) (hG : ∀ b, ¬ G.IsFlowerParent b) :
    (G.FreeBranch → ℝ) ≃ᵐ (GBranch G.tree → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (LGSpine.freeBranchEquivOfNoFlowerParent G hG)

theorem measurePreserving_allTimeEquiv {w : ℕ} (G : Garden w) (hG : ∀ b, ¬ G.IsFlowerParent b) :
    MeasurePreserving (allTimeEquiv G hG) volume volume :=
  measurePreserving_piCongrLeft (fun _ : GBranch G.tree => (volume : Measure ℝ))
    (LGSpine.freeBranchEquivOfNoFlowerParent G hG)

theorem extendTime_eq_allTimeEquiv {w : ℕ} (G : Garden w) (hG : ∀ b, ¬ G.IsFlowerParent b)
    (s : ℝ) (τ : G.FreeBranch → ℝ) : G.extendTime s τ = allTimeEquiv G hG τ := by
  funext b
  simp only [Garden.extendTime,hG b,dite_false]
  rfl

theorem extendTime_allTimeEquiv_symm {w : ℕ} (G : Garden w) (hG : ∀ b, ¬ G.IsFlowerParent b)
    (s : ℝ) (τ : GBranch G.tree → ℝ) : G.extendTime s ((allTimeEquiv G hG).symm τ) = τ :=
  (extendTime_eq_allTimeEquiv G hG s _).trans ((allTimeEquiv G hG).apply_symm_apply τ)

noncomputable def kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ *
    ∏ ℓ ∈ inputLeaves LG.garden,
      (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem kernelAllIntegrand_allTimeEquiv {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : LG.garden.FreeBranch → ℝ) :
    kernelAllIntegrand L γ δ F LG up s k₀ κ (allTimeEquiv LG.garden hG τ) =
      kernelIntegrand L γ δ F LG up s k₀ κ τ := by
  unfold kernelAllIntegrand kernelIntegrand
  rw [extendTime_eq_allTimeEquiv LG.garden hG]

theorem integrable_kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelAllIntegrand L γ δ F LG up s k₀ κ) := by
  have hi := (measurePreserving_allTimeEquiv LG.garden hG).symm.integrable_comp_of_integrable
    (integrable_kernelIntegrand L γ δ F LG up s k₀ κ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro τ
  exact (kernelAllIntegrand_allTimeEquiv L γ δ F LG hG up s k₀ κ
    ((allTimeEquiv LG.garden hG).symm τ)).symm.trans
      (congrArg (kernelAllIntegrand L γ δ F LG up s k₀ κ)
        ((allTimeEquiv LG.garden hG).apply_symm_apply τ))

theorem integral_kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, kernelAllIntegrand L γ δ F LG up s k₀ κ τ) =
      (∫ τ, kernelIntegrand L γ δ F LG up s k₀ κ τ) := by
  apply ((measurePreserving_allTimeEquiv LG.garden hG).integral_comp'
    (kernelAllIntegrand L γ δ F LG up s k₀ κ)).symm.trans
  exact integral_congr_ae (Filter.Eventually.of_forall (kernelAllIntegrand_allTimeEquiv L γ δ F LG hG up s k₀ κ))

/-- No convergence premise is needed for this literal summand identity. -/
theorem kernelK_eq_tsum_integral_all {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F LG up s k₀ nroot nfl =
      (coupling d L γ δ : ℂ)^LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, ∫ τ, kernelAllIntegrand L γ δ F LG up s k₀ κ τ := by
  unfold kernelK
  congr 1
  apply tsum_congr
  intro κ
  exact ((integral_kernelAllIntegrand L γ δ F LG hG up s k₀ κ).trans
    (integral_kernelIntegrand L γ δ F LG up s k₀ κ)).symm

end WaveTurbulence.RegRed
