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

noncomputable def kernelAllIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ *
    ∏ ℓ ∈ inputLeaves LG.garden,
      (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

end WaveTurbulence.RegRed
