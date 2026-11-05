/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Scale
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp

/-! # Homogeneity of the leafwise kernels in each leaf profile (RA1-LEAFWISE) -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine Finset

variable {d : ℕ}

theorem kernelLeaves_scale {w : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H H' : LeafProfiles w d)
    (β : Fin w × Path → ℝ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) * kernelLeaves L γ δ LG H' up s k₀ nroot nfl := by
  unfold kernelLeaves
  have hp (κ : GenDecoration LG.garden d nroot nfl) :
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) =
        ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H' ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    rw [h ℓ hℓ]
    push_cast
    rfl
  simp_rw [hp]
  have : ∀ κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        (((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H' ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H' ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) :=
    fun κ => by ring
  simp_rw [this, tsum_mul_left]
  ring

theorem coupleLeaves_scale (L γ δ : ℝ) (LG : LayeredGarden 2) (H H' : LeafProfiles 2 d)
    (β : Fin 2 × Path → ℝ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k) (t s : ℝ) (k : Mom d) :
    coupleLeaves L γ δ LG H t s k =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) * coupleLeaves L γ δ LG H' t s k :=
  kernelLeaves_scale L γ δ LG H H' β h _ _ _ _ _

theorem treeLeaves_scale (L γ δ : ℝ) (LG : LayeredGarden 1) (H H' : LeafProfiles 1 d)
    (β : Fin 1 × Path → ℝ)
    (h : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k) (t s : ℝ) (k : Mom d) :
    treeLeaves L γ δ LG H t s k =
      ((∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 : ℝ) : ℂ) * treeLeaves L γ δ LG H' t s k :=
  kernelLeaves_scale L γ δ LG H H' β h _ _ _ _ _

end WaveTurbulence.RA1Leafwise
