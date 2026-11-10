/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelCosetPhase
/-! TARGET L2065–2067: the literal garden kernel with individual real profiles at its positive input leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

/-- Raw addresses retain the original leaf identity through code slicing and grafting. Only
addresses of actual positive unmarked leaves are evaluated in kernelLeaves. -/
abbrev LeafProfiles (w d : ℕ) := (Fin w × TTree.Path) → Mom d → ℝ

/-- The exact multilinear extension of defkg0, with the same decoration sum and phase. -/
noncomputable def kernelLeaves {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

noncomputable def coupleLeaves {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeaves L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0

/-- The source estimates are homogeneous in each individual leaf seminorm bound. -/
def LeafwiseControlled {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (B : (Fin w × TTree.Path) → NNReal) : Prop :=
  ∀ ℓ ∈ inputLeaves LG.garden,
    SNormR (40 * d) (40 * d) (H ℓ.1) ≤ ENNReal.ofReal (B ℓ.1 : ℝ)

noncomputable def leafSizeProduct {w : ℕ} (LG : LayeredGarden w)
    (B : (Fin w × TTree.Path) → NNReal) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ)

/-- The ordinary source kernel is the specialization assigning its layer input at every leaf. -/
theorem kernelLeaves_eq_kernelK {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (F : ℕ → Mom d → ℝ) (H : LeafProfiles w d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = F (LG.layer ℓ.toNode))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl = kernelK L γ δ F LG up s k₀ nroot nfl := by
  unfold kernelLeaves kernelK
  congr 1
  apply tsum_congr
  intro κ
  congr 1
  apply prod_congr rfl
  intro ℓ hℓ
  rw [hH ℓ hℓ]

end WaveTurbulence.LGSpine
