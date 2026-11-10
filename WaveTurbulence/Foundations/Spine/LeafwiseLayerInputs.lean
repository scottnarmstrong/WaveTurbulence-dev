/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.XChain.SNormPointwise
/-! The original layer profiles as a literal specialization of the individual-leaf kernel. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def layerProfiles {w d : ℕ} (LG : LayeredGarden w)
    (F : ℕ → Mom d → ℝ) : LeafProfiles w d := fun a =>
  if h : a.2 ∈ (LG.garden.tree a.1).nodes then F (LG.layer ⟨a, h⟩) else fun _ => 0

theorem layerProfiles_leaf {w d : ℕ} (LG : LayeredGarden w)
    (F : ℕ → Mom d → ℝ) (ℓ : GLeaf LG.garden.tree) :
    layerProfiles LG F ℓ.1 = F (LG.layer ℓ.toNode) := by
  simp only [layerProfiles, dite_eq_left (TTree.leaves_subset_nodes _ ℓ.2)]
  exact congrArg (fun a : GNode LG.garden.tree => F (LG.layer a)) (Subtype.ext rfl)

theorem kernelLeaves_layerProfiles {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (F : ℕ → Mom d → ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG (layerProfiles LG F) up s k₀ nroot nfl =
      kernelK L γ δ F LG up s k₀ nroot nfl :=
  kernelLeaves_eq_kernelK L γ δ LG F _ (fun ℓ _ => layerProfiles_leaf LG F ℓ) up s k₀ nroot nfl

end WaveTurbulence.LGSpine
