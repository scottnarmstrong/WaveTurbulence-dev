/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Bridge
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GluePiece
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.FlowerTop.Port.NonregularGardenGen
public import WaveTurbulence.Foundations.FlowerTop.Port.NonregularCoupleGen
/-! FLOWER-P7: bridge from the six-tree kernel `kernelKgen` (no designated nodes) to LG-SPINE's
`kernelLeaves … layerProfiles` and the base-`k` slice estimates (AMEND-ST3: `garden_estimate_slice_of_gate`,
`couple_estimate_slice_of_gate`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

theorem kernelKgen_eq_kernelLeaves {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (hP : LG.garden.IsPlain) (tt : Fin w → ℝ) (k : Mom d) (n : Fin w → (Fin d → ℤ)) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun x => tt x.1.1) k n 0 =
      LGSpine.kernelLeaves L γ δ LG (LGSpine.layerProfiles LG F) (fun x => tt x.1.1) 0 k n 0 := by
  rw [kernelKgen_noFix L γ δ F LG hP (fun x => tt x.1.1) 0 k n 0, LGSpine.kernelLeaves_layerProfiles]

#check @LGSpine.garden_estimate_slice_of_gate
#check @LGSpine.couple_estimate_slice_of_gate

end WaveTurbulence.FlowerP7
