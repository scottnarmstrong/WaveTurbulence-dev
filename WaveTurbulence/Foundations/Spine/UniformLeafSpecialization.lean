/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
/-! A uniform-layer couple is exactly the common-profile specialization of the leafwise kernel. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem coupleLeaves_uniform_eq_KQstar {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (p : ℕ) (hlayer : ∀ a, LG.layer a = p) (F : ℕ → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    coupleLeaves L γ δ LG (fun _ => F p) t s k = KQstar L γ δ F LG t s k := by
  apply kernelLeaves_eq_kernelK
  intro l _
  rw [hlayer]

end WaveTurbulence.LGSpine
