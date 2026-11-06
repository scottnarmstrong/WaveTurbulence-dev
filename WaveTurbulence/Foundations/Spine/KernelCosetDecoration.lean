/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelCosetPhase
/-! The real coset decoration preserves the exact source Kirchhoff and pairing constraints. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem isDecoration_cosetDecoration {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) :
    IsDecoration G (cosetDecoration G L k z) := by
  constructor
  · intro b
    change k + latticePoint L (z b.toNode) =
      (k + latticePoint L (z (b.child 0))) - (k + latticePoint L (z (b.child 1))) +
        (k + latticePoint L (z (b.child 2)))
    rw [latticePoint_decoration_consistent G L z hz b]
    abel
  · intro l
    change k + latticePoint L (z l.toNode) = k + latticePoint L (z (G.pair l).toNode)
    rw [hz.2 l]

end WaveTurbulence.LGSpine
