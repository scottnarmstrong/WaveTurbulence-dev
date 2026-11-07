/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.DecorationShift

/-! # The source coset vectors obey the actual conservation and matching rules -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed

theorem latticePoint_sub {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) :
    latticePoint L (a-b) = latticePoint L a-latticePoint L b := by
  ext j
  simp only [latticePoint,PiLp.sub_apply,Pi.sub_apply,Int.cast_sub,sub_div]

theorem isDecoration_coset {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (hκ : IsDecoration G κ) :
    IsDecoration G (cosetDecoration G L k κ) := by
  constructor
  · intro b
    change k+latticePoint L (κ b.toNode) =
      (k+latticePoint L (κ (b.child 0)))-(k+latticePoint L (κ (b.child 1)))+
        (k+latticePoint L (κ (b.child 2)))
    rw [hκ.1 b,latticePoint_add,latticePoint_sub]
    abel
  · intro ℓ
    exact congrArg (fun n => k+latticePoint L n) (hκ.2 ℓ)

end WaveTurbulence.RegRed
