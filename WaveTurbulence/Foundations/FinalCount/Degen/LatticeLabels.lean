/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # Injectivity of the actual lattice/coset label representation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Degen

/-- Physical momentum equality recovers the integer label when L is nonzero. -/
theorem coset_label_injective {d : ℕ} {L : ℝ} (hL : L ≠ 0) (w : Mom d) :
    Function.Injective (fun n : Fin d → ℤ => w + latticePoint L n) := by
  intro n m h
  have he : latticePoint L n = latticePoint L m := add_left_cancel h
  funext i
  have hi := congrArg (fun x : Mom d => x i) he
  change (n i : ℝ) / L = (m i : ℝ) / L at hi
  have hh := congrArg (fun x : ℝ => x * L) hi
  have hr : (n i : ℝ) = (m i : ℝ) := by simpa only [div_mul_cancel₀ _ hL] using hh
  exact_mod_cast hr

end WaveTurbulence.Degen
