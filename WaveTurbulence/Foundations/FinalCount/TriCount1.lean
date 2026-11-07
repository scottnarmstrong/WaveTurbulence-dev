/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriClosed2
public import WaveTurbulence.Foundations.FinalCount.TriLattice
/-! Triangles, part 10 (FINALCOUNT-G2): lattice algebra for the triple count. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} {d : ℕ}

theorem latticePoint_add' (L : ℝ) (a b : Fin d → ℤ) : latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
  ext j; simp [latticePoint, add_div]

theorem latticePoint_zero' (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext j; simp [latticePoint]

theorem latticePoint_injective (L : ℝ) (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro a b h
  funext i
  have := congrArg (fun v : Mom d => v i) h
  simp only [latticePoint] at this
  have h2 : (a i : ℝ) / L = (b i : ℝ) / L := this
  have h3 : (a i : ℝ) = b i := by field_simp at h2; exact h2
  exact_mod_cast h3

theorem triC_eq (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) (j : Fin 3) :
    TriData.triC L w z j = latticePoint L (z j - z (j - 1)) := by
  unfold TriData.triC TriData.triK
  rw [latticePoint_sub]; abel

theorem triK_sub (L : ℝ) (w : Mom d) (z z' : Fin 3 → (Fin d → ℤ)) (j : Fin 3) :
    TriData.triK L w z j - TriData.triK L w z' j = latticePoint L (z j - z' j) := by
  unfold TriData.triK; rw [latticePoint_sub]; abel

/-- Shifting two bond vectors by the same lattice vector changes the energy difference by a linear form. -/
theorem energy_shift (L : ℝ) (w : Mom d) (zi zj zi' zj' u : Fin d → ℤ) (hi : zi = zi' + u) (hj : zj = zj' + u) :
    (‖w + latticePoint L zi‖ ^ 2 - ‖w + latticePoint L zj‖ ^ 2) -
        (‖w + latticePoint L zi'‖ ^ 2 - ‖w + latticePoint L zj'‖ ^ 2) =
      2 * (∑ k, ((zi' k - zj' k : ℤ) : ℝ) * (u k : ℝ)) / L ^ 2 := by
  subst hi hj
  rw [latticePoint_add', latticePoint_add']
  set p := latticePoint L u
  set a := w + latticePoint L zi'
  set b := w + latticePoint L zj'
  have h1 : w + (latticePoint L zi' + p) = a + p := by simp only [a]; abel
  have h2 : w + (latticePoint L zj' + p) = b + p := by simp only [b]; abel
  rw [h1, h2]
  have h3 : a - b = latticePoint L (zi' - zj') := by simp only [a, b, latticePoint_sub]; abel
  have e1 : ‖a + p‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a p + ‖p‖ ^ 2 := norm_add_sq_real a p
  have e2 : ‖b + p‖ ^ 2 = ‖b‖ ^ 2 + 2 * inner ℝ b p + ‖p‖ ^ 2 := norm_add_sq_real b p
  have e3 : inner ℝ a p - inner ℝ b p = (∑ k, ((zi' k - zj' k : ℤ) : ℝ) * (u k : ℝ)) / L ^ 2 := by
    rw [← inner_sub_left, h3, inner_latticePoint]
    simp only [Pi.sub_apply]
  rw [e1, e2, mul_div_assoc, ← e3]
  ring

theorem gapAt_eq (M : Molecule V D) [DecidableEq V] [Fintype D] [DecidableEq D] (T : TriData M) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3) :
    Molecule.gapAt L w κ (T.a j) (T.b j) = latticePoint L (T.triZ κ (j - 1) - T.triZ κ j) := by
  unfold Molecule.gapAt Molecule.kvec
  rw [T.kappa_a κ hκ, latticePoint_sub]
  unfold TriData.triZ; abel

end WaveTurbulence.FinalCount
