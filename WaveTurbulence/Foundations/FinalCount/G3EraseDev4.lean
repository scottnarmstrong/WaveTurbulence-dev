/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev2
/-! **FINALCOUNT-G3: the flux identity and the value counts of an erasure** (R27, research-remtame-i L1).

For a decoration with all bonds at `v` equal to `k`, a component `C` of `M - v` satisfies
`∑_{b ∈ C} c_b = sgnC C • (w + k/L)`.  Hence a pinned `v` has its value `k` determined by `c`; in general `k` lies in a box of
`(⌊2L⌋ + 1)^d` lattice points around `k⁰`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {M : Molecule V D} {v : V}


/-- The lattice points `k` with `‖w + k/L - r‖ ≤ 1` lie in a box of at most `(⌊2L⌋ + 1)^d` points. -/
theorem exists_box {L : ℝ} (hL : 0 < L) (w r : Mom d) :
    ∃ I : Finset (Fin d → ℤ), I.card ≤ (⌊2 * L⌋₊ + 1) ^ d ∧
      ∀ k : Fin d → ℤ, ‖w + latticePoint L k - r‖ ≤ 1 → k ∈ I := by
  let a : Fin d → ℤ := fun i => ⌈L * (r i - w i) - L⌉
  let b : Fin d → ℤ := fun i => ⌊L * (r i - w i) + L⌋
  refine ⟨Fintype.piFinset fun i => Finset.Icc (a i) (b i), ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    calc ∏ i, (Finset.Icc (a i) (b i)).card ≤ ∏ _i : Fin d, (⌊2 * L⌋₊ + 1) := by
          refine Finset.prod_le_prod' fun i _ => ?_
          rw [Int.card_Icc]
          have h1 : (b i : ℝ) ≤ L * (r i - w i) + L := Int.floor_le _
          have h2 : L * (r i - w i) - L ≤ (a i : ℝ) := Int.le_ceil _
          have h3 : ((b i - a i : ℤ) : ℝ) ≤ 2 * L := by push_cast; linarith
          have h4 : b i - a i ≤ ⌊2 * L⌋ := Int.le_floor.2 h3
          have h5 : ⌊2 * L⌋ = (⌊2 * L⌋₊ : ℤ) := (Int.natCast_floor_eq_floor (by linarith)).symm
          omega
      _ = (⌊2 * L⌋₊ + 1) ^ d := by simp
  · intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hi : |(w + latticePoint L k - r) i| ≤ 1 := by
      have := PiLp.norm_apply_le (w + latticePoint L k - r) i
      rw [Real.norm_eq_abs] at this
      exact this.trans hk
    have hi' : (w + latticePoint L k - r) i = w i + (k i : ℝ) / L - r i := by
      simp [latticePoint]
    rw [hi', abs_le] at hi
    have e1 : L * (r i - w i) - L ≤ (k i : ℝ) := by
      have : (k i : ℝ) / L ≥ r i - w i - 1 := by linarith [hi.1]
      rw [ge_iff_le, le_div_iff₀ hL] at this
      nlinarith
    have e2 : (k i : ℝ) ≤ L * (r i - w i) + L := by
      have : (k i : ℝ) / L ≤ r i - w i + 1 := by linarith [hi.2]
      rw [div_le_iff₀ hL] at this
      nlinarith
    exact ⟨Int.ceil_le.2 e1, Int.le_floor.2 e2⟩

end WaveTurbulence.FinalCountG3
