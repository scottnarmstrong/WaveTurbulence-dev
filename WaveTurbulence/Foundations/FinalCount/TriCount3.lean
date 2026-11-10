/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCount2
/-! Triangles, part 12 (FINALCOUNT-G2): the cases of the triple count. Common facts for two decorations of the
same parameter triple. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem encard_le_of_subset_image {α β : Type*} (f : α → β) (s : Finset α) (Z : Set β) (h : Z ⊆ f '' (s : Set α)) :
    Z.encard ≤ (s.card : ℕ∞) := by
  calc Z.encard ≤ (f '' (s : Set α)).encard := Set.encard_le_encard h
    _ ≤ (s : Set α).encard := Set.encard_image_le f _
    _ = s.card := Set.encard_coe_eq_coe_finsetCard s

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem triC_eq_iff (L : ℝ) (hL : L ≠ 0) (w : Mom d) (z z' : Fin 3 → (Fin d → ℤ)) (j : Fin 3) :
    triC L w z j = triC L w z' j ↔ z j - z (j - 1) = z' j - z' (j - 1) := by
  rw [triC_eq, triC_eq]
  exact (latticePoint_injective L hL).eq_iff

theorem box_u (L γ δ : ℝ) (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκ' : κ' ∈ decSet M L γ δ w Adm c β k0) (j : Fin 3) :
    (T.triZ κ j - T.triZ κ' j) ∈ boxF d ⌊2 * L⌋₊ := by
  rw [mem_boxF]
  intro i
  have h1 := hκ.2.1.2 (T.b j)
  have h2 := hκ'.2.1.2 (T.b j)
  have h3 : ‖latticePoint L (T.triZ κ j - T.triZ κ' j)‖ ≤ 2 := by
    rw [← triK_sub]
    have : triK L w (T.triZ κ) j - triK L w (T.triZ κ') j =
        (Molecule.kvec L w κ (T.b j) - k0 (T.b j)) - (Molecule.kvec L w κ' (T.b j) - k0 (T.b j)) := by
      unfold triK Molecule.kvec triZ; abel
    rw [this]
    calc _ ≤ ‖Molecule.kvec L w κ (T.b j) - k0 (T.b j)‖ + ‖Molecule.kvec L w κ' (T.b j) - k0 (T.b j)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  have h4 : ‖(latticePoint L (T.triZ κ j - T.triZ κ' j)) i‖ ≤ 2 :=
    (PiLp.norm_apply_le _ i).trans h3
  have h5 : (latticePoint L (T.triZ κ j - T.triZ κ' j)) i = (((T.triZ κ j - T.triZ κ' j) i : ℤ) : ℝ) / L := rfl
  rw [h5, Real.norm_eq_abs, abs_div, abs_of_pos hL, div_le_iff₀ hL] at h4
  have h6 : (|(T.triZ κ j - T.triZ κ' j) i| : ℤ) ≤ ⌊2 * L⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith
  have h7 := Int.natCast_floor_eq_floor (a := 2 * L) (by linarith)
  rw [h7]; exact h6

theorem gap_ne_zero {L : ℝ} (hL : L ≠ 0) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3)
    (h : Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0) : T.triZ κ (j - 1) - T.triZ κ j ≠ 0 := by
  intro e
  apply h
  rw [gapAt_eq M T L w κ hκ, e, latticePoint_zero']

/-- The energy relation in the form used for slabs. -/
theorem slab_of_energy (L : ℝ) (hL : 0 < L) (w : Mom d) (zi zj zi' zj' u : Fin d → ℤ) (hi : zi = zi' + u) (hj : zj = zj' + u)
    (R : ℝ) (hR : |(‖w + latticePoint L zi‖ ^ 2 - ‖w + latticePoint L zj‖ ^ 2) -
        (‖w + latticePoint L zi'‖ ^ 2 - ‖w + latticePoint L zj'‖ ^ 2)| ≤ 2 * (R / L ^ 2)) :
    |∑ k, (((zi' - zj' : Fin d → ℤ) k : ℤ) : ℝ) * (u k : ℝ)| ≤ R := by
  rw [energy_shift L w zi zj zi' zj' u hi hj] at hR
  have hL2 : 0 < L ^ 2 := by positivity
  have e : 2 * (∑ k, ((zi' k - zj' k : ℤ) : ℝ) * (u k : ℝ)) / L ^ 2 =
      2 * ((∑ k, (((zi' - zj' : Fin d → ℤ) k : ℤ) : ℝ) * (u k : ℝ)) / L ^ 2) := by
    simp only [Pi.sub_apply]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_div, abs_of_pos hL2] at hR
  have := (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp hR
  rw [div_le_div_iff_of_pos_right hL2] at this
  exact this

end TriData
end WaveTurbulence.FinalCount
