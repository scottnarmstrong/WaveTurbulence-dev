/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-! # PROT-OPS: the local lattice outputs of o73 (13.3)-(13.4) are finitely many and `1/L`-separated -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence

namespace WaveTurbulence.Flower.ProtOps

variable {d : ℕ}

theorem coord_le_norm (x : Mom d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

theorem latticePoint_apply (L : ℝ) (n : Fin d → ℤ) (i : Fin d) : latticePoint L n i = (n i : ℝ) / L := rfl

theorem lattice_finset (L : ℝ) (hL : 1 ≤ L) (b₀ c₀ : Mom d) :
    ∃ S : Finset (Mom d),
      (↑S : Set (Mom d)) = {k | ‖k - c₀‖ ≤ 1 ∧ ∃ n : Fin d → ℤ, k = b₀ + latticePoint L n} ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 / L ≤ ‖a - b‖) ∧ (S.card : ℝ) ≤ (3 * L) ^ d := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  classical
  let lo : Fin d → ℤ := fun i => ⌈L * (c₀ i - b₀ i) - L⌉
  let hi : Fin d → ℤ := fun i => ⌊L * (c₀ i - b₀ i) + L⌋
  let Nset : Finset (Fin d → ℤ) := Fintype.piFinset fun i => Finset.Icc (lo i) (hi i)
  let S : Finset (Mom d) :=
    (Nset.filter fun n => ‖b₀ + latticePoint L n - c₀‖ ≤ 1).image fun n => b₀ + latticePoint L n
  refine ⟨S, ?_, ?_, ?_⟩
  · ext k
    simp only [S, Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_ofPred_eq, Nset,
      Fintype.mem_piFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨n, ⟨-, hn⟩, rfl⟩
      exact ⟨hn, n, rfl⟩
    · rintro ⟨hk, n, rfl⟩
      refine ⟨n, ⟨fun i => ?_, hk⟩, rfl⟩
      have h1 := (coord_le_norm (b₀ + latticePoint L n - c₀) i).trans hk
      have h2 : (b₀ + latticePoint L n - c₀) i = b₀ i + (n i : ℝ) / L - c₀ i := by
        simp [latticePoint_apply]
      rw [h2, abs_le] at h1
      obtain ⟨h1a, h1b⟩ := h1
      constructor
      · apply Int.ceil_le.2
        have : (n i : ℝ) / L ≥ c₀ i - b₀ i - 1 := by linarith
        rw [ge_iff_le, le_div_iff₀ hL0] at this
        nlinarith
      · apply Int.le_floor.2
        have : (n i : ℝ) / L ≤ c₀ i - b₀ i + 1 := by linarith
        rw [div_le_iff₀ hL0] at this
        nlinarith
  · intro a ha b hb hab
    simp only [S, Finset.mem_image] at ha hb
    obtain ⟨n, -, rfl⟩ := ha
    obtain ⟨n', -, rfl⟩ := hb
    have hne : n ≠ n' := fun h => hab (by rw [h])
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    refine le_trans ?_ (coord_le_norm _ i)
    have h2 : (b₀ + latticePoint L n - (b₀ + latticePoint L n')) i = ((n i : ℝ) - n' i) / L := by
      simp [latticePoint_apply]; ring
    rw [h2, abs_div, abs_of_pos hL0]
    refine div_le_div_of_nonneg_right ?_ hL0.le
    have : (1 : ℤ) ≤ |n i - n' i| := Int.one_le_abs (sub_ne_zero.2 hi)
    have h3 : (1 : ℝ) ≤ ((|n i - n' i| : ℤ) : ℝ) := by exact_mod_cast this
    simpa [Int.cast_abs] using h3
  · calc (S.card : ℝ) ≤ (Nset.card : ℝ) := by
          exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le _ _))
      _ = ∏ i : Fin d, ((Finset.Icc (lo i) (hi i)).card : ℝ) := by
          simp only [Nset, Fintype.card_piFinset]; push_cast; rfl
      _ ≤ ∏ _i : Fin d, (3 * L) := by
          gcongr with i _
          rw [Int.card_Icc]
          have h1 : (hi i : ℝ) ≤ L * (c₀ i - b₀ i) + L := Int.floor_le _
          have h2 : L * (c₀ i - b₀ i) - L ≤ (lo i : ℝ) := Int.le_ceil _
          rcases le_or_gt (hi i + 1 - lo i) 0 with h | h
          · rw [Int.toNat_of_nonpos h]; push_cast; positivity
          · have : (((hi i + 1 - lo i).toNat : ℤ) : ℝ) = (hi i : ℝ) + 1 - lo i := by
              rw [Int.toNat_of_nonneg h.le]; push_cast; ring
            have h4 : (((hi i + 1 - lo i).toNat : ℕ) : ℝ) = (hi i : ℝ) + 1 - lo i := by
              rw [← this]; rfl
            rw [h4]; nlinarith
      _ = (3 * L) ^ d := by simp

end WaveTurbulence.Flower.ProtOps
