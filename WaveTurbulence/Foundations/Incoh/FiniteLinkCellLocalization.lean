/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumTreeLocalization
public import WaveTurbulence.Foundations.Incoh.HalfCellArrays

/-!
# Exponentially many actual half-width link cells per leaf localization

TARGET Step (2), audit P-2. The node cover and the explicit half-cell index
boxes produce a finite set of active link-cell arrays. All constants are
independent of the root momentum and all leaf localization centers.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Uniform exponential cover of every actual half-width cell meeting a source leaf localization. -/
theorem exists_finite_link_cell_localization (d : ℕ) (hd : 0 < d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n m w : ℕ, ∀ P : MomentumTreeData n m w,
      ∀ k : Mom d, ∀ c : Fin m → Fin d → ℤ,
      ∃ S : Finset ((Fin n × Fin 2) → Fin d → ℤ), (S.card : ℝ) ≤ C₀ ^ n ∧
        ∀ x : Fin n → Fin 2 → Mom d, P.inputCellWeight c k x ≠ 0 →
          ∀ z : (Fin n × Fin 2) → Fin d → ℤ,
            halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S := by
  classical
  obtain ⟨C, hb⟩ := exists_finite_link_localization d hd
  let B : ℝ := ((8 * Real.sqrt d + 3) ^ d)
  let C₀ : ℝ := ((C : ℝ) * B + 1) ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨C₀, by dsimp only [C₀]; positivity, ?_⟩
  intro n m w P k c
  obtain ⟨T, hT, ht⟩ := hb n m w P k c
  let boxes := fun a : Fin n → Fin 2 → Mom d =>
    halfCellArrayCover (fun p : Fin n × Fin 2 => a p.1 p.2) (2 * Real.sqrt d)
  let S := T.biUnion boxes
  have hbox (a : Fin n → Fin 2 → Mom d) : ((boxes a).card : ℝ) ≤ B ^ (2 * n) := by
    have h := card_halfCellArrayCover_le (fun p : Fin n × Fin 2 => a p.1 p.2)
      (show 0 ≤ 2 * Real.sqrt (d : ℝ) by positivity)
    have he : 4 * (2 * Real.sqrt (d : ℝ)) + 3 = 8 * Real.sqrt d + 3 := by ring
    simpa only [boxes, B, he, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h
  refine ⟨S, ?_, ?_⟩
  · have hs : (S.card : ℝ) ≤ ∑ a ∈ T, ((boxes a).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := T) (t := boxes))
    calc
      _ ≤ ∑ _a ∈ T, B ^ (2 * n) := hs.trans (Finset.sum_le_sum (fun a _ => hbox a))
      _ = (T.card : ℝ) * B ^ (2 * n) := by simp
      _ ≤ (C : ℝ) ^ (2 * n) * B ^ (2 * n) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hT) (pow_nonneg hB _)
      _ = ((C : ℝ) * B) ^ (2 * n) := (mul_pow _ _ _).symm
      _ ≤ ((C : ℝ) * B + 1) ^ (2 * n) :=
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg C) hB) (by linarith) _
      _ = C₀ ^ n := by dsimp only [C₀]; rw [pow_mul]
  · intro x hx z hz
    obtain ⟨a, ha, hclose⟩ := ht x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, mem_halfCellArrayCover (fun p => hclose p.1 p.2) hz⟩

end WaveTurbulence.Incoh
