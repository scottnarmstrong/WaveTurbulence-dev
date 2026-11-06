/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3b
public import WaveTurbulence.Foundations.Spine.Arith2
import Mathlib.Tactic
/-! `#classes ≤ 4^n`, scale ranges. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem Sigs_card_le (G : Garden w) : (Sigs G).card ≤ 4 ^ G.order := by
  unfold Sigs
  rw [Fintype.card_piFinset]
  have h1 : ∀ S : LQ G, (S.1 ×ˢ S.1).card ≤ 4 ^ S.1.card := by
    intro S
    rw [Finset.card_product]
    have : ∀ k : ℕ, k * k ≤ 4 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
          _ ≤ 4 ^ k + 3 * 4 ^ k := by
              have : 2 * k + 1 ≤ 3 * 4 ^ k := by
                have := Nat.lt_pow_self (by norm_num : 1 < 4) (n := k)
                omega
              omega
          _ = 4 ^ (k + 1) := by ring
    exact this _
  calc ∏ S : LQ G, (S.1 ×ˢ S.1).card ≤ ∏ S : LQ G, 4 ^ S.1.card := Finset.prod_le_prod (fun S _ => h1 S)
    _ = 4 ^ ∑ S : LQ G, S.1.card := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ 4 ^ G.order := by
        apply Nat.pow_le_pow_right (by norm_num)
        have := card_atoms_decomp G
        omega

theorem scale_le_one {D : SplicedKernelData G d} {scales : Finset (GBranch G.tree) → ℝ} {L γ η δ : ℝ}
    {base : Mom d} {roots : Fin w → (Fin d → ℤ)} {π0 : PF G}
    {α : GBranch G.tree → ℝ} (hα : α ∈ clsPF G D scales L γ η δ base roots π0) (S : LQ G) :
    scales S.1 ≤ 1 := by
  obtain ⟨z, _, _, _, h4, _⟩ := hα
  have := (h4 S.1 S.2).1
  rcases this with h | ⟨_, _, h2⟩
  · rw [h]; norm_num
  · exact h2

end WaveTurbulence.Ladder
