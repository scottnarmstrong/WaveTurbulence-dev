/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LinBoundedSpanning
import Mathlib.Tactic
/-! The linear-algebra step of the localization (TARGET L2015–L2024): by `lincomblem` all rung sums
are, up to the errors, bounded combinations of at most `d` of them. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence

theorem loc_alg {d : ℕ} (I : Finset ℕ) (Y0 : ℕ → Mom d) (C : ℕ → ℝ) (ε : ℝ) :
    ∃ (q : ℕ) (r : Fin q → ℕ) (cc : ℕ → Fin q → ℝ) (dd : ℕ → ℝ), q ≤ d ∧ (∀ i, r i ∈ I) ∧
      (∀ j ∈ I, ∀ i, |cc j i| ≤ (2 : ℝ) ^ (d - 1)) ∧
      ∀ (S E : ℕ → ℝ) (ψ : Mom d), (∀ j ∈ I, |E j| ≤ ε) →
        (∀ j ∈ I, S j = inner ℝ ψ (Y0 j) + C j + E j) →
        ∀ j ∈ I, |S j - ∑ i, cc j i * S (r i) - dd j| ≤ (1 + d * (2 : ℝ) ^ (d - 1)) * |ε| := by
  classical
  obtain ⟨q, hq, X, hX, hspan⟩ := WaveTurbulence.LinAlg.exists_bounded_spanning_selection (I.image Y0)
  have hr : ∀ i, ∃ j ∈ I, Y0 j = X i := fun i => by
    have := hX i; simpa [Finset.mem_image] using this
  choose r hrI hrY using hr
  have hc : ∀ j : ℕ, ∃ c : Fin q → ℝ, j ∈ I → ((∀ i, |c i| ≤ (2 : ℝ) ^ (d - 1)) ∧ ∑ i, c i • X i = Y0 j) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨c, h1, h2⟩ := hspan (Y0 j) (Finset.mem_image_of_mem _ hj)
      exact ⟨c, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hj⟩
  choose cc hcc using hc
  refine ⟨q, r, cc, fun j => C j - ∑ i, cc j i * C (r i), hq, hrI, fun j hj i => (hcc j hj).1 i, ?_⟩
  intro S E ψ hE hS j hj
  have hsum : ∑ i, cc j i * S (r i) = inner ℝ ψ (Y0 j) + ∑ i, cc j i * C (r i) + ∑ i, cc j i * E (r i) := by
    have : ∀ i, cc j i * S (r i) = cc j i * inner ℝ ψ (X i) + cc j i * C (r i) + cc j i * E (r i) := by
      intro i; rw [hS (r i) (hrI i), hrY i]; ring
    simp_rw [this, Finset.sum_add_distrib]
    have hY : inner ℝ ψ (Y0 j) = ∑ i, cc j i * inner ℝ ψ (X i) := by
      rw [← (hcc j hj).2, inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [inner_smul_right]
    rw [hY]
  have : S j - ∑ i, cc j i * S (r i) - (C j - ∑ i, cc j i * C (r i)) = E j - ∑ i, cc j i * E (r i) := by
    rw [hsum, hS j hj]; ring
  rw [this]
  calc |E j - ∑ i, cc j i * E (r i)| ≤ |E j| + |∑ i, cc j i * E (r i)| := abs_sub _ _
    _ ≤ |ε| + ∑ i, |cc j i * E (r i)| := by
        exact add_le_add ((hE j hj).trans (le_abs_self ε)) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ |ε| + ∑ _i : Fin q, (2 : ℝ) ^ (d - 1) * |ε| := by
        gcongr with i _
        rw [abs_mul]
        exact mul_le_mul ((hcc j hj).1 i) ((hE _ (hrI i)).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
    _ ≤ (1 + d * (2 : ℝ) ^ (d - 1)) * |ε| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (q : ℝ) ≤ d := by exact_mod_cast hq
        nlinarith [abs_nonneg ε, (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (d - 1)), mul_nonneg (abs_nonneg ε) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (d - 1))]

theorem loc_shift {d q : ℕ} (hq : q ≤ d) (I : Finset ℕ) (r : Fin q → ℕ) (cc : ℕ → Fin q → ℝ)
    (hcc : ∀ j ∈ I, ∀ i, |cc j i| ≤ (2 : ℝ) ^ (d - 1)) (dd : ℕ → ℝ) (ε : ℝ) (S S' : ℕ → ℝ)
    (hS : ∀ j ∈ I, |S' j - ∑ i, cc j i * S' (r i) - dd j| ≤ ε)
    (hsh : ∀ j, |S j - S' j| ≤ 2) (_hr : ∀ i, r i ∈ I) :
    ∀ j ∈ I, |S j - ∑ i, cc j i * S (r i) - dd j| ≤ ε + 2 + 2 * d * (2 : ℝ) ^ (d - 1) := by
  intro j hj
  have h1 : S j - ∑ i, cc j i * S (r i) - dd j =
      (S' j - ∑ i, cc j i * S' (r i) - dd j) + (S j - S' j) - ∑ i, cc j i * (S (r i) - S' (r i)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [h1]
  have h2 : |∑ i, cc j i * (S (r i) - S' (r i))| ≤ q * ((2 : ℝ) ^ (d - 1) * 2) := by
    calc |∑ i, cc j i * (S (r i) - S' (r i))| ≤ ∑ i, |cc j i * (S (r i) - S' (r i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin q, ((2 : ℝ) ^ (d - 1) * 2) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hcc j hj i) (hsh _) (abs_nonneg _) (by positivity)
      _ = q * ((2 : ℝ) ^ (d - 1) * 2) := by simp
  have h3 : (q : ℝ) ≤ d := by exact_mod_cast hq
  calc _ ≤ |(S' j - ∑ i, cc j i * S' (r i) - dd j) + (S j - S' j)| + |∑ i, cc j i * (S (r i) - S' (r i))| :=
        abs_sub _ _
    _ ≤ (|S' j - ∑ i, cc j i * S' (r i) - dd j| + |S j - S' j|) + q * ((2 : ℝ) ^ (d - 1) * 2) :=
        add_le_add (abs_add_le _ _) h2
    _ ≤ (ε + 2) + d * ((2 : ℝ) ^ (d - 1) * 2) :=
        add_le_add (add_le_add (hS j hj) (hsh j)) (mul_le_mul_of_nonneg_right h3 (by positivity))
    _ = _ := by ring

end WaveTurbulence.Ladder
