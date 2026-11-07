/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # The degenerate part of the coefficient `ε` (DEGEN-VINE, algebra)

`epsCoef n₁ n₂ n₃` (DH23 (defcoef0)) is `1` off the degenerate set `n₂ ∈ {n₁, n₃}`, `-1` on `n₁ = n₂ = n₃`
and `0` on the rest of the degenerate set.  Hence `ε - 1` is supported on the degenerate set, and for a
product over nodes `∏ ε - 1 = ∑_{S ≠ ∅} ∏_{i ∈ S} (ε_i - 1)`, each term supported where every node of `S`
is degenerate.  Every factor `ε_i - 1` has absolute value at most `2`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence Finset

variable {d : ℕ}

/-- The degenerate indicator: `n₂ ∈ {n₁, n₃}`. -/
def IsDegenerate (n₁ n₂ n₃ : Fin d → ℤ) : Prop := n₂ = n₁ ∨ n₂ = n₃

theorem epsCoef_eq_one_sub (n₁ n₂ n₃ : Fin d → ℤ) :
    epsCoef n₁ n₂ n₃ = 1 - (if n₂ = n₁ then 1 else 0) - (if n₂ = n₃ then 1 else 0) := by
  unfold epsCoef
  by_cases h1 : n₂ = n₁
  · by_cases h3 : n₂ = n₃
    · subst h1; subst h3; simp
    · subst h1; simp [h3]
  · by_cases h3 : n₂ = n₃
    · subst h3; simp [h1]
      exact fun h => h1 h.symm
    · simp [h1, h3]

theorem epsCoef_eq_one_of_not_degenerate {n₁ n₂ n₃ : Fin d → ℤ} (h : ¬ IsDegenerate n₁ n₂ n₃) :
    epsCoef n₁ n₂ n₃ = 1 := by
  unfold IsDegenerate at h
  push Not at h
  unfold epsCoef
  simp [h.1, h.2]

theorem isDegenerate_of_epsCoef_ne_one {n₁ n₂ n₃ : Fin d → ℤ} (h : epsCoef n₁ n₂ n₃ ≠ 1) :
    IsDegenerate n₁ n₂ n₃ := by
  by_contra hc
  exact h (epsCoef_eq_one_of_not_degenerate hc)

theorem epsCoef_ne_one_iff {n₁ n₂ n₃ : Fin d → ℤ} :
    epsCoef n₁ n₂ n₃ ≠ 1 ↔ IsDegenerate n₁ n₂ n₃ := by
  refine ⟨isDegenerate_of_epsCoef_ne_one, fun h h1 => ?_⟩
  unfold IsDegenerate at h
  unfold epsCoef at h1
  split_ifs at h1 with h2 h3
  · rcases h with h | h
    · exact h2.1 h
    · exact h2.2 h
  · norm_num at h1
  · norm_num at h1

theorem abs_epsCoef_sub_one_le (n₁ n₂ n₃ : Fin d → ℤ) : |epsCoef n₁ n₂ n₃ - 1| ≤ 2 := by
  unfold epsCoef
  split_ifs <;> norm_num

/-- On the support of `ε` the value is `±1`. -/
theorem epsCoef_cases (n₁ n₂ n₃ : Fin d → ℤ) :
    epsCoef n₁ n₂ n₃ = 1 ∨ epsCoef n₁ n₂ n₃ = -1 ∨ epsCoef n₁ n₂ n₃ = 0 := by
  unfold epsCoef; split_ifs <;> simp

/-- `ε = -1` exactly on `n₁ = n₂ = n₃`. -/
theorem epsCoef_eq_neg_one_iff {n₁ n₂ n₃ : Fin d → ℤ} :
    epsCoef n₁ n₂ n₃ = -1 ↔ n₁ = n₂ ∧ n₂ = n₃ := by
  unfold epsCoef
  by_cases h : n₂ ≠ n₁ ∧ n₂ ≠ n₃
  · rw [if_pos h]
    constructor
    · intro h1; norm_num at h1
    · intro h1; exact absurd h1.1.symm h.1
  · rw [if_neg h]
    by_cases h' : n₁ = n₂ ∧ n₂ = n₃
    · simp [h']
    · rw [if_neg h']
      constructor
      · intro h1; norm_num at h1
      · intro h1; exact absurd h1 h'

variable {ι : Type*} [Fintype ι]

/-- The node-wise defect `ε_i - 1`. -/
def defect (a b c : ι → Fin d → ℤ) (i : ι) : ℝ := epsCoef (a i) (b i) (c i) - 1

open Classical in
/-- **Defect expansion.** `∏ ε_i - 1 = ∑_{∅ ≠ S} ∏_{i ∈ S} (ε_i - 1)`. -/
theorem prod_eps_sub_one (a b c : ι → Fin d → ℤ) :
    (∏ i, epsCoef (a i) (b i) (c i)) - 1 =
      ∑ S ∈ (univ : Finset ι).powerset.erase ∅, ∏ i ∈ S, defect a b c i := by
  classical
  have h : ∏ i, epsCoef (a i) (b i) (c i) = ∏ i, (1 + defect a b c i) := by
    refine prod_congr rfl fun i _ => ?_
    unfold defect; ring
  rw [h, prod_one_add]
  have h0 : (∅ : Finset ι) ∈ (univ : Finset ι).powerset := empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ h0]
  simp

omit [Fintype ι] in
/-- Each defect term is supported where all its nodes are degenerate. -/
theorem prod_defect_ne_zero {a b c : ι → Fin d → ℤ} {S : Finset ι}
    (h : ∏ i ∈ S, defect a b c i ≠ 0) : ∀ i ∈ S, IsDegenerate (a i) (b i) (c i) := by
  intro i hi
  have hne : defect a b c i ≠ 0 := fun h0 => h (prod_eq_zero hi h0)
  refine isDegenerate_of_epsCoef_ne_one fun h1 => hne ?_
  unfold defect; rw [h1]; ring

omit [Fintype ι] in
theorem abs_prod_defect_le (a b c : ι → Fin d → ℤ) (S : Finset ι) :
    |∏ i ∈ S, defect a b c i| ≤ 2 ^ S.card := by
  rw [abs_prod]
  calc ∏ i ∈ S, |defect a b c i| ≤ ∏ _i ∈ S, (2 : ℝ) := by
        gcongr with i hi
        exact abs_epsCoef_sub_one_le _ _ _
    _ = 2 ^ S.card := by simp

/-- Non-degenerate decorations have `ε`-product `1`. -/
theorem prod_eps_eq_one_of_nondegenerate (a b c : ι → Fin d → ℤ)
    (h : ∀ i, ¬ IsDegenerate (a i) (b i) (c i)) : ∏ i, epsCoef (a i) (b i) (c i) = 1 :=
  prod_eq_one fun i _ => epsCoef_eq_one_of_not_degenerate (h i)

/-- If the `ε`-product is not `1`, some node is degenerate. -/
theorem exists_degenerate_of_prod_ne_one (a b c : ι → Fin d → ℤ)
    (h : ∏ i, epsCoef (a i) (b i) (c i) ≠ 1) : ∃ i, IsDegenerate (a i) (b i) (c i) := by
  by_contra hc
  push Not at hc
  exact h (prod_eps_eq_one_of_nondegenerate a b c hc)

end WaveTurbulence.DegenVine
