/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSupport
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Exact four-state expansion of the squared source Wick factors

The both-zero value is retained: ε²=1-a_x-a_y+2a_x a_y.
Every nontrivial term fixes zero-coordinate planes, leaving all other
links unmasked. There are at most4^n terms, with coefficients at most2^n.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Links

/-- States are none, left zero, right zero, and both zero. -/
def wickPatternCoefficient (c : Fin 4) : ℂ := if c=0 then 1 else if c=3 then 2 else -1

/-- The exact coordinate planes required by one four-state term. -/
def wickPatternConstraint {d n : ℕ} (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (j : Fin n) (c : Fin 4) : Prop :=
  if c=0 then True else if c=1 then (θ j).1=0 else if c=2 then (θ j).2=0
    else (θ j).1=0 ∧ (θ j).2=0

/-- The actual signed contribution of one state at one link. -/
def wickPatternTerm {d n : ℕ} (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (j : Fin n) (c : Fin 4) : ℂ := by
  classical
  exact if wickPatternConstraint θ j c then wickPatternCoefficient c else 0

/-- The both-zero contribution has coefficient2, since the source squared
factor is one at the intersection of the two zero planes. -/
theorem epsXY_sq_eq_sum_patterns {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (j : Fin n) :
    ((epsXY (θ j).1 (θ j).2^2:ℝ):ℂ) = ∑ c : Fin 4, wickPatternTerm θ j c := by
  by_cases hx : (θ j).1=0 <;> by_cases hy : (θ j).2=0 <;>
    norm_num [epsXY,wickPatternTerm,wickPatternConstraint,wickPatternCoefficient,Fin.sum_univ_succ,hx,hy]

/-- Exact expansion retains every source Wick factor, including its square. -/
theorem prod_epsXY_sq_eq_sum_patterns {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ) =
      ∑ σ : Fin n → Fin 4, ∏ j, wickPatternTerm θ j (σ j) := by
  rw [Complex.ofReal_prod]
  simp_rw [epsXY_sq_eq_sum_patterns]
  exact Fintype.prod_sum _

/-- The actual correction is the sum of all nontrivial zero-plane patterns. -/
theorem wick_difference_inclusion_exclusion {d n : ℕ}
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)-1 =
      ∑ σ ∈ ((univ : Finset (Fin n → Fin 4)).erase 0), ∏ j, wickPatternTerm θ j (σ j) := by
  classical
  rw [prod_epsXY_sq_eq_sum_patterns]
  have he := sum_erase_add (s := (univ : Finset (Fin n → Fin 4)))
    (f := fun σ => ∏ j, wickPatternTerm θ j (σ j)) (a := 0) (by simp)
  have hz : (∏ j : Fin n, wickPatternTerm θ j 0) = 1 := by
    simp [wickPatternTerm,wickPatternConstraint,wickPatternCoefficient]
  simp only [Pi.zero_apply,hz] at he
  rw [← he,add_sub_cancel_right]

/-- The expansion has geometric multiplicity, even before terms vanish. -/
theorem wick_patterns_card_le (n : ℕ) :
    (((univ : Finset (Fin n → Fin 4)).erase 0).card) ≤ 4^n := by
  exact (card_erase_le).trans_eq (by simp)

theorem norm_wickPatternCoefficient_le_two (c : Fin 4) : ‖wickPatternCoefficient c‖ ≤ (2:ℝ) := by
  fin_cases c <;> norm_num [wickPatternCoefficient]

/-- Every source coefficient introduced by the expansion is geometrically bounded. -/
theorem norm_wickPatternCoefficient_prod_le {n : ℕ} (σ : Fin n → Fin 4) :
    ‖∏ j, wickPatternCoefficient (σ j)‖ ≤ (2:ℝ)^n := by
  apply (Finset.norm_prod_le _ _).trans
  calc
    _ ≤ ∏ _j : Fin n, (2:ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => by
      exact norm_wickPatternCoefficient_le_two (σ j))
    _ = _ := by simp

end WaveTurbulence.RegAsymp
