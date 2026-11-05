/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimePolynomial

/-! # Geometric coefficient mass of the actual source tree time polynomial -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp

/-- The coefficient mass of a finite actual source time polynomial. -/
@[expose] def treeTimePolynomialMass (zs : List TreeTimeTerm) : ℝ :=
  (zs.map (fun z => ‖z.coeff‖)).sum

theorem treeTimePolynomialMass_nonneg (zs : List TreeTimeTerm) : 0 ≤ treeTimePolynomialMass zs := by
  exact List.sum_nonneg (fun x hx => by obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)

/-- Every source term has the same actual homogeneous degree. -/
theorem treeTimePolynomial_degree : ∀ (X : RegChain) (z : TreeTimeTerm), z ∈ treeTimePolynomial X →
    z.upperPower + z.lowerPower = chainTimeDegree X
  | .nil, z, hz => by
    simp only [treeTimePolynomial, List.mem_singleton] at hz
    subst z
    rfl
  | .pair _ r g _ rest, z, hz => by
    obtain ⟨q, hq, hz⟩ := List.mem_flatMap.mp hz
    have hd := treeTimePolynomial_degree rest q hq
    simp only [TreeTimeTerm.integrate, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> dsimp only [chainTimeDegree] <;> omega

/-- One exact polynomial integration costs at most twice its scalar coefficient. -/
theorem TreeTimeTerm.integrate_mass_le (p : ℕ) (A : ℝ) (z : TreeTimeTerm) :
    treeTimePolynomialMass (z.integrate p A) ≤ 2 * ‖A‖ * ‖z.coeff‖ := by
  have hd : (1 : ℝ) ≤ (p + z.upperPower + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hh := div_le_self (mul_nonneg (norm_nonneg A) (norm_nonneg z.coeff)) hd
  simp only [treeTimePolynomialMass, TreeTimeTerm.integrate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, norm_neg, norm_div, norm_mul, Real.norm_natCast, add_zero]
  linarith only [hh]

/-- The finite antiderivative transform retains an exact geometric coefficient budget. -/
theorem treeTimePolynomialMass_flatMap_le (zs : List TreeTimeTerm) (p : ℕ) (A : ℝ) :
    treeTimePolynomialMass (zs.flatMap (TreeTimeTerm.integrate p A)) ≤
      2 * ‖A‖ * treeTimePolynomialMass zs := by
  induction zs with
  | nil => simp [treeTimePolynomialMass]
  | cons z zs ih =>
    have hz := z.integrate_mass_le p A
    simp only [List.flatMap_cons, treeTimePolynomialMass, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at hz ih ⊢
    linarith only [hz, ih]

/-- The original source tree polynomial has a geometric coefficient mass, uniformly in its code. -/
theorem treeTimePolynomialMass_le : ∀ X : RegChain,
    treeTimePolynomialMass (treeTimePolynomial X) ≤ (4 : ℝ) ^ chainTimeDegree X
  | .nil => by simp [treeTimePolynomial, treeTimePolynomialMass, chainTimeDegree]
  | .pair _ r g _ rest => by
    let p := coupleTimeDegree r + coupleTimeDegree g
    let A := r.JB 0 1 1 * g.JB 0 1 1
    have hA : ‖A‖ ≤ (2 : ℝ) ^ p := by
      rw [show A = r.JB 0 1 1 * g.JB 0 1 1 from rfl, norm_mul, show p = _ from rfl, pow_add]
      exact mul_le_mul (norm_couple_JB_diagonal_coefficient_le r)
        (norm_couple_JB_diagonal_coefficient_le g) (norm_nonneg _) (by positivity)
    have h2 : (2 : ℝ) * 2 ^ p ≤ 4 ^ (p + 1) := by
      calc
        (2 : ℝ) * 2 ^ p ≤ (4 : ℝ) * 4 ^ p := mul_le_mul
          (by norm_num : (2 : ℝ) ≤ 4)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4) p)
          (by positivity) (by norm_num)
        _ = (4 : ℝ) ^ (p + 1) := by rw [pow_succ]; ring
    apply (treeTimePolynomialMass_flatMap_le (treeTimePolynomial rest) p A).trans
    calc
      _ ≤ (2 * 2 ^ p) * (4 : ℝ) ^ chainTimeDegree rest :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) (treeTimePolynomialMass_le rest)
          (treeTimePolynomialMass_nonneg _) (by positivity)
      _ ≤ (4 : ℝ) ^ (p + 1) * 4 ^ chainTimeDegree rest := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; dsimp only [p, chainTimeDegree]; omega

end WaveTurbulence.RegAsymp
