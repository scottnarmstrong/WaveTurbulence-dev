/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EvalBound
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
public import WaveTurbulence.Foundations.Spine.RootWeightExpansion
/-! AMEND6' (design P*): the root weight `prod_j jbr(r_j)^{2 n}` as a finite sum over choices
`c : Fin w -> Fin n -> Option (Fin d)` of products of squared root coordinates, and the corresponding operation
lists (two root forms `M^{(j)}_i` per chosen coordinate). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem sum_option_sq {d : ℕ} (x : Mom d) :
    (∑ o : Option (Fin d), o.elim (1 : ℝ) (fun i => x i ^ 2)) = 1 + ‖x‖ ^ 2 := by
  rw [Fintype.sum_option, EuclideanSpace.real_norm_sq_eq]
  rfl

theorem jbr_pow_expand {d : ℕ} (x : Mom d) (n : ℕ) :
    jbr x ^ (2 * n) = ∑ c : Fin n → Option (Fin d), ∏ t, (c t).elim (1 : ℝ) (fun i => x i ^ 2) := by
  rw [pow_mul, jbr_sq, ← sum_option_sq x]
  have := Fintype.prod_sum (fun (_t : Fin n) (o : Option (Fin d)) => o.elim (1 : ℝ) (fun i => x i ^ 2))
  simpa using this

theorem prod_jbr_pow_expand {d w : ℕ} (r : Fin w → Mom d) (n : ℕ) :
    ∏ j, jbr (r j) ^ (2 * n) =
      ∑ c : Fin w → Fin n → Option (Fin d), ∏ j, ∏ t, (c j t).elim (1 : ℝ) (fun i => (r j) i ^ 2) := by
  simp_rw [jbr_pow_expand]
  exact Fintype.prod_sum _

/-- The operation list of a choice: two root forms `M^{(j)}_i` for each chosen `(j, t)`. -/
@[expose] def opsOfChoice {d w n : ℕ} (c : Fin w → Fin n → Option (Fin d)) : List (Fin w × Fin d) :=
  (List.finRange w).flatMap fun j => (List.finRange n).flatMap fun t =>
    match c j t with
    | none => []
    | some i => [(j, i), (j, i)]

theorem prod_flatMap_aux {α R : Type*} [CommMonoid R] (l : List α) (g : α → List R) :
    (l.flatMap g).prod = (l.map fun a => (g a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prod_opsOfChoice {d w n : ℕ} {R : Type*} [CommRing R] (c : Fin w → Fin n → Option (Fin d))
    (fv : Fin w → Fin d → R) :
    ((opsOfChoice c).map fun f => fv f.1 f.2).prod =
      ∏ j, ∏ t, (c j t).elim 1 (fun i => fv j i ^ 2) := by
  unfold opsOfChoice
  rw [List.map_flatMap, prod_flatMap_aux, ← Fin.prod_univ_def]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [List.map_flatMap, prod_flatMap_aux]
  rw [← Fin.prod_univ_def]
  refine Finset.prod_congr rfl fun t _ => ?_
  cases c j t <;> simp [sq]

end WaveTurbulence.LGSpine
