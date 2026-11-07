/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# CLASSCOUNT: counting arc multisets by classes of bonds

An arc multiset on the labels `Fin n` is the sum of three parts: a *near* part supported on the pairs `(a, b)`
with `0 < |a - b| ≤ 2` and with multiplicities `≤ 2` (the regular bonds of the maximal ladders, once the ladders
are laid out as intervals), a *unit* part taken from a prescribed family `𝓤` of arc count functions, and at most
`K` further *listed* arcs.  `arcLists n K 𝓤` is the finite set of lists realizing such arc multisets, and
`card_arcLists_le` bounds its size.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

/-- `x = (a, b)` has `a ≠ b` and `|a - b| ≤ 2`. -/
def nearPair (n : ℕ) (x : Fin n × Fin n) : Prop :=
  x.1 ≠ x.2 ∧ (x.1 : ℕ) ≤ x.2 + 2 ∧ (x.2 : ℕ) ≤ x.1 + 2

instance (n : ℕ) : DecidablePred (nearPair n) := fun x => by unfold nearPair; infer_instance

/-- Arc count functions supported on the near pairs with values `< 3`. -/
def nearFns (n : ℕ) : Finset (Fin n × Fin n → ℕ) :=
  Fintype.piFinset (fun x => if nearPair n x then range 3 else {0})

theorem card_near_le (n : ℕ) : (univ.filter (nearPair n)).card ≤ 5 * n := by
  classical
  have h1 : (univ.filter (nearPair n)).card =
      ∑ a : Fin n, ((univ.filter (nearPair n)).filter (fun x => x.1 = a)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => Finset.mem_univ _)]
  rw [h1]
  calc ∑ a : Fin n, ((univ.filter (nearPair n)).filter (fun x => x.1 = a)).card
      ≤ ∑ _a : Fin n, 5 := by
        apply Finset.sum_le_sum
        intro a _
        have : ((univ.filter (nearPair n)).filter (fun x => x.1 = a)).card ≤
            (Finset.Icc ((a : ℕ) - 2) ((a : ℕ) + 2)).card := by
          apply Finset.card_le_card_of_injOn (fun x => (x.2 : ℕ))
          · intro x hx
            have hx := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
            have hx' := (Finset.mem_filter.mp hx.1).2
            simp only [Finset.coe_Icc, Set.mem_Icc]
            obtain ⟨⟨h1, h2, h3⟩, h4⟩ := And.intro hx' hx.2
            subst h4
            omega
          · intro x hx y hy hxy
            have hx := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
            have hy := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
            exact Prod.ext (hx.trans hy.symm) (Fin.ext hxy)
        simp only [Nat.card_Icc] at this
        omega
    _ = 5 * n := by simp [mul_comm]

theorem card_nearFns_le (n : ℕ) : (nearFns n).card ≤ 3 ^ (5 * n) := by
  classical
  unfold nearFns
  rw [Fintype.card_piFinset]
  have : ∀ x : Fin n × Fin n, (if nearPair n x then range 3 else ({0} : Finset ℕ)).card =
      if nearPair n x then 3 else 1 := by
    intro x; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
  exact pow_le_pow_right₀ (by norm_num) (card_near_le n)

/-- The list realizing an arc count function. -/
noncomputable def cntList {n : ℕ} (f : Fin n × Fin n → ℕ) : List (Fin n × Fin n) :=
  (univ : Finset (Fin n × Fin n)).toList.flatMap (fun x => List.replicate (f x) x)

theorem count_cntList {n : ℕ} (f : Fin n × Fin n → ℕ) (x : Fin n × Fin n) :
    (cntList f).count x = f x := by
  classical
  have h1 : (cntList f).count x =
      ((univ : Finset (Fin n × Fin n)).toList.map (fun y => (List.replicate (f y) y).count x)).sum := by
    unfold cntList; rw [List.count_flatMap]; rfl
  rw [h1, Finset.sum_map_toList]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [List.count_replicate]; simp [hy]
  · intro h; exact absurd (Finset.mem_univ x) h


/-- Lists of length at most `K`. -/
def listsLe (n K : ℕ) : Finset (List (Fin n × Fin n)) :=
  (range (K + 1)).biUnion (fun k =>
    (univ : Finset (Fin k → Fin n × Fin n)).image List.ofFn)

theorem mem_listsLe {n K : ℕ} {l : List (Fin n × Fin n)} (h : l.length ≤ K) : l ∈ listsLe n K := by
  unfold listsLe
  refine Finset.mem_biUnion.mpr ⟨l.length, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩

theorem card_listsLe_le (n K : ℕ) : (listsLe n K).card ≤ (K + 1) * (n * n + 1) ^ K := by
  unfold listsLe
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ k ∈ range (K + 1), ((univ : Finset (Fin k → Fin n × Fin n)).image List.ofFn).card
      ≤ ∑ k ∈ range (K + 1), (n * n + 1) ^ K := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod]
        simp only [Fintype.card_fin]
        calc (n * n) ^ k ≤ (n * n + 1) ^ k := Nat.pow_le_pow_left (by omega) k
          _ ≤ (n * n + 1) ^ K := Nat.pow_le_pow_right (by omega) hk'
    _ = (K + 1) * (n * n + 1) ^ K := by simp

/-- The lists realizing "near part + unit part + at most `K` listed arcs". -/
noncomputable def arcLists (n K : ℕ) (𝓤 : Finset (Fin n × Fin n → ℕ)) :
    Finset (List (Fin n × Fin n)) :=
  ((nearFns n ×ˢ 𝓤) ×ˢ listsLe n K).image (fun t => cntList t.1.1 ++ cntList t.1.2 ++ t.2)

theorem card_arcLists_le (n K : ℕ) (𝓤 : Finset (Fin n × Fin n → ℕ)) :
    (arcLists n K 𝓤).card ≤ 3 ^ (5 * n) * 𝓤.card * ((K + 1) * (n * n + 1) ^ K) := by
  unfold arcLists
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_product]
  exact Nat.mul_le_mul (Nat.mul_le_mul (card_nearFns_le n) le_rfl) (card_listsLe_le n K)

/-- **The arc-class decomposition.**  A bond family whose bonds split into near regular bonds (multiplicity
`≤ 2` per arc), unit bonds with arc count function in `𝓤`, and at most `K` further bonds has its arc multiset
realized by a list of `arcLists n K 𝓤`. -/
theorem exists_arcList {B : Type*} [Fintype B] {n K : ℕ} (arc : B → Fin n × Fin n)
    (Rg Un : B → Prop) [DecidablePred Rg] [DecidablePred Un] (𝓤 : Finset (Fin n × Fin n → ℕ))
    (h1 : ∀ b, Rg b → nearPair n (arc b))
    (h2 : ∀ x, (univ.filter (fun b => Rg b ∧ arc b = x)).card ≤ 2)
    (h3 : ∀ b, ¬ (Rg b ∧ Un b))
    (h4 : (fun x => (univ.filter (fun b => Un b ∧ arc b = x)).card) ∈ 𝓤)
    (h5 : (univ.filter (fun b => ¬ Rg b ∧ ¬ Un b)).card ≤ K) :
    ∃ L ∈ arcLists n K 𝓤, ∀ x, (univ.filter (fun b => arc b = x)).card = L.count x := by
  classical
  set f : Fin n × Fin n → ℕ := fun x => (univ.filter (fun b => Rg b ∧ arc b = x)).card with hf
  set u : Fin n × Fin n → ℕ := fun x => (univ.filter (fun b => Un b ∧ arc b = x)).card with hu
  set I : Finset B := univ.filter (fun b => ¬ Rg b ∧ ¬ Un b) with hI
  set lI : List (Fin n × Fin n) := I.toList.map arc with hlI
  have hfm : f ∈ nearFns n := by
    unfold nearFns
    rw [Fintype.mem_piFinset]
    intro x
    by_cases hx : nearPair n x
    · rw [if_pos hx, Finset.mem_range]; have := h2 x; simp only [hf]; omega
    · rw [if_neg hx, Finset.mem_singleton]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      rintro b - ⟨hb, rfl⟩
      exact hx (h1 b hb)
  have hlen : lI.length ≤ K := by rw [hlI, List.length_map, Finset.length_toList]; exact h5
  refine ⟨cntList f ++ cntList u ++ lI, ?_, ?_⟩
  · unfold arcLists
    exact Finset.mem_image.mpr ⟨((f, u), lI), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hfm, h4⟩, mem_listsLe hlen⟩, rfl⟩
  · intro x
    rw [List.count_append, List.count_append, count_cntList, count_cntList]
    have hc : lI.count x = (I.filter (fun b => arc b = x)).card := by
      rw [hlI]
      have : (↑(I.toList.map arc) : Multiset _) = I.val.map arc := by
        rw [← Multiset.map_coe, Finset.coe_toList]
      rw [← Multiset.coe_count, this, Multiset.count_map, Finset.card_def, Finset.filter_val]
      congr 1
      exact Multiset.filter_congr (fun b _ => eq_comm)
    rw [hc]
    simp only [hf, hu]
    rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hI]
      tauto
    · rw [Finset.disjoint_left]
      intro b hb hb'
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hI] at hb hb'
      tauto
    · rw [Finset.disjoint_left]
      intro b hb hb'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
      exact h3 b ⟨hb.1, hb'.1⟩


/-- `x^m ≤ m! 3^x`. -/
theorem pow_le_factorial_mul (x m : ℕ) : x ^ m ≤ m.factorial * 3 ^ x := by
  have h := Real.pow_div_factorial_le_exp (x := (x : ℝ)) (Nat.cast_nonneg x) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have he : Real.exp (x : ℝ) ≤ 3 ^ x := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le x
  have h2 : (x : ℝ) ^ m ≤ m.factorial * 3 ^ x := by
    rw [div_le_iff₀ hf] at h
    calc (x : ℝ) ^ m ≤ Real.exp x * m.factorial := h
      _ ≤ 3 ^ x * m.factorial := mul_le_mul_of_nonneg_right he hf.le
      _ = m.factorial * 3 ^ x := mul_comm _ _
  exact_mod_cast h2

theorem succ_mul_factorial_le (K : ℕ) : (K + 1) * (2 * K).factorial ≤ (3 * K).factorial := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · calc (K + 1) * (2 * K).factorial ≤ (2 * K + 1) * (2 * K).factorial :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (2 * K + 1).factorial := (Nat.factorial_succ _).symm
      _ ≤ (3 * K).factorial := Nat.factorial_le (by omega)

/-- The size of `arcLists`: `≤ 27^n |𝓤| 3 (3K)!`-shape bound. -/
theorem card_arcLists_le' (n K : ℕ) (𝓤 : Finset (Fin n × Fin n → ℕ)) :
    (arcLists n K 𝓤).card ≤ 3 ^ (5 * n) * 3 ^ (n + 1) * 𝓤.card * (3 * K).factorial := by
  refine (card_arcLists_le n K 𝓤).trans ?_
  have h1 : (n * n + 1) ^ K ≤ (n + 1) ^ (2 * K) := by
    calc (n * n + 1) ^ K ≤ ((n + 1) ^ 2) ^ K := Nat.pow_le_pow_left (by nlinarith) K
      _ = (n + 1) ^ (2 * K) := by rw [← pow_mul]
  have h2 := pow_le_factorial_mul (n + 1) (2 * K)
  have h3 := succ_mul_factorial_le K
  calc 3 ^ (5 * n) * 𝓤.card * ((K + 1) * (n * n + 1) ^ K)
      ≤ 3 ^ (5 * n) * 𝓤.card * ((K + 1) * ((2 * K).factorial * 3 ^ (n + 1))) := by
        gcongr; exact h1.trans h2
    _ = 3 ^ (5 * n) * 3 ^ (n + 1) * 𝓤.card * ((K + 1) * (2 * K).factorial) := by ring
    _ ≤ 3 ^ (5 * n) * 3 ^ (n + 1) * 𝓤.card * (3 * K).factorial := by gcongr

end WaveTurbulence.ClassCount
