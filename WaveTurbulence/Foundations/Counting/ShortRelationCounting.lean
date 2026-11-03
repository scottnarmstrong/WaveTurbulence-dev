/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.SeparableStrips
public import WaveTurbulence.Foundations.Counting.RelationIndices
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# Summing the two short-relation counts

The coefficient-summation step in DH23 `estcross`: each nonzero transverse
coefficient contributes its reciprocal, and the two harmonic sums account
for the logarithmic loss. This generic counting theorem is used only after
the actual short relations have been supplied by the proved density argument.
-/

public section

namespace WaveTurbulence.Counting

/-- A family with two bounded short relations admits the weighted box count.
The hypothesis describes actual integer coefficients and linear inequalities;
this helper is distinct from the source density theorem `estcross`. -/
theorem card_family_with_two_short_relations_le {d : ℕ}
    (s : Finset ((Fin (d+1) → ℤ) × (Fin 2 → ℤ))) (c : Fin (d+1) → ℝ)
    {M : ℕ} {rho L : ℝ} (hM : 1 ≤ M) (hrho : 0 ≤ rho) (hMrho : (M:ℝ) ≤ rho)
    (hL : 0 ≤ L) (hbox : ∀ n ∈ s, ∀ i, |(n.1 i:ℝ)-c i| ≤ L)
    (hrel : ∀ n ∈ s, ∃ u ∈ relationIndices M, ∃ v ∈ relationIndices M,
      |(relationFirst u:ℝ)*(n.1 0:ℝ)+(relationSecond u:ℝ)*(n.2 0:ℝ)| ≤ 2*rho ∧
      |(relationFirst v:ℝ)*(n.1 0:ℝ)+(relationSecond v:ℝ)*(n.2 1:ℝ)| ≤ 2*rho) :
    (s.card:ℝ) ≤ 1296*(2*L+1)^(d+1)*rho^2*(M:ℝ)^2*(1+Real.log M)^2 := by
  classical
  let W := relationIndices M
  let C : ℝ := (2*L+1)^(d+1)
  let weight : (Bool × (ℤ × ℕ)) → ℝ := fun w => 6*rho/|(relationSecond w:ℝ)|
  let family := fun w : (Bool × (ℤ × ℕ)) × (Bool × (ℤ × ℕ)) =>
    s.filter (fun n =>
      |(relationFirst w.1:ℝ)*(n.1 0:ℝ)+(relationSecond w.1:ℝ)*(n.2 0:ℝ)| ≤ 2*rho ∧
      |(relationFirst w.2:ℝ)*(n.1 0:ℝ)+(relationSecond w.2:ℝ)*(n.2 1:ℝ)| ≤ 2*rho)
  have hcover : s ⊆ (W.product W).biUnion family := by
    intro n hn
    obtain ⟨u,hu,v,hv,h₀,h₁⟩ := hrel n hn
    exact Finset.mem_biUnion.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,
      Finset.mem_filter.mpr ⟨hn,h₀,h₁⟩⟩
  have hfiber (w : (Bool × (ℤ × ℕ)) × (Bool × (ℤ × ℕ)))
      (hw : w ∈ W.product W) : ((family w).card:ℝ) ≤ C*(weight w.1*weight w.2) := by
    have hw' := Finset.mem_product.mp hw
    have hu := relationIndices_bounds hw'.1
    have hv := relationIndices_bounds hw'.2
    have ha : (relationSecond w.1:ℝ) ≠ 0 := by exact_mod_cast hu.2.1
    have hb : (relationSecond w.2:ℝ) ≠ 0 := by exact_mod_cast hv.2.1
    have hc := card_separable_strips_le (family w) c
      (fun z => -(relationFirst w.1:ℝ)*(z 0:ℝ))
      (fun z => -(relationFirst w.2:ℝ)*(z 0:ℝ)) ha hb
      (by positivity : 0 ≤ 2*rho)
      (hu.2.2.trans (by linarith only [hMrho,hrho]))
      (hv.2.2.trans (by linarith only [hMrho,hrho])) hL
      (fun n hn => hbox n (Finset.mem_filter.mp hn).1)
      (by
        intro n hn
        have hh := (Finset.mem_filter.mp hn).2.1
        have he : (relationSecond w.1:ℝ)*(n.2 0:ℝ)-(-(relationFirst w.1:ℝ)*(n.1 0:ℝ)) =
            (relationFirst w.1:ℝ)*(n.1 0:ℝ)+(relationSecond w.1:ℝ)*(n.2 0:ℝ) := by ring
        rw [he]
        exact hh)
      (by
        intro n hn
        have hh := (Finset.mem_filter.mp hn).2.2
        have he : (relationSecond w.2:ℝ)*(n.2 1:ℝ)-(-(relationFirst w.2:ℝ)*(n.1 0:ℝ)) =
            (relationFirst w.2:ℝ)*(n.1 0:ℝ)+(relationSecond w.2:ℝ)*(n.2 1:ℝ) := by ring
        rw [he]
        exact hh)
    simpa only [C,weight,show (3:ℝ)*(2*rho) = 6*rho by ring] using hc
  have hnat := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcount : (s.card:ℝ) ≤ ∑ w ∈ W.product W, C*(weight w.1*weight w.2) := by
    have hc : (s.card:ℝ) ≤ ∑ w ∈ W.product W, ((family w).card:ℝ) := by exact_mod_cast hnat
    exact hc.trans (Finset.sum_le_sum hfiber)
  have hprod : (∑ w ∈ W.product W, weight w.1*weight w.2) = (∑ w ∈ W, weight w)^2 := by
    have hp : (∑ w ∈ W.product W, weight w.1*weight w.2) =
        ∑ u ∈ W, ∑ v ∈ W, weight u*weight v := by
      simpa only using! Finset.sum_product W W (fun w => weight w.1*weight w.2)
    rw [hp]
    simpa only [pow_two] using! (Finset.sum_mul_sum W W weight weight).symm
  have hsum : (∑ w ∈ W.product W, C*(weight w.1*weight w.2)) = C*(∑ w ∈ W, weight w)^2 := by
    rw [← Finset.mul_sum,hprod]
  have hweight : (∑ w ∈ W, weight w) = 6*rho*(∑ w ∈ W, 1/|(relationSecond w:ℝ)|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    dsimp only [weight]
    ring
  have hupper : (∑ w ∈ W, weight w) ≤ 6*rho*(6*(M:ℝ)*(1+Real.log M)) := by
    rw [hweight]
    exact mul_le_mul_of_nonneg_left (sum_relationIndices_inv_abs_le M hM) (by positivity)
  have hnonneg : 0 ≤ ∑ w ∈ W, weight w := Finset.sum_nonneg (fun w _ => by dsimp only [weight]; positivity)
  have hsq := pow_le_pow_left₀ hnonneg hupper 2
  calc
    _ ≤ C*(∑ w ∈ W, weight w)^2 := by rw [← hsum]; exact hcount
    _ ≤ C*(6*rho*(6*(M:ℝ)*(1+Real.log M)))^2 :=
      mul_le_mul_of_nonneg_left hsq (by dsimp only [C]; positivity)
    _ = _ := by dsimp only [C]; ring

end WaveTurbulence.Counting
