/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DenseRelationIndices
public import WaveTurbulence.Foundations.Counting.ShortRelationCounting
public import WaveTurbulence.Foundations.Counting.EstcrossBudget
import Mathlib.Tactic

/-!
# Estcross on a fixed dominant-coordinate region

DH23 `basiccount0pre` (2): all short-relation witnesses in the coefficient
sum are discharged from the actual density of the dot-product strip. The
first coordinate is assumed to be a large maximal coordinate here; the final
finite decomposition removes that restriction.
-/

public section

namespace WaveTurbulence.Counting

/-- Dense dot-product strips on the region with a large dominant first
coordinate. The centers of the dense strips and their levels may depend on
`x`, as required by the source's supremum over the ball and level. -/
theorem card_dense_strips_dominant_zero_le {d : ℕ}
    (s : Finset (Fin (d+3) → ℤ)) (c : Fin (d+3) → ℝ)
    {rho theta L : ℝ} (hrho : 0 ≤ rho) (htheta : 1 ≤ theta)
    (hscale : 16*((3:ℝ)^(d+1)*theta) ≤ rho) (hrhoL : rho ≤ L)
    (hbox : ∀ x ∈ s, ∀ i, |(x i:ℝ)-c i| ≤ L)
    (hlarge : ∀ x ∈ s, 2*rho < |(x 0:ℝ)|)
    (hdom : ∀ x ∈ s, ∀ i, |(x i:ℝ)| ≤ |(x 0:ℝ)|)
    (hdense : ∀ x ∈ s,
      ∃ Y : Finset (Fin (d+3) → ℤ), ∃ b : Fin (d+3) → ℝ, ∃ alpha : ℝ,
        (∀ y ∈ Y, ∀ i, |(y i:ℝ)-b i| ≤ L) ∧
        (∀ y ∈ Y, |(∑ i, (x i:ℝ)*(y i:ℝ))-alpha| ≤ rho) ∧
        L^(d+2)/theta ≤ (Y.card:ℝ)) :
    (s.card:ℝ) ≤ 129600*((3:ℝ)^(d+1))^3*L^(d+1)*rho^2*theta^2*(1+Real.log L)^2 := by
  classical
  let A : ℝ := (3:ℝ)^(d+1)*theta
  let M : ℕ := ⌈9*A⌉₊
  have hp3 : 1 ≤ (3:ℝ)^(d+1) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (by norm_num : (1:ℝ) ≤ 3) (d+1)
  have hA : 1 ≤ A := by dsimp only [A]; nlinarith only [hp3,htheta]
  have hbudget : 9*A ≤ (M:ℝ) := Nat.le_ceil _
  have hM : 1 ≤ M := Nat.one_le_ceil_iff.mpr (by linarith only [hA])
  have hMbound : (M:ℝ) ≤ 10*A := by
    have hh := Nat.ceil_lt_add_one (by linarith only [hA] : 0 ≤ 9*A)
    change (M:ℝ) < 9*A+1 at hh
    linarith only [hh,hA]
  have hMrho : (M:ℝ) ≤ rho := by change 16*A ≤ rho at hscale; linarith only [hMbound,hscale,hA]
  have hML : (M:ℝ) ≤ L := hMrho.trans hrhoL
  have hL1 : 1 ≤ L := by
    have hh : 16*A ≤ L := hscale.trans hrhoL
    linarith only [hh,hA]
  have hLbudget : 16*((3:ℝ)^(d+1)*theta) ≤ L := hscale.trans hrhoL
  let t := s.map (latticeSplitThree d).toEmbedding
  let cbase : Fin (d+1) → ℝ := Fin.cons (c 0) (fun i => c i.succ.succ.succ)
  have hc := card_family_with_two_short_relations_le t cbase hM hrho hMrho
    (le_trans zero_le_one hL1)
    (by
      intro p hp i
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hbox x hx 0
      · exact hbox x hx j.succ.succ.succ)
    (by
      intro p hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨Y,b,alpha,hYbox,hYstrip,hYcard⟩ := hdense x hx
      obtain ⟨u,hu,v,hv,hurel,hvrel⟩ := exists_two_relationIndices_of_dense_vector_strip
        Y (fun i => (x i:ℝ)) b hrho htheta hLbudget (hlarge x hx)
        (hdom x hx 1) (hdom x hx 2) hYbox hYstrip hYcard hbudget
      refine ⟨u,hu,v,hv,?_,?_⟩
      · change |(relationFirst u:ℝ)*(x 0:ℝ)+(relationSecond u:ℝ)*(x 1:ℝ)| ≤ 2*rho
        simpa only [mul_comm] using hurel
      · change |(relationFirst v:ℝ)*(x 0:ℝ)+(relationSecond v:ℝ)*(x 2:ℝ)| ≤ 2*rho
        simpa only [mul_comm] using hvrel)
  have hc' : (s.card:ℝ) ≤ 1296*(2*L+1)^(d+1)*rho^2*(M:ℝ)^2*(1+Real.log M)^2 := by
    simpa only [t,Finset.card_map] using hc
  exact hc'.trans (short_relation_count_bound hL1 hM hMbound hML)

end WaveTurbulence.Counting
