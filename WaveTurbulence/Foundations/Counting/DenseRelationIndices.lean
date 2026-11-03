/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DenseVectorStrip
public import WaveTurbulence.Foundations.Counting.RelationIndices
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-!
# Actual short-relation indices from strip density

The density argument is connected to the finite coefficient sum in `estcross`.
A coordinate permutation gives the second independent relation. The integer
coefficient budget is a subdivision parameter, chosen explicitly at the source
estimate, rather than an unproved relation hypothesis.
-/

public section

namespace WaveTurbulence.Counting

/-- The first two coordinates of a dense strip supply an actual finite
relation index within any budget dominating the proved coefficient bound. -/
theorem exists_relationIndex_of_dense_vector_strip {d M : ℕ}
    (s : Finset (Fin (d+2) → ℤ)) (x c : Fin (d+2) → ℝ)
    {alpha rho theta L : ℝ}
    (hrho : 0 ≤ rho) (htheta : 1 ≤ theta) (hL : 16*((3:ℝ)^d*theta) ≤ L)
    (ha : 2*rho < |x 0|) (hb : |x 1| ≤ |x 0|)
    (hbox : ∀ n ∈ s, ∀ i, |(n i:ℝ)-c i| ≤ L)
    (hstrip : ∀ n ∈ s, |(∑ i, x i*(n i:ℝ))-alpha| ≤ rho)
    (hdense : L^(d+1)/theta ≤ (s.card:ℝ))
    (hbudget : 9*((3:ℝ)^d*theta) ≤ (M:ℝ)) :
    ∃ w ∈ relationIndices M, |x 0*(relationFirst w:ℝ)+x 1*(relationSecond w:ℝ)| ≤ 2*rho := by
  obtain ⟨m,n,hn,hnabs,hmabs,hrel⟩ := exists_small_relation_of_dense_vector_strip
    s x c hrho htheta hL ha hb hbox hstrip hdense
  have htheta0 : 0 ≤ (3:ℝ)^d*theta := by positivity
  obtain ⟨w,hw,hfirst,hsecond⟩ := exists_mem_relationIndices_of_real_bounds m n hn
    (hmabs.trans hbudget) (hnabs.trans (by linarith only [hbudget,htheta0]))
  refine ⟨w,hw,?_⟩
  rw [hfirst,hsecond]
  exact hrel

/-- The two independent coordinate pairs `(0,1)` and `(0,2)` supply the two
actual relation indices required by the proved weighted counting bound. -/
theorem exists_two_relationIndices_of_dense_vector_strip {d M : ℕ}
    (s : Finset (Fin (d+3) → ℤ)) (x c : Fin (d+3) → ℝ)
    {alpha rho theta L : ℝ}
    (hrho : 0 ≤ rho) (htheta : 1 ≤ theta) (hL : 16*((3:ℝ)^(d+1)*theta) ≤ L)
    (ha : 2*rho < |x 0|) (hb : |x 1| ≤ |x 0|) (hc : |x 2| ≤ |x 0|)
    (hbox : ∀ n ∈ s, ∀ i, |(n i:ℝ)-c i| ≤ L)
    (hstrip : ∀ n ∈ s, |(∑ i, x i*(n i:ℝ))-alpha| ≤ rho)
    (hdense : L^(d+2)/theta ≤ (s.card:ℝ))
    (hbudget : 9*((3:ℝ)^(d+1)*theta) ≤ (M:ℝ)) :
    ∃ u ∈ relationIndices M, ∃ v ∈ relationIndices M,
      |x 0*(relationFirst u:ℝ)+x 1*(relationSecond u:ℝ)| ≤ 2*rho ∧
      |x 0*(relationFirst v:ℝ)+x 2*(relationSecond v:ℝ)| ≤ 2*rho := by
  classical
  obtain ⟨u,hu,hurel⟩ := exists_relationIndex_of_dense_vector_strip (d := d+1)
    s x c hrho htheta hL ha hb hbox hstrip hdense hbudget
  let e : Fin (d+3) ≃ Fin (d+3) := Equiv.swap 1 2
  have he0 : e 0 = 0 := by
    norm_num [e,Equiv.swap_apply_def]
    intro hh
    have hv := congrArg (fun i : Fin (d+3) => i.val) hh
    simp only [Fin.coe_ofNat_eq_mod,Nat.zero_mod] at hv
    rw [Nat.mod_eq_of_lt (by omega : 2 < d+3)] at hv
    omega
  have he1 : e 1 = 2 := Equiv.swap_apply_left _ _
  let t := s.map (latticePermute e).toEmbedding
  have hlarge : 2*rho < |(fun i => x (e i)) 0| := by
    change 2*rho < |x (e 0)|
    rw [he0]
    exact ha
  have hdom : |(fun i => x (e i)) 1| ≤ |(fun i => x (e i)) 0| := by
    change |x (e 1)| ≤ |x (e 0)|
    rw [he1,he0]
    exact hc
  obtain ⟨v,hv,hvrel⟩ := exists_relationIndex_of_dense_vector_strip (d := d+1)
    t (fun i => x (e i)) (fun i => c (e i)) hrho htheta hL hlarge hdom
    (by
      intro n hn i
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn
      exact hbox q hq (e i))
    (by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn
      change |(∑ i, x (e i)*(q (e i):ℝ))-alpha| ≤ rho
      rw [sum_coordinate_mul_permute]
      exact hstrip q hq)
    (by simpa only [t,Finset.card_map] using hdense) hbudget
  refine ⟨u,hu,v,hv,hurel,?_⟩
  simpa only [he0,he1] using hvrel

end WaveTurbulence.Counting
