/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.EstcrossDominant
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Exceptional vectors admitting a dense dot-product strip

DH23 `basiccount0pre` (2), `estcross` (TeX L2033–L2051), in every dimension
at least three. The source's balls are enlarged to their coordinate boxes,
so the result below is stronger and uniform in all real centers and levels.
The explicit standing scale convention is `theta >= 1`,
`16 * 3^(D-2) * theta <= rho <= L`. The logarithmic loss is `(1+log L)^2`.
-/

public section

namespace WaveTurbulence.Counting

private theorem two_products_le_product_sums {A B P E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    A*P+B*E ≤ (A+B)*(P+E) := by
  have h₁ := mul_nonneg hA hE
  have h₂ := mul_nonneg hB hP
  nlinarith only [h₁,h₂]

/-- DH23 `estcross`: a finite set of integer vectors in a box of radius `L`
which admit dense dot-product strips is bounded by a small-vector term and
a codimension-two term with two logarithms. Dense-strip centers and levels
are allowed to depend arbitrarily on the vector being counted. -/
theorem card_dense_dot_product_strips_le {d : ℕ}
    (s : Finset (Fin (d+3) → ℤ)) (c : Fin (d+3) → ℝ)
    {rho theta L : ℝ} (hrho : 0 ≤ rho) (htheta : 1 ≤ theta)
    (hscale : 16*((3:ℝ)^(d+1)*theta) ≤ rho) (hrhoL : rho ≤ L)
    (hbox : ∀ x ∈ s, ∀ i, |(x i:ℝ)-c i| ≤ L)
    (hdense : ∀ x ∈ s,
      ∃ Y : Finset (Fin (d+3) → ℤ), ∃ b : Fin (d+3) → ℝ, ∃ alpha : ℝ,
        (∀ y ∈ Y, ∀ i, |(y i:ℝ)-b i| ≤ L) ∧
        (∀ y ∈ Y, |(∑ i, (x i:ℝ)*(y i:ℝ))-alpha| ≤ rho) ∧
        L^(d+2)/theta ≤ (Y.card:ℝ)) :
    (s.card:ℝ) ≤ ((5:ℝ)^(d+3)+(d+3)*129600*((3:ℝ)^(d+1))^3)*
      (rho^(d+3)+L^(d+1)*rho^2*theta^2*(1+Real.log L)^2) := by
  classical
  let small := s.filter (fun x => ∀ i, |(x i:ℝ)| ≤ 2*rho)
  let region := fun j : Fin (d+3) => s.filter (fun x =>
    2*rho < |(x j:ℝ)| ∧ ∀ i, |(x i:ℝ)| ≤ |(x j:ℝ)|)
  let K : ℝ := 129600*((3:ℝ)^(d+1))^3
  let E : ℝ := L^(d+1)*rho^2*theta^2*(1+Real.log L)^2
  have hp3 : 1 ≤ (3:ℝ)^(d+1) := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (by norm_num : (1:ℝ) ≤ 3) (d+1)
  have hA : 1 ≤ (3:ℝ)^(d+1)*theta := by nlinarith only [hp3,htheta]
  have hrho1 : 1 ≤ rho := by linarith only [hscale,hA]
  have hLp : 0 ≤ L := le_trans (le_trans zero_le_one hrho1) hrhoL
  have hsmall : (small.card:ℝ) ≤ (5:ℝ)^(d+3)*rho^(d+3) := by
    have hc := card_le_of_coordinate_bounds small (fun _ => (0:ℝ))
      (show 0 ≤ 2*rho by positivity)
      (by
        intro x hx i
        simpa only [sub_zero] using (Finset.mem_filter.mp hx).2 i)
    have hpow : (2*(2*rho)+1)^(d+3) ≤ (5*rho)^(d+3) :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hrho1]) (d+3)
    exact hc.trans (by simpa only [mul_pow] using hpow)
  have hregion (j : Fin (d+3)) : ((region j).card:ℝ) ≤ K*E := by
    let e : Fin (d+3) ≃ Fin (d+3) := Equiv.swap 0 j
    have he0 : e 0 = j := Equiv.swap_apply_left _ _
    let t := (region j).map (latticePermute e).toEmbedding
    have hc := card_dense_strips_dominant_zero_le t (fun i => c (e i)) hrho htheta hscale hrhoL
      (by
        intro p hp i
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
        exact hbox x (Finset.mem_filter.mp hx).1 (e i))
      (by
        intro p hp
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
        change 2*rho < |(x (e 0):ℝ)|
        rw [he0]
        exact (Finset.mem_filter.mp hx).2.1)
      (by
        intro p hp i
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
        change |(x (e i):ℝ)| ≤ |(x (e 0):ℝ)|
        rw [he0]
        exact (Finset.mem_filter.mp hx).2.2 (e i))
      (by
        intro p hp
        obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
        obtain ⟨Y,b,alpha,hYbox,hYstrip,hYcard⟩ := hdense x (Finset.mem_filter.mp hx).1
        refine ⟨Y.map (latticePermute e).toEmbedding,(fun i => b (e i)),alpha,?_,?_,?_⟩
        · intro q hq i
          obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hq
          exact hYbox y hy (e i)
        · intro q hq
          obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hq
          change |(∑ i, (x (e i):ℝ)*(y (e i):ℝ))-alpha| ≤ rho
          rw [sum_coordinate_mul_permute e (fun i => (x i:ℝ)) y]
          exact hYstrip y hy
        · simpa only [Finset.card_map] using hYcard)
    have hc' : ((region j).card:ℝ) ≤
        129600*((3:ℝ)^(d+1))^3*L^(d+1)*rho^2*theta^2*(1+Real.log L)^2 := by
      simpa only [t,Finset.card_map] using hc
    calc
      _ ≤ 129600*((3:ℝ)^(d+1))^3*L^(d+1)*rho^2*theta^2*(1+Real.log L)^2 := hc'
      _ = _ := by dsimp only [K,E]; ring
  have hcover : s ⊆ small ∪ Finset.univ.biUnion region := by
    intro x hx
    by_cases h : ∀ i, |(x i:ℝ)| ≤ 2*rho
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx,h⟩))
    · push Not at h
      obtain ⟨i,hi⟩ := h
      obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ (fun i : Fin (d+3) => |(x i:ℝ)|)
        Finset.univ_nonempty
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨j,hj,?_⟩))
      exact Finset.mem_filter.mpr ⟨hx,hi.trans_le (hmax i (Finset.mem_univ _)),
        fun k => hmax k (Finset.mem_univ _)⟩
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le small (Finset.univ.biUnion region)
  have hb := Finset.card_biUnion_le (s := Finset.univ) (t := region)
  have hcount : s.card ≤ small.card+∑ j, (region j).card := by omega
  have hcountR : (s.card:ℝ) ≤ (small.card:ℝ)+∑ j, ((region j).card:ℝ) := by exact_mod_cast hcount
  have hregions : (∑ j : Fin (d+3), ((region j).card:ℝ)) ≤ (d+3)*(K*E) := by
    calc
      _ ≤ ∑ _j : Fin (d+3), K*E := Finset.sum_le_sum (fun j _ => hregion j)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  have htot : (s.card:ℝ) ≤ (5:ℝ)^(d+3)*rho^(d+3)+((d+3)*K)*E := by
    calc
      _ ≤ (small.card:ℝ)+∑ j, ((region j).card:ℝ) := hcountR
      _ ≤ (5:ℝ)^(d+3)*rho^(d+3)+(d+3)*(K*E) := add_le_add hsmall hregions
      _ = _ := by ring
  apply htot.trans
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hh := two_products_le_product_sums (by positivity : 0 ≤ (5:ℝ)^(d+3))
    (show 0 ≤ (d+3)*K by positivity) (pow_nonneg hrho (d+3)) hE
  simpa only [K,E,mul_assoc] using hh

end WaveTurbulence.Counting
