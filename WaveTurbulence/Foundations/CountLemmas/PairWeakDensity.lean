/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairDense
public import WaveTurbulence.Foundations.CountLemmas.PairMajorants
public import WaveTurbulence.Foundations.CountLemmas.PairFiberCap
public import WaveTurbulence.Foundations.CountLemmas.DyadicDensity

/-! # Summing the actual dense-fiber distribution for DH23 A.2(2) -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The dyadic density argument gains one full power of θ compared with a
single crude sparse/dense split. Every witness is an actual source fiber. -/
theorem card_pair_weak_density_le {d : ℕ}
    (s : Finset ((Fin (d+3) → ℤ) × (Fin (d+3) → ℤ)))
    {L τ R θ : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hR : 0 < R) (hθ : 1 ≤ θ)
    (hscale : 16*((3 : ℝ)^(d+1)*(pairFiberCap (d+3)*θ)) ≤ τ*L^2)
    (hτL : τ*L^2 ≤ L) (hτR : τ*L ≤ R)
    (a b r : Mom (d+3)) (α β : ℝ) (i : Fin (d+3)) (hi : r i ≠ 0)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      R ≤ ‖latticePoint L q.1‖ ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ τ) :
    (s.card : ℝ) ≤ 2*((2*L+1)^(d+2)*(2*τ*L/|r i|+1))*(L^(d+2)/θ)+
      4*(densePairConstant (d+3)*L^(d+1)*(τ*L^2)^2*(1+Real.log L)^2)*
        (pairFiberCap (d+3))^2*L^(d+2)*θ := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hθp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  let C := pairFiberCap (d+3)
  have hC : 1 ≤ C := one_le_pairFiberCap _
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let X := s.image Prod.fst
  let Y := fun x => (s.filter (fun q => q.1 = x)).image Prod.snd
  let w := fun x => (((s.filter (fun q => q.1 = x)).card) : ℝ)
  let H := C*L^(d+2)
  let K := densePairConstant (d+3)*L^(d+1)*(τ*L^2)^2*(1+Real.log L)^2
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hK : 0 ≤ K := by dsimp only [K,densePairConstant]; positivity
  have hYcard (x) : ((Y x).card : ℝ) = w x := by
    apply congrArg (fun n : ℕ => (n : ℝ))
    apply card_image_of_injOn
    intro q hq p hp he
    exact Prod.ext ((mem_filter.mp hq).2.trans (mem_filter.mp hp).2.symm) he
  have hY (x y) (hy : y ∈ Y x) : ∃ q ∈ s, q.1 = x ∧ q.2 = y := by
    obtain ⟨q,hq,he⟩ := mem_image.mp hy
    exact ⟨q,(mem_filter.mp hq).1,(mem_filter.mp hq).2,he⟩
  have hcap : ∀ x ∈ X, w x ≤ H := by
    intro x hx
    rw [← hYcard x]
    have hxR : R ≤ ‖latticePoint L x‖ := by
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
      exact (hs q hq).2.2.1
    have hb := card_dot_fiber_cap (by omega : 0 < d+3) (Y x) hL hτ hR hτR b (latticePoint L x) α hxR
      (by intro y hy; obtain ⟨q,hq,_,rfl⟩ := hY x y hy; exact (hs q hq).2.1)
      (by intro y hy; obtain ⟨q,hq,hx,rfl⟩ := hY x y hy; rw [← hx]; exact (hs q hq).2.2.2.1)
    simpa only [show d+3-1 = d+2 by omega] using hb
  obtain ⟨J,hJ,hJnext⟩ := exists_nat_pow_near (one_le_mul_of_one_le_of_one_le hC hθ)
    (by norm_num : (1 : ℝ) < 2)
  have hsmall : H/(2 : ℝ)^J ≤ 2*L^(d+2)/θ := by
    apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ)^J) hθp).mpr
    have hh := mul_le_mul_of_nonneg_right hJnext.le (by positivity : 0 ≤ L^(d+2))
    rw [show (2 : ℝ)^(J+1) = (2 : ℝ)^J*2 by rw [pow_succ]] at hh
    dsimp only [H]
    nlinarith only [hh]
  have hdense : ∀ j < J,
      (((X.filter (fun x => H/(2 : ℝ)^(j+1) < w x ∧ w x ≤ H/(2 : ℝ)^j)).card) : ℝ) ≤ K*((2 : ℝ)^(j+1))^2 := by
    intro j hj
    let t := X.filter (fun x => H/(2 : ℝ)^(j+1) < w x ∧ w x ≤ H/(2 : ℝ)^j)
    have hpow : (2 : ℝ)^(j+1) ≤ C*θ :=
      (pow_le_pow_right₀ (by norm_num) hj).trans hJ
    have hsc : 16*((3 : ℝ)^(d+1)*(2 : ℝ)^(j+1)) ≤ τ*L^2 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (3 : ℝ)^(d+1))) (by norm_num : (0 : ℝ) ≤ 16)).trans hscale
    have hb := card_dense_strips_codim_two_le t (fun k => L*a k) hL (by positivity)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hsc hτL
      (by
        intro x hx k
        obtain ⟨q,hq,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
        simpa only [mul_one] using coordinate_bound_of_ball hLp a q.1 (hs q hq).1 k)
      (by
        intro x hx
        refine ⟨Y x,(fun k => L*b k),L^2*α,?_,?_,?_⟩
        · intro y hy k
          obtain ⟨q,hq,_,rfl⟩ := hY x y hy
          simpa only [mul_one] using coordinate_bound_of_ball hLp b q.2 (hs q hq).2.1 k
        · intro y hy
          obtain ⟨q,hq,hx,rfl⟩ := hY x y hy
          rw [← hx]
          exact integer_dot_band hLp.ne' q.1 q.2 (hs q hq).2.2.2.1
        · rw [hYcard]
          have hh : L^(d+2) ≤ H := by
            dsimp only [H]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ L^(d+2))
          exact (div_le_div_of_nonneg_right hh (by positivity : 0 ≤ (2 : ℝ)^(j+1))).trans (mem_filter.mp hx).2.1.le)
    convert hb using 1
    dsimp only [K,densePairConstant]
    simp only [show d+3-2 = d+1 by omega,Nat.cast_add,Nat.cast_ofNat]
    ring
  have hsum := sum_le_of_dyadic_density_bounds X w hH hK J hcap hdense
  have hcard : (s.card : ℝ) = ∑ x ∈ X, w x := by rw [card_eq_sum_card_image Prod.fst s,Nat.cast_sum]
  rw [← hcard] at hsum
  have hproj : (X.card : ℝ) ≤ (2*L+1)^(d+2)*(2*τ*L/|r i|+1) := by
    have hb := card_dot_strip_ball_le X hLp (by norm_num : (0 : ℝ) ≤ 1) hτ a r β i hi
      (by intro x hx; obtain ⟨q,hq,rfl⟩ := mem_image.mp hx; exact (hs q hq).1)
      (by intro x hx; obtain ⟨q,hq,rfl⟩ := mem_image.mp hx; exact (hs q hq).2.2.2.2)
    simpa only [mul_one,show d+3-1 = d+2 by omega] using hb
  have hlow := mul_le_mul hproj hsmall (by positivity) (by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 4*K*H)
  have hh := hsum.trans (add_le_add hlow hhigh)
  convert hh using 1
  dsimp only [K,H,C]
  ring

end WaveTurbulence.CountLemmas
