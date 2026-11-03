/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DenseStripCount
public import WaveTurbulence.Foundations.CountLemmas.SparseDense
public import WaveTurbulence.Foundations.CountLemmas.IntegerEnergy
public import WaveTurbulence.Foundations.CountLemmas.DotStrip

/-! # Sparse and dense pair fibers for DH23 A.2(1) -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The high-γ pair estimate before choosing the density threshold. Every
fiber and density witness is constructed from the actual source set. -/
theorem card_pair_dense_split_le {d : ℕ}
    (s : Finset ((Fin (d+3) → ℤ) × (Fin (d+3) → ℤ)))
    {L τ R θ : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hR : 0 < R) (hθ : 1 ≤ θ)
    (hscale : 16*((3 : ℝ)^(d+1)*θ) ≤ τ*L^2) (hτL : τ*L^2 ≤ L)
    (a b r : Mom (d+3)) (α β : ℝ) (i : Fin (d+3)) (hi : r i ≠ 0)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      R ≤ ‖latticePoint L q.1‖ ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ τ) :
    (s.card : ℝ) ≤ (2*L+1)^(d+2)*(2*τ*L/|r i|+1)*(L^(d+2)/θ)+
      (2*((5 : ℝ)^(d+3)+(d+3)*129600*((3 : ℝ)^(d+1))^3)*
        L^(d+1)*(τ*L^2)^2*θ^2*(1+Real.log L)^2)*
      ((2*L+1)^(d+2)*(2*((d+3 : ℕ) : ℝ)*τ*L/R+1)) := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hθp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  let X := s.image Prod.fst
  let Y := fun x => (s.filter (fun q => q.1 = x)).image Prod.snd
  let B := L^(d+2)/θ
  let H := X.filter (fun x => B < (((s.filter (fun q => q.1 = x)).card) : ℝ))
  let A := (2*L+1)^(d+2)*(2*((d+3 : ℕ) : ℝ)*τ*L/R+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hYcard (x) : ((Y x).card : ℝ) = (((s.filter (fun q => q.1 = x)).card) : ℝ) := by
    apply congrArg (fun n : ℕ => (n : ℝ))
    apply card_image_of_injOn
    intro q hq p hp he
    exact Prod.ext ((mem_filter.mp hq).2.trans (mem_filter.mp hp).2.symm) he
  have hY (x) (y) (hy : y ∈ Y x) : ∃ q ∈ s, q.1 = x ∧ q.2 = y := by
    obtain ⟨q,hq,he⟩ := mem_image.mp hy
    exact ⟨q,(mem_filter.mp hq).1,(mem_filter.mp hq).2,he⟩
  have hcap : ∀ x ∈ X, (((s.filter (fun q => q.1 = x)).card) : ℝ) ≤ A := by
    intro x hx
    rw [← hYcard x]
    have hxR : R ≤ ‖latticePoint L x‖ := by
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
      exact (hs q hq).2.2.1
    have hb := card_dot_strip_ball_norm_le (by omega : 0 < d+3) (Y x) hLp
      (by norm_num : (0 : ℝ) ≤ 1) hτ hR b (latticePoint L x) α hxR
      (by
        intro y hy
        obtain ⟨q,hq,_,rfl⟩ := hY x y hy
        exact (hs q hq).2.1)
      (by
        intro y hy
        obtain ⟨q,hq,hx,rfl⟩ := hY x y hy
        rw [← hx]
        exact (hs q hq).2.2.2.1)
    simpa only [mul_one,show d+3-1 = d+2 by omega] using hb
  have hproj : (X.card : ℝ) ≤ (2*L+1)^(d+2)*(2*τ*L/|r i|+1) := by
    have hb := card_dot_strip_ball_le X hLp (by norm_num : (0 : ℝ) ≤ 1) hτ a r β i hi
      (by intro x hx; obtain ⟨q,hq,rfl⟩ := mem_image.mp hx; exact (hs q hq).1)
      (by intro x hx; obtain ⟨q,hq,rfl⟩ := mem_image.mp hx; exact (hs q hq).2.2.2.2)
    simpa only [mul_one,show d+3-1 = d+2 by omega] using hb
  have hH := card_dense_strips_codim_two_le H (fun j => L*a j) hL (by positivity) hθ hscale hτL
    (by
      intro x hx j
      obtain ⟨q,hq,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
      simpa only [mul_one] using coordinate_bound_of_ball hLp a q.1 (hs q hq).1 j)
    (by
      intro x hx
      refine ⟨Y x,(fun j => L*b j),L^2*α,?_,?_,?_⟩
      · intro y hy j
        obtain ⟨q,hq,_,rfl⟩ := hY x y hy
        simpa only [mul_one] using coordinate_bound_of_ball hLp b q.2 (hs q hq).2.1 j
      · intro y hy
        obtain ⟨q,hq,hx,rfl⟩ := hY x y hy
        rw [← hx]
        exact integer_dot_band hLp.ne' q.1 q.2 (hs q hq).2.2.2.1
      · rw [hYcard]
        exact (mem_filter.mp hx).2.le)
  have hc := card_le_sparse_add_dense s Prod.fst (B := B) (by dsimp only [B]; positivity) hcap
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_right hproj (by dsimp only [B]; positivity))
    (mul_le_mul_of_nonneg_right hH hA))

end WaveTurbulence.CountLemmas
