/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.ImprovedSumFiberPower
public import WaveTurbulence.Foundations.CountLemmas.DotStrip
public import WaveTurbulence.Foundations.Counting.FiniteFibers

/-! # The coupled pair count with selector x+y -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The fixed-sum annulus gain combines with the independent strip on the
sum. The source r and all three real centers are unrestricted. -/
theorem card_pair_sum_strip_improved_power_le {d : ℕ}
    (s : Finset ((Fin (d+2) → ℤ) × (Fin (d+2) → ℤ)))
    {L τ A e : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hW : 1 ≤ 2*τ*L^2) (he : e ≤ 1/2) (hWe : 2*τ*L^2 ≤ L^e)
    (a b r : Mom (d+2)) (α β : ℝ) (hr : A ≤ ‖r‖)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
      |inner ℝ r (latticePoint L q.1+latticePoint L q.2)-β| ≤ τ) :
    (s.card : ℝ) ≤ (4*L+1)^(d+1)*(2*((d+2 : ℕ) : ℝ)*τ*L/A+1)*
      ((3^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002))*L^((d : ℝ)+81*(2+e)/244)) := by
  classical
  let f := fun q : (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) => q.1+q.2
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hproj : ((s.image f).card : ℝ) ≤
      (4*L+1)^(d+1)*(2*((d+2 : ℕ) : ℝ)*τ*L/A+1) := by
    have hb := card_dot_strip_ball_norm_le (by omega : 0 < d+2) (s.image f) hLp
      (by norm_num : (0 : ℝ) ≤ 2) hτ hA (a+b) r β hr
      (by
        intro n hn
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
        rw [WeylSums.latticePoint_add_eq]
        have heq : (latticePoint L q.1+latticePoint L q.2)-(a+b) =
            (latticePoint L q.1-a)+(latticePoint L q.2-b) := by abel
        rw [heq]
        have ha : ‖latticePoint L q.1-a‖ ≤ 1 := (hs q hq).1
        have hb : ‖latticePoint L q.2-b‖ ≤ 1 := (hs q hq).2.1
        exact (norm_add_le _ _).trans (by linarith only [ha,hb]))
      (by
        intro n hn
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
        rw [WeylSums.latticePoint_add_eq]
        exact (hs q hq).2.2.2)
    simpa only [show d+2-1 = d+1 by omega,show 2*(L*2)+1 = 4*L+1 by ring] using hb
  have hfib : ∀ u ∈ s.image f,
      (((s.filter (fun q => f q = u)).card) : ℝ) ≤
      (3^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002))*L^((d : ℝ)+81*(2+e)/244) := by
    intro u hu
    apply card_fixed_sum_band_improved_power_le hL hτ hW he hWe a b u α
    intro q hq
    have hh := hs q (mem_filter.mp hq).1
    exact ⟨hh.1,hh.2.1,(mem_filter.mp hq).2,hh.2.2.1⟩
  have hc := Counting.card_le_image_card_mul_of_fiber_le s f hfib
  exact hc.trans (mul_le_mul_of_nonneg_right hproj (by positivity))

end WaveTurbulence.CountLemmas
