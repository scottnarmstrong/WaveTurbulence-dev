/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairSmallBall
public import WaveTurbulence.Foundations.Counting.FiniteFibers

/-! # An elementary coupled-pair estimate before estcross -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The elementary two-strip bound for selector x. Small first vectors are
summed geometrically; large first vectors are sliced in a dominant coordinate. -/
theorem card_pair_coarse_le {d : ℕ} (hd : 3 ≤ d)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ))) {L τ : ℝ}
    (hL : 1 ≤ L) (hτ : 0 ≤ τ) (a b r : Mom d) (α β : ℝ)
    (i : Fin d) (hi : r i ≠ 0)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ τ) :
    (s.card : ℝ) ≤ 15^d*L^d+12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2*
      (2*τ*L/|r i|+1)*(1+τ*L) := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let A := (3^(d-1)*L^(d-1))^2*(2*τ*L/|r i|+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let small := s.filter (fun q => ‖latticePoint L q.1‖ ≤ 1)
  let large := s.filter (fun q => ¬‖latticePoint L q.1‖ ≤ 1)
  have hsmall : (small.card : ℝ) ≤ 15^d*L^d+2*A+2*(A*(4*(d : ℝ)*τ*L)) := by
    have hb := card_pair_small_ball_le hd small hL hτ (by norm_num : (0 : ℝ) < 1)
      (by simpa only [mul_one] using hL) b r α β i hi (by
        intro q hq
        have hh := hs q (mem_filter.mp hq).1
        exact ⟨(mem_filter.mp hq).2,hh.2.1,hh.2.2.1,hh.2.2.2⟩)
    simpa only [one_pow,mul_one] using hb
  have hproj : ((large.image Prod.fst).card : ℝ) ≤
      (2*L+1)^(d-1)*(2*τ*L/|r i|+1) := by
    have hb := card_dot_strip_ball_le (large.image Prod.fst) hLp (by norm_num : (0 : ℝ) ≤ 1)
      hτ a r β i hi (by
        intro x hx
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
        exact (hs q (mem_filter.mp hq).1).1) (by
        intro x hx
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
        exact (hs q (mem_filter.mp hq).1).2.2.2)
    simpa only [mul_one] using hb
  have hfib : ∀ x ∈ large.image Prod.fst,
      (((large.filter (fun q => q.1 = x)).card) : ℝ) ≤
      (2*L+1)^(d-1)*(2*(d : ℝ)*τ*L+1) := by
    intro x hx
    let t := large.filter (fun q => q.1 = x)
    have hinj : Set.InjOn Prod.snd (t : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
      intro q hq p hp he
      exact Prod.ext ((mem_filter.mp hq).2.trans (mem_filter.mp hp).2.symm) he
    have hnorm : 1 ≤ ‖latticePoint L x‖ := by
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
      exact (not_le.mp (mem_filter.mp hq).2).le
    rw [← card_image_of_injOn hinj]
    have hb := card_dot_strip_ball_norm_le (by omega : 0 < d) (t.image Prod.snd) hLp
      (by norm_num : (0 : ℝ) ≤ 1) hτ (by norm_num : (0 : ℝ) < 1) b (latticePoint L x) α hnorm
      (by
        intro y hy
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
        exact (hs q (mem_filter.mp (mem_filter.mp hq).1).1).2.1)
      (by
        intro y hy
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
        rw [← (mem_filter.mp hq).2]
        exact (hs q (mem_filter.mp (mem_filter.mp hq).1).1).2.2.1)
    simpa only [mul_one,div_one] using hb
  have hc := Counting.card_le_image_card_mul_of_fiber_le large Prod.fst hfib
  have hl : (large.card : ℝ) ≤ A*(2*(d : ℝ)*τ*L+1) := by
    have hh := hc.trans (mul_le_mul_of_nonneg_right hproj (by positivity))
    have hbox : (2*L+1)^(d-1) ≤ (3 : ℝ)^(d-1)*L^(d-1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
    have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ (2*L+1)^(d-1)) (by positivity)).mpr hbox
    have hb := mul_le_mul_of_nonneg_right hsquare
      (by positivity : 0 ≤ (2*τ*L/|r i|+1)*(2*(d : ℝ)*τ*L+1))
    apply hh.trans
    convert hb using 1 <;> dsimp only [A] <;> ring
  have he : (small.card : ℝ)+(large.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := s) (fun q => ‖latticePoint L q.1‖ ≤ 1)
  have hT : 0 ≤ τ*L := mul_nonneg hτ hLp.le
  have hdim : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hpoly : 2*A+2*(A*(4*(d : ℝ)*τ*L))+A*(2*(d : ℝ)*τ*L+1) ≤
      12*((d : ℝ)+1)*A*(1+τ*L) := by
    nlinarith only [hA,mul_nonneg hA hT,mul_nonneg (mul_nonneg hA hdim) hT,mul_nonneg hA hdim]
  have hh := add_le_add hsmall hl
  dsimp only [A] at hpoly
  linarith only [hh,he,hpoly]

end WaveTurbulence.CountLemmas
