/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VdCB.ExponentPair
public import WaveTurbulence.Foundations.NumberTheory.ExponentPairSmoothing
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Applications of the shared VdCB exponent-pair API

Positive character frequencies preserve the actual shared power-profile
predicate. Thus an actual `VdCB.IsExponentPair` gives uniform frequency
bounds and the exact optimized sawtooth exponent on that phase class.
No exponent-pair notion or analytic A/B-closure is defined here. Circle
coverage remains a separate actual family application, never an implicit
assertion that every smooth multiplicative factor is a small perturbation.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Positive scaling preserves VdCB's literal derivative-controlled model,
with the same derivative order and perturbation allowance. -/
theorem hasPowerProfile_const_mul {f : ℝ → ℝ} {N F s t delta : ℝ} {r : ℕ}
    (ht : 0 ≤ t) (hf : VdCB.HasPowerProfile f N F s r delta) :
    VdCB.HasPowerProfile (fun x => t*f x) N (t*F) s r delta := by
  refine ⟨contDiffOn_const.mul hf.1,?_⟩
  intro j hj x hx
  rw [iteratedDerivWithin_const_mul_field]
  have he : t*iteratedDerivWithin (j+1) f (Set.Icc N (2*N)) x-
      (t*F)/N^(j+1)*VdCB.powerDerivativeCoefficient s j*(x/N)^(-s-j) =
      t*(iteratedDerivWithin (j+1) f (Set.Icc N (2*N)) x-
        F/N^(j+1)*VdCB.powerDerivativeCoefficient s j*(x/N)^(-s-j)) := by ring
  rw [he,abs_mul,abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left (hf.2 j hj x hx) ht).trans_eq (by ring)

/-- The shared exponent-pair property gives all positive integer frequency
bounds with constants chosen before the scales, phase and subinterval. -/
theorem exists_frequency_bound_of_isExponentPair {kappa lambda s : ℝ}
    (hp : VdCB.IsExponentPair kappa lambda) (hs : 0 < s) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N F : ℝ) (f : ℝ → ℝ) (a b : ℝ),
        1 ≤ N → N ≤ F → VdCB.HasPowerProfile f N F s r delta →
        N ≤ a → a ≤ b → b ≤ 2*N → ∀ n : ℕ, 0 < n →
          ‖VdCB.exponentialSum (fun x => (n:ℝ)*f x) a b‖ ≤
            (C*(F/N)^kappa*N^lambda)*(n:ℝ)^kappa := by
  obtain ⟨r,hr,delta,hdelta,C,hC,happ⟩ := hp.2 s hs
  refine ⟨r,hr,delta,hdelta,C,hC,?_⟩
  intro N F f a b hN hF hf ha hab hb n hn
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hFp : 0 < F := hNp.trans_le hF
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hFn : N ≤ (n:ℝ)*F := hF.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn1 hFp.le])
  have he := happ N ((n:ℝ)*F) (fun x => (n:ℝ)*f x) a b hN hFn
    (hasPowerProfile_const_mul hn0 hf) ha hab hb
  apply he.trans_eq
  rw [show (n:ℝ)*F/N = (n:ℝ)*(F/N) by ring,
    Real.mul_rpow hn0 (div_nonneg hFp.le hNp.le)]
  ring

/-- The exact sawtooth exponent derived from an actual shared exponent pair
on its shared phase class. This conditional class application is distinct
from any unconditional circle-family theorem. -/
theorem exists_sawtooth_bound_of_isExponentPair {kappa lambda s : ℝ}
    (hp : VdCB.IsExponentPair kappa lambda) (hk : 0 < kappa) (hs : 0 < s) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℝ) (f : ℝ → ℝ) (a b : ℝ),
        1 ≤ Q → VdCB.HasPowerProfile f Q Q s r delta →
        Q ≤ a → a ≤ b → b ≤ 2*Q →
          |∑ n ∈ VdCB.integerInterval a b, sawtooth (f n)| ≤
            (1+2*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*Q^((kappa+lambda)/(1+kappa)) := by
  obtain ⟨r,hr,delta,hdelta,C,hC,happ⟩ := exists_frequency_bound_of_isExponentPair hp hs
  refine ⟨r,hr,delta,hdelta,C,hC,?_⟩
  intro Q f a b hQ hf ha hab hb
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  obtain ⟨_,hkhalf,_,hl1,_⟩ := hp.1
  have hk1 : kappa < 1 := by linarith only [hkhalf]
  have hcard : ((VdCB.integerInterval a b).card:ℝ) ≤ 2*Q :=
    (VdCB.card_integerInterval_le hab).trans (by linarith only [ha,hb,hQ])
  have hfreq : ∀ n : ℕ, 0 < n →
      ‖∑ i ∈ VdCB.integerInterval a b, expPhase ((n:ℝ)*f i)‖ ≤ (C*Q^lambda)*(n:ℝ)^kappa := by
    intro n hn
    have he := happ Q Q f a b hQ le_rfl hf ha hab hb n hn
    simpa only [VdCB.exponentialSum,div_self hQp.ne',Real.one_rpow,mul_one] using he
  have he := abs_sum_sawtooth_le_of_frequency_scale (VdCB.integerInterval a b) (fun n : ℤ => f n)
    hQ hC.le (by norm_num : (0:ℝ) ≤ 2) hk hk1 hl1 hcard hfreq
  simpa only [show (2:ℝ)/2 = 1 by norm_num] using! he

end WaveTurbulence.NumberTheory
