/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimeDegree
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Positive scaling of the literal source leading time factors -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory

private theorem scale_interval_integral (c a b : ℝ) (p : ℕ) (f h : ℝ → ℝ)
    (he : ∀ x, f (c * x) = c ^ p * h x) :
    (∫ x in c * a..c * b, f x) = c ^ (p + 1) * ∫ x in a..b, h x := by
  calc
    _ = c * ∫ x in a..b, f (c * x) := by
      simpa only [smul_eq_mul] using (intervalIntegral.smul_integral_comp_mul_left f c).symm
    _ = c * ∫ x in a..b, c ^ p * h x := by
      congr 1
      exact intervalIntegral.integral_congr fun x _ => he x
    _ = _ := by rw [intervalIntegral.integral_const_mul, pow_succ]; ring

mutual
/-- Simultaneous positive time scaling of the original source couple leading coefficient. -/
theorem couple_JB_scale (c : ℝ) (hc : 0 < c) : ∀ (Q : RegCpl) (t s : ℝ),
    Q.JB 0 (c * t) (c * s) = c ^ coupleTimeDegree Q * Q.JB 0 t s
  | .triv, _, _ => by simp [RegCpl.JB, coupleTimeDegree]
  | .type1 _ a b d, t, s => by
    have hmin : min (c * t) (c * s) = c * min t s := (mul_min_of_nonneg t s hc.le).symm
    simp only [RegCpl.JB, hmin]
    have hI := scale_interval_integral c 0 (min t s)
      (coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree d)
      (fun x => a.JB 0 x x * b.JB 0 x x * d.JB 0 x x)
      (fun x => a.JB 0 x x * b.JB 0 x x * d.JB 0 x x)
      (fun x => by
        rw [couple_JB_scale c hc a x x, couple_JB_scale c hc b x x, couple_JB_scale c hc d x x]
        simp only [pow_add]
        ring)
    simp only [mul_zero] at hI
    rw [hI]
    have hdeg : coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree d + 1 =
        coupleTimeDegree (.type1 0 a b d) := by simp only [coupleTimeDegree]; omega
    simp only [coupleTimeDegree] at hdeg ⊢
    rw [hdeg]
    ring
  | .type2 p m q, t, s => by
    have hi (u : ℝ) :
        m.JBchain 0 0 (c * s) (fun v => q.JB 0 (c * u) v) =
          c ^ (chainTimeDegree m + coupleTimeDegree q) *
            m.JBchain 0 0 s (fun v => q.JB 0 u v) := by
      simpa only [mul_zero] using chain_JB_scale c hc m 0 s
        (fun v => q.JB 0 (c * u) v) (fun v => q.JB 0 u v) (coupleTimeDegree q)
        (fun v => couple_JB_scale c hc q u v)
    have ho := chain_JB_scale c hc p 0 t
      (fun u => m.JBchain 0 0 (c * s) (fun v => q.JB 0 u v))
      (fun u => m.JBchain 0 0 s (fun v => q.JB 0 u v))
      (chainTimeDegree m + coupleTimeDegree q) hi
    simpa only [mul_zero, RegCpl.JB, coupleTimeDegree, Nat.add_assoc] using ho

/-- The source chain scaling identity permits an arbitrary homogeneous continuation. -/
theorem chain_JB_scale (c : ℝ) (hc : 0 < c) : ∀ (X : RegChain) (lo t : ℝ)
    (G H : ℝ → ℝ) (k : ℕ), (∀ u, G (c * u) = c ^ k * H u) →
    X.JBchain 0 (c * lo) (c * t) G =
      c ^ (chainTimeDegree X + k) * X.JBchain 0 lo t H
  | .nil, _, t, G, H, k, hG => by simpa only [RegChain.JBchain, chainTimeDegree, zero_add] using hG t
  | .pair _ r g _ rest, lo, t, G, H, k, hG => by
    simp only [RegChain.JBchain]
    have hI := scale_interval_integral c lo t
      (coupleTimeDegree r + coupleTimeDegree g + (chainTimeDegree rest + k))
      (fun u => r.JB 0 u u * g.JB 0 u u * rest.JBchain 0 (c * lo) u G)
      (fun u => r.JB 0 u u * g.JB 0 u u * rest.JBchain 0 lo u H)
      (fun u => by
        rw [couple_JB_scale c hc r u u, couple_JB_scale c hc g u u,
          chain_JB_scale c hc rest lo u G H k hG]
        simp only [pow_add]
        ring)
    rw [hI]
    congr 2
    simp only [chainTimeDegree]
    omega
end

end WaveTurbulence.RegAsymp
