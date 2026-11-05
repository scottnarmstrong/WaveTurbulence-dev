/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimeDegree
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Geometric pointwise bounds of the actual leading time coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set

mutual
/-- The original couple leading coefficient has a geometric bound on the source square. -/
theorem norm_couple_JB_le : ∀ (Q : RegCpl) (t s : ℝ), t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
    ‖Q.JB 0 t s‖ ≤ (2 : ℝ) ^ coupleTimeDegree Q
  | .triv, _, _, _, _ => by simp [RegCpl.JB, coupleTimeDegree]
  | .type1 _ a b c, t, s, ht, hs => by
    have hm0 : 0 ≤ min t s := le_min ht.1 hs.1
    have hm1 : min t s ≤ 1 := (min_le_left _ _).trans ht.2
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := min t s)
      (C := (2 : ℝ) ^ (coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree c))
      (f := fun u => a.JB 0 u u * b.JB 0 u u * c.JB 0 u u) (fun u hu => by
        rw [uIoc_of_le hm0] at hu
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨(le_of_lt hu.1), hu.2.trans hm1⟩
        rw [norm_mul, norm_mul, pow_add, pow_add]
        exact mul_le_mul (mul_le_mul (norm_couple_JB_le a u u hu' hu')
          (norm_couple_JB_le b u u hu' hu') (norm_nonneg _) (by positivity))
          (norm_couple_JB_le c u u hu' hu') (norm_nonneg _) (by positivity))
    rw [sub_zero] at hI
    have hh : ‖∫ u in (0 : ℝ)..min t s, a.JB 0 u u * b.JB 0 u u * c.JB 0 u u‖ ≤
        (2 : ℝ) ^ (coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree c) := by
      refine hI.trans ?_
      rw [abs_of_nonneg hm0]
      exact mul_le_of_le_one_right (by positivity) hm1
    simp only [RegCpl.JB, norm_mul, Real.norm_ofNat, coupleTimeDegree]
    have he : 1 + coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree c =
        (coupleTimeDegree a + coupleTimeDegree b + coupleTimeDegree c) + 1 := by omega
    rw [he, pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
  | .type2 p m q, t, s, ht, hs => by
    have hi (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) := chain_JB_norm_le m 0 s
      (fun v => q.JB 0 u v) ((2 : ℝ) ^ coupleTimeDegree q) (by positivity)
      ⟨le_rfl, hs.1⟩ hs.2 (fun v hv => norm_couple_JB_le q u v hu hv)
    have ho := chain_JB_norm_le p 0 t
      (fun u => m.JBchain 0 0 s (fun v => q.JB 0 u v))
      ((2 : ℝ) ^ chainTimeDegree m * 2 ^ coupleTimeDegree q) (by positivity)
      ⟨le_rfl, ht.1⟩ ht.2 hi
    simpa only [RegCpl.JB, coupleTimeDegree, pow_add, mul_assoc] using ho

/-- The original chain integrates a bounded continuation with only a geometric order loss. -/
theorem chain_JB_norm_le : ∀ (X : RegChain) (lo t : ℝ) (G : ℝ → ℝ) (B : ℝ), 0 ≤ B →
    lo ∈ Icc (0 : ℝ) t → t ≤ 1 → (∀ u ∈ Icc (0 : ℝ) 1, ‖G u‖ ≤ B) →
    ‖X.JBchain 0 lo t G‖ ≤ (2 : ℝ) ^ chainTimeDegree X * B
  | .nil, lo, t, G, B, _, hlo, ht, hG => by
    simpa only [RegChain.JBchain, chainTimeDegree, pow_zero, one_mul] using hG t ⟨hlo.1.trans hlo.2, ht⟩
  | .pair _ r g _ rest, lo, t, G, B, hB, hlo, ht, hG => by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := lo) (b := t)
      (C := (2 : ℝ) ^ (coupleTimeDegree r + coupleTimeDegree g + chainTimeDegree rest) * B)
      (f := fun u => r.JB 0 u u * g.JB 0 u u * rest.JBchain 0 lo u G) (fun u hu => by
        rw [uIoc_of_le hlo.2] at hu
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hlo.1.trans (le_of_lt hu.1), hu.2.trans ht⟩
        rw [norm_mul, norm_mul, pow_add, pow_add]
        have hb := mul_le_mul (mul_le_mul (norm_couple_JB_le r u u hu' hu')
          (norm_couple_JB_le g u u hu' hu') (norm_nonneg _) (by positivity))
          (chain_JB_norm_le rest lo u G B hB ⟨hlo.1, le_of_lt hu.1⟩ hu'.2 hG)
          (norm_nonneg _) (by positivity)
        exact hb.trans_eq (by ring))
    have hlen : |t - lo| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hlo.2)]; linarith only [ht, hlo.1]
    have hnon : 0 ≤ (2 : ℝ) ^ (coupleTimeDegree r + coupleTimeDegree g + chainTimeDegree rest) * B :=
      mul_nonneg (by positivity) hB
    apply hI.trans
    calc
      _ ≤ (2 : ℝ) ^ (coupleTimeDegree r + coupleTimeDegree g + chainTimeDegree rest) * B :=
        mul_le_of_le_one_right hnon hlen
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by simp only [chainTimeDegree]; omega)) hB
end

end WaveTurbulence.RegAsymp
