/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.NearTerms
public import WaveTurbulence.Foundations.NTSP.FarTerms

/-!
# Near Poisson modes in DH23 Lemma 6.5 (2)

For the frequencies `P_g(s) = Lg + c + s v`, at most one `g` has `|P_g(s)| < L/2`
(`eq_of_norm_lt_half`). The near modes `g ≠ 0`, `|P_g(s)| < L/4` contribute
(`lintegral_nearModes_le`)

  `∫ ∑_{g ≠ 0, |P_g(s)| < L/4} min(⟨s⟩^{-d}, ω(|P_g(s)| - λ√d|s|)) ds
      ≤ C (λ + 1)/L + 1_{|c| > L/2} ∫ ⟨s⟩^{-d} ds`:

when `|s||v| ≤ L/4` the near mode forces `|c| > L/2` (DH23 L1058–L1062); otherwise
`|s| > L/(4√d|v_i|)` for a coordinate `i` with `|v_i| ≥ |v|/√d`, and the one-dimensional measure
estimate `lintegral_near_le` applies to the `i`-th coordinate of `P_g(s)` (DH23 L1063–L1072).
The decomposition of the near modes of a pair `(g, h) ≠ 0` into an `x`-part and a `y`-part is
`tsum_nearPair_le`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.NTSP

variable {d : ℕ}

theorem eq_of_norm_lt_half {L : ℝ} (hL : 0 < L) {c : Mom d} {g g' : Fin d → ℤ}
    (hg : ‖L • intVec g + c‖ < L / 2) (hg' : ‖L • intVec g' + c‖ < L / 2) : g = g' := by
  by_contra hne
  have h1 := one_le_norm_intVec (sub_ne_zero.2 hne)
  have h2 : L • intVec (g - g') = (L • intVec g + c) - (L • intVec g' + c) := by
    rw [intVec_sub, smul_sub]; abel
  have h3 : ‖L • intVec (g - g')‖ < L := by
    rw [h2]
    calc ‖(L • intVec g + c) - (L • intVec g' + c)‖
        ≤ ‖L • intVec g + c‖ + ‖L • intVec g' + c‖ := norm_sub_le _ _
      _ < L / 2 + L / 2 := add_lt_add hg hg'
      _ = L := by ring
  rw [norm_smul, Real.norm_of_nonneg hL.le] at h3
  nlinarith

/-- A sum over a set with at most one element is at most the bound of its terms. -/
theorem tsum_indicator_le_of_unique {ι : Type*} {S : Set ι} {f : ι → ℝ≥0∞} {B : ℝ≥0∞}
    (hS : ∀ i ∈ S, ∀ j ∈ S, i = j) (hB : ∀ i ∈ S, f i ≤ B) :
    ∑' i, S.indicator f i ≤ B := by
  by_cases h : ∃ i, i ∈ S
  · obtain ⟨i, hi⟩ := h
    rw [tsum_eq_single i (fun j hj => Set.indicator_of_notMem (fun hjS => hj (hS j hjS i hi)) _),
      Set.indicator_of_mem hi]
    exact hB i hi
  · simp only [not_exists] at h
    simp [Set.indicator_of_notMem (h _)]

theorem tsum_indicator_one_le {L : ℝ} (hL : 0 < L) (c : Mom d) :
    ∑' g : Fin d → ℤ, {g : Fin d → ℤ | ‖L • intVec g + c‖ < L / 4}.indicator (fun _ => (1 : ℝ≥0∞))
      g ≤ 1 :=
  tsum_indicator_le_of_unique (fun i hi j hj => eq_of_norm_lt_half hL
    (lt_of_lt_of_le (Set.mem_ofPred_eq ▸ hi) (by linarith))
    (lt_of_lt_of_le (Set.mem_ofPred_eq ▸ hj) (by linarith))) (fun _ _ => le_rfl)

/-- The near modes of `P_g(s) = Lg + c + s v`, `g ≠ 0`, `|P_g(s)| < L/4`, integrated in `s`. -/
theorem lintegral_nearModes_le (hd : 3 ≤ d) {N : ℕ} (hN : 4 ≤ N) {L lam : ℝ} (hL : 0 < L)
    (hlam : 0 ≤ lam) (c v : Mom d) :
    ∫⁻ s, ∑' g : Fin d → ℤ,
      {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
        (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
          (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) g ≤
      ENNReal.ofReal (nearConst d * (lam + 1) / L) +
        {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => ENNReal.ofReal (sInt d)) c := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j : Fin d => |v j|)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hv : ‖v‖ ≤ Real.sqrt d * |v i| := by
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (v i)), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ j, ‖v j‖ ^ 2 ≤ ∑ _j : Fin d, |v i| ^ 2 := Finset.sum_le_sum fun j _ => by
          rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hi j) 2
      _ = d * |v i| ^ 2 := by simp
  -- the two majorants
  set X : ℝ → ℝ≥0∞ := fun s =>
    {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => ENNReal.ofReal (((1 + |s|) ^ d)⁻¹)) c
  set Y : ℝ → ℝ≥0∞ := fun s => if v i = 0 then 0 else
    {s : ℝ | L / (4 * Real.sqrt d * |v i|) < |s|}.indicator
    (fun s => ∑' m : ℤ, ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
      (decayW N (|L * m + c i + s * v i| - |s| * (lam * Real.sqrt d))))) s
  have hpt : ∀ s, ∑' g : Fin d → ℤ,
      {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
        (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
          (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) g ≤
      X s + Y s := fun s => by
    refine tsum_indicator_le_of_unique (fun g hg g' hg' => ?_) (fun g hg => ?_)
    · refine eq_of_norm_lt_half hL (c := c + s • v) ?_ ?_
      · rw [← add_assoc]; linarith [hg.2]
      · rw [← add_assoc]; linarith [hg'.2]
    · obtain ⟨hg0, hgs⟩ := hg
      rcases le_or_gt (|s| * ‖v‖) (L / 4) with hsv | hsv
      · -- the shift is large
        have hc : L / 2 < ‖c‖ := by
          have h1 : ‖L • intVec g + c‖ < L / 2 := by
            have := norm_add_le ((L • intVec g + c) + s • v) (-(s • v))
            rw [add_neg_cancel_right, norm_neg, norm_smul, Real.norm_eq_abs] at this
            linarith
          have h2 : L ≤ ‖L • intVec g‖ := by
            rw [norm_smul, Real.norm_of_nonneg hL.le]
            nlinarith [one_le_norm_intVec hg0]
          have h3 := norm_sub_norm_le (L • intVec g) (-c)
          rw [sub_neg_eq_add, norm_neg] at h3
          linarith
        refine le_trans ?_ le_self_add
        simp only [X, Set.indicator_of_mem (show c ∈ {x : Mom d | L / 2 < ‖x‖} from hc)]
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
      · -- the coordinate argument
        have hvi : 0 < |v i| := by
          by_contra h0
          have : ‖v‖ = 0 := le_antisymm (by nlinarith [abs_nonneg (v i)]) (norm_nonneg _)
          rw [this, mul_zero] at hsv
          linarith
        have hsA : L / (4 * Real.sqrt d * |v i|) < |s| := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg s]
        refine le_trans ?_ le_add_self
        simp only [Y, abs_pos.1 hvi, ↓reduceIte, Set.indicator_of_mem (show s ∈
          {s : ℝ | L / (4 * Real.sqrt d * |v i|) < |s|} from hsA)]
        refine le_trans ?_ (ENNReal.le_tsum (g i))
        refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl (decayW_anti N ?_))
        have hcoord : ((L • intVec g + c) + s • v) i = L * (g i : ℝ) + c i + s * v i := by
          simp [intVec_apply]
        have := PiLp.norm_apply_le ((L • intVec g + c) + s • v) i
        rw [hcoord, Real.norm_eq_abs] at this
        linarith
  have hXm : Measurable X := by
    by_cases hc : c ∈ {x : Mom d | L / 2 < ‖x‖}
    · simp only [X, Set.indicator_of_mem hc]
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · simp only [X, Set.indicator_of_notMem hc]
      exact measurable_const
  have hX : ∫⁻ s, X s ≤ {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => ENNReal.ofReal (sInt d)) c := by
    by_cases hc : c ∈ {x : Mom d | L / 2 < ‖x‖}
    · simp only [X, Set.indicator_of_mem hc]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inv_one_add_abs_pow (by omega))
        (Filter.Eventually.of_forall fun s => by positivity), sInt]
    · simp [X, Set.indicator_of_notMem hc]
  have hY : ∫⁻ s, Y s ≤ ENNReal.ofReal (nearConst d * (lam + 1) / L) := by
    by_cases hv0 : v i = 0
    · have hY0 : ∀ s, Y s = 0 := fun s => by simp only [Y, hv0, ↓reduceIte]
      simp [hY0]
    · simp only [Y, hv0, ↓reduceIte]
      exact lintegral_near_le hd hN hL hlam hv0 (c i)
  calc ∫⁻ s, ∑' g : Fin d → ℤ,
        {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + c) + s • v‖ < L / 4}.indicator
          (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
            (decayW N (‖(L • intVec g + c) + s • v‖ - |s| * (lam * Real.sqrt d))))) g
      ≤ ∫⁻ s, (X s + Y s) := lintegral_mono hpt
    _ = (∫⁻ s, X s) + ∫⁻ s, Y s := lintegral_add_left hXm _
    _ ≤ {x : Mom d | L / 2 < ‖x‖}.indicator (fun _ => ENNReal.ofReal (sInt d)) c +
          ENNReal.ofReal (nearConst d * (lam + 1) / L) := add_le_add hX hY
    _ = _ := add_comm _ _

/-- The near modes of a pair `(g, h) ≠ 0` split into an `x`-part and a `y`-part. -/
theorem tsum_nearPair_le {N : ℕ} {L lam s : ℝ} (hL : 0 < L) (a b ξ ζ : Mom d) :
    ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
      {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0 ∧ ‖(L • intVec gh.1 + ξ) + s • b‖ < L / 4 ∧
          ‖(L • intVec gh.2 + ζ) + s • a‖ < L / 4}.indicator
        (fun gh => ENNReal.ofReal
          (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))) gh ≤
      (∑' g : Fin d → ℤ, {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + ξ) + s • b‖ < L / 4}.indicator
        (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
          (decayW N (‖(L • intVec g + ξ) + s • b‖ - |s| * (lam * Real.sqrt d))))) g) +
      ∑' h : Fin d → ℤ, {h : Fin d → ℤ | h ≠ 0 ∧ ‖(L • intVec h + ζ) + s • a‖ < L / 4}.indicator
        (fun h => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
          (decayW N (‖(L • intVec h + ζ) + s • a‖ - |s| * (lam * Real.sqrt d))))) h := by
  set ng : (Fin d → ℤ) → ℝ≥0∞ := fun g =>
    {g : Fin d → ℤ | g ≠ 0 ∧ ‖(L • intVec g + ξ) + s • b‖ < L / 4}.indicator
      (fun g => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
        (decayW N (‖(L • intVec g + ξ) + s • b‖ - |s| * (lam * Real.sqrt d))))) g
  set nh : (Fin d → ℤ) → ℝ≥0∞ := fun h =>
    {h : Fin d → ℤ | h ≠ 0 ∧ ‖(L • intVec h + ζ) + s • a‖ < L / 4}.indicator
      (fun h => ENNReal.ofReal (min (((1 + |s|) ^ d)⁻¹)
        (decayW N (‖(L • intVec h + ζ) + s • a‖ - |s| * (lam * Real.sqrt d))))) h
  set xg : (Fin d → ℤ) → ℝ≥0∞ := fun g =>
    {g : Fin d → ℤ | ‖L • intVec g + (ξ + s • b)‖ < L / 4}.indicator (fun _ => 1) g
  set xh : (Fin d → ℤ) → ℝ≥0∞ := fun h =>
    {h : Fin d → ℤ | ‖L • intVec h + (ζ + s • a)‖ < L / 4}.indicator (fun _ => 1) h
  have hpt : ∀ gh : (Fin d → ℤ) × (Fin d → ℤ),
      {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0 ∧ ‖(L • intVec gh.1 + ξ) + s • b‖ < L / 4 ∧
          ‖(L • intVec gh.2 + ζ) + s • a‖ < L / 4}.indicator
        (fun gh => ENNReal.ofReal
          (termBound d N lam s ((L • intVec gh.1 + ξ) + s • b) ((L • intVec gh.2 + ζ) + s • a))) gh ≤
        ng gh.1 * xh gh.2 + xg gh.1 * nh gh.2 := fun gh => by
    by_cases hgh : gh ∈ {gh : (Fin d → ℤ) × (Fin d → ℤ) | gh ≠ 0 ∧
        ‖(L • intVec gh.1 + ξ) + s • b‖ < L / 4 ∧ ‖(L • intVec gh.2 + ζ) + s • a‖ < L / 4}
    · rw [Set.indicator_of_mem hgh]
      obtain ⟨h0, hP, hQ⟩ := hgh
      have hxg : xg gh.1 = 1 := by
        simp only [xg]; rw [Set.indicator_of_mem]; simp only [Set.mem_ofPred_eq, ← add_assoc]
        exact hP
      have hxh : xh gh.2 = 1 := by
        simp only [xh]; rw [Set.indicator_of_mem]; simp only [Set.mem_ofPred_eq, ← add_assoc]
        exact hQ
      rw [hxg, hxh, mul_one, one_mul]
      by_cases hg0 : gh.1 = 0
      · have hh0 : gh.2 ≠ 0 := fun h => h0 (Prod.ext hg0 h)
        refine le_trans ?_ le_add_self
        simp only [nh]
        rw [Set.indicator_of_mem (show gh.2 ∈ {h : Fin d → ℤ | h ≠ 0 ∧
          ‖(L • intVec h + ζ) + s • a‖ < L / 4} from ⟨hh0, hQ⟩)]
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (min_le_right _ _))
      · refine le_trans ?_ le_self_add
        simp only [ng]
        rw [Set.indicator_of_mem (show gh.1 ∈ {g : Fin d → ℤ | g ≠ 0 ∧
          ‖(L • intVec g + ξ) + s • b‖ < L / 4} from ⟨hg0, hP⟩)]
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (min_le_left _ _))
    · rw [Set.indicator_of_notMem hgh]; exact bot_le
  have hxg1 : ∑' g, xg g ≤ 1 := tsum_indicator_one_le hL (ξ + s • b)
  have hxh1 : ∑' h, xh h ≤ 1 := tsum_indicator_one_le hL (ζ + s • a)
  calc _ ≤ ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), (ng gh.1 * xh gh.2 + xg gh.1 * nh gh.2) :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' g, ng g) * (∑' h, xh h) + (∑' g, xg g) * ∑' h, nh h := by
        rw [ENNReal.tsum_add, ENNReal.tsum_prod (f := fun g h => ng g * xh h),
          ENNReal.tsum_prod (f := fun g h => xg g * nh h)]
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ (∑' g, ng g) * 1 + 1 * ∑' h, nh h := by gcongr
    _ = _ := by rw [mul_one, one_mul]

end WaveTurbulence.NTSP
