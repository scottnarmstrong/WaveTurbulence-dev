/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
public import WaveTurbulence.Foundations.Sumint.WindowRescaleGeneral
/-! # Time geometry of a rung: same layer and different layers (S3b LADDER-DECAY)

A rung sum `f(σ)`, `σ = c (s - t)`, obeys a pointwise majorant `A1 + A2 (1+|σ|)^{-d}` for
`|σ| ≤ Ls`, and an integral bound `A_l` on `Ls ≤ |σ| ≤ W`.  When the two times lie in the same
unit box the time integral costs `c⁻¹ (A2 K + A_l) + A1`; when the boxes are different the extra
distance `m` gains `(1+m)^{-(d-1)}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open MeasureTheory Set

/-- Positive-side tail of the power kernel. -/
theorem integral_inv_pow_pos {d : ℕ} (hd : 3 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ σ in Icc a b, ((1 + |σ|) ^ d)⁻¹) ≤ (1 + a) ^ (-((d : ℝ) - 1)) / ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcongr : (∫ σ in Icc a b, ((1 + |σ|) ^ d)⁻¹) = ∫ σ in a..b, ((1 + σ) ^ d)⁻¹ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
    simp only [abs_of_nonneg (ha.trans hσ.1)]
  rw [hcongr]
  set F : ℝ → ℝ := fun σ => -(((1 + σ) ^ (d - 1))⁻¹) / ((d : ℝ) - 1) with hF
  have hder : ∀ σ ∈ Icc a b, HasDerivAt F (((1 + σ) ^ d)⁻¹) σ := by
    intro σ hσ
    have h1 : 0 < 1 + σ := by linarith [hσ.1]
    have hp : HasDerivAt (fun σ : ℝ => (1 + σ) ^ (d - 1)) (((d - 1 : ℕ) : ℝ) * (1 + σ) ^ (d - 1 - 1)) σ := by
      have := (hasDerivAt_pow (d - 1) (1 + σ)).comp σ ((hasDerivAt_id σ).const_add 1)
      simpa [Function.comp_def] using this
    have hne : (1 + σ) ^ (d - 1) ≠ 0 := (pow_pos h1 _).ne'
    have h2 := (hp.inv hne).neg.div_const ((d : ℝ) - 1)
    refine h2.congr_deriv ?_
    have hd' : (d - 1 : ℕ) = d - 1 + 0 := rfl
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    simp only [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
    push_cast
    have hk : ((k : ℝ) + 2 - 1) = (k : ℝ) + 1 := by ring
    rw [hk]
    field_simp
    ring
  have hint : IntervalIntegrable (fun σ : ℝ => ((1 + σ) ^ d)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) (fun σ hσ => ?_)
    rw [uIcc_of_le hab] at hσ
    exact (pow_pos (by linarith [hσ.1]) _).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ hσ => hder σ (by rwa [uIcc_of_le hab] at hσ)) hint]
  have hFb : 0 ≤ ((1 + b) ^ (d - 1))⁻¹ / ((d : ℝ) - 1) := by
    have : 0 < 1 + b := by linarith
    positivity
  have : (1 + a) ^ (-((d : ℝ) - 1)) = (((1 + a) ^ (d - 1))⁻¹) := by
    rw [Real.rpow_neg (by linarith), show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; simp, Real.rpow_natCast]
  rw [this]
  simp only [hF]
  have e1 : -(((1 + b) ^ (d - 1))⁻¹) / ((d : ℝ) - 1) - -(((1 + a) ^ (d - 1))⁻¹) / ((d : ℝ) - 1)
      = ((1 + a) ^ (d - 1))⁻¹ / ((d : ℝ) - 1) - ((1 + b) ^ (d - 1))⁻¹ / ((d : ℝ) - 1) := by ring
  rw [e1]
  linarith

/-- Negative-side tail, by reflection. -/
theorem integral_inv_pow_neg {d : ℕ} (hd : 3 ≤ d) {a b : ℝ} (hb : b ≤ 0) (hab : a ≤ b) :
    (∫ σ in Icc a b, ((1 + |σ|) ^ d)⁻¹) ≤ (1 + (-b)) ^ (-((d : ℝ) - 1)) / ((d : ℝ) - 1) := by
  have h := integral_inv_pow_pos hd (a := -b) (b := -a) (by linarith) (by linarith)
  refine le_trans (le_of_eq ?_) h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -b ≤ -a),
    ← intervalIntegral.integral_comp_neg]
  simp only [abs_neg]

/-- Tail mass of the power kernel on an interval at distance at least `m ≥ 0` from the origin. -/
theorem integral_inv_pow_le {d : ℕ} (hd : 3 ≤ d) {m α β : ℝ} (hm : 0 ≤ m) (hαβ : α ≤ β)
    (hJ : ∀ σ ∈ Icc α β, m ≤ |σ|) :
    (∫ σ in Icc α β, ((1 + |σ|) ^ d)⁻¹) ≤ 2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hanti : ∀ x : ℝ, m ≤ x → (1 + x) ^ (-((d : ℝ) - 1)) ≤ (1 + m) ^ (-((d : ℝ) - 1)) := by
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hpos : 0 ≤ (1 + m) ^ (-((d : ℝ) - 1)) := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt 0 α with ha | ha
  · have hmα : m ≤ α := by simpa [abs_of_nonneg ha] using hJ α ⟨le_rfl, hαβ⟩
    have := integral_inv_pow_pos hd ha hαβ
    calc _ ≤ _ := this
      _ ≤ (1 + m) ^ (-((d : ℝ) - 1)) / ((d : ℝ) - 1) := by
          exact div_le_div_of_nonneg_right (hanti α hmα) hd1.le
      _ ≤ _ := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
          nlinarith [inv_pos.mpr hd1]
  · rcases le_or_gt β 0 with hb | hb
    · have hmβ : m ≤ -β := by simpa [abs_of_nonpos hb] using hJ β ⟨hαβ, le_rfl⟩
      have := integral_inv_pow_neg hd hb hαβ
      calc _ ≤ _ := this
        _ ≤ (1 + m) ^ (-((d : ℝ) - 1)) / ((d : ℝ) - 1) :=
            div_le_div_of_nonneg_right (hanti (-β) hmβ) hd1.le
        _ ≤ _ := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
            nlinarith [inv_pos.mpr hd1]
    · have hm0 : m = 0 := by
        have := hJ 0 ⟨ha.le, hb.le⟩
        simp at this; linarith
      subst hm0
      have h1 := integral_inv_pow_neg hd (a := α) (b := 0) le_rfl ha.le
      have h2 := integral_inv_pow_pos hd (a := 0) (b := β) le_rfl hb.le
      have hsplit : (∫ σ in Icc α β, ((1 + |σ|) ^ d)⁻¹) =
          (∫ σ in Icc α 0, ((1 + |σ|) ^ d)⁻¹) + ∫ σ in Icc 0 β, ((1 + |σ|) ^ d)⁻¹ := by
        have hc : Continuous (fun σ : ℝ => ((1 + |σ|) ^ d)⁻¹) := by
          refine Continuous.inv₀ (by fun_prop) (fun σ => (pow_pos (by positivity) _).ne')
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le ha.le, ← intervalIntegral.integral_of_le hb.le,
          ← intervalIntegral.integral_of_le hαβ]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
      rw [hsplit]
      simp only [neg_zero, add_zero] at h1 h2 ⊢
      have e1 : (1 : ℝ) ^ (-((d : ℝ) - 1)) = 1 := Real.one_rpow _
      rw [e1] at h1 h2 ⊢
      rw [div_mul_eq_mul_div, mul_one]
      have e2 : (2 : ℝ) / ((d : ℝ) - 1) = 1 / ((d : ℝ) - 1) + 1 / ((d : ℝ) - 1) := by ring
      rw [e2]
      linarith

/-- **Inner time window.** -/
theorem inner_window_bound {d : ℕ} (hd : 3 ≤ d) {f : ℝ → ℝ} (hfc : Continuous f)
    (hfn : ∀ σ, 0 ≤ f σ) {c l u t W Ls A1 A2 Al m : ℝ} (hc : 0 < c) (hlu : l ≤ u)
    (hwlo : -W ≤ c * (l - t)) (hwhi : c * (u - t) ≤ W) (hm : 0 ≤ m)
    (hdist : ∀ s ∈ Icc l u, m ≤ |c * (s - t)|) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hpt : ∀ σ, |σ| ≤ Ls → f σ ≤ A1 + A2 * ((1 + |σ|) ^ d)⁻¹)
    (hlarge : ∫ σ in {σ : ℝ | Ls ≤ |σ| ∧ |σ| ≤ W}, f σ ≤ Al) :
    (∫ s in Icc l u, f (c * (s - t))) ≤
      (u - l) * A1 + c⁻¹ * (A2 * (2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1))) + Al) := by
  rw [Sumint.integral_Icc_affine f hc hlu t]
  set α := c * (l - t) with hα
  set β := c * (u - t) with hβ
  have hαβ : α ≤ β := mul_le_mul_of_nonneg_left (sub_le_sub_right hlu t) hc.le
  have hg : Continuous (fun σ : ℝ => ((1 + |σ|) ^ d)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun σ => (pow_pos (by positivity) _).ne')
  set S : Set ℝ := {σ : ℝ | Ls ≤ |σ| ∧ |σ| ≤ W} with hS
  have hSsub : S ⊆ Icc (-W) W := fun σ hσ => abs_le.mp hσ.2
  have hfS : IntegrableOn f S := (hfc.integrableOn_Icc (a := -W) (b := W)).mono_set hSsub
  have hJint : IntegrableOn f (Icc α β) := hfc.integrableOn_Icc
  have hgJ : IntegrableOn (fun σ : ℝ => ((1 + |σ|) ^ d)⁻¹) (Icc α β) := hg.integrableOn_Icc
  have hSclosed : MeasurableSet S := by
    have : IsClosed S := by
      refine IsClosed.inter (isClosed_le continuous_const continuous_abs) (isClosed_le continuous_abs continuous_const)
    exact this.measurableSet
  have hind : IntegrableOn (S.indicator f) (Icc α β) :=
    ((integrable_indicator_iff hSclosed).mpr hfS).integrableOn
  have hpoint : ∀ σ ∈ Icc α β, f σ ≤ (A1 + A2 * ((1 + |σ|) ^ d)⁻¹) + S.indicator f σ := by
    intro σ hσ
    by_cases h : |σ| ≤ Ls
    · by_cases hS' : σ ∈ S
      · rw [indicator_of_mem hS']
        have := hpt σ h
        linarith [hfn σ]
      · rw [indicator_of_notMem hS']
        have := hpt σ h
        linarith
    · push Not at h
      have hσS : σ ∈ S := ⟨h.le, abs_le.mpr ⟨by linarith [hσ.1, hwlo], by linarith [hσ.2, hwhi]⟩⟩
      rw [indicator_of_mem hσS]
      have : 0 ≤ A1 + A2 * ((1 + |σ|) ^ d)⁻¹ := by positivity
      linarith
  have hA1int : IntegrableOn (fun _ : ℝ => A1) (Icc α β) :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hI1 : IntegrableOn (fun σ : ℝ => A1 + A2 * ((1 + |σ|) ^ d)⁻¹) (Icc α β) :=
    hA1int.add (hgJ.const_mul A2)
  have hmono : (∫ σ in Icc α β, f σ) ≤
      (∫ σ in Icc α β, (A1 + A2 * ((1 + |σ|) ^ d)⁻¹)) + ∫ σ in Icc α β, S.indicator f σ := by
    rw [← integral_add hI1 hind]
    exact setIntegral_mono_on hJint (hI1.add hind) measurableSet_Icc hpoint
  have hsplit2 : (∫ σ in Icc α β, (A1 + A2 * ((1 + |σ|) ^ d)⁻¹)) =
      (∫ σ in Icc α β, A1) + A2 * ∫ σ in Icc α β, ((1 + |σ|) ^ d)⁻¹ := by
    rw [integral_add hA1int (hgJ.const_mul A2), integral_const_mul]
  rw [hsplit2] at hmono
  have h1 : (∫ σ in Icc α β, A1) = (β - α) * A1 := by
    simp [Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hαβ), mul_comm]
  have h2 : (∫ σ in Icc α β, ((1 + |σ|) ^ d)⁻¹) ≤ 2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1)) :=
    integral_inv_pow_le hd hm hαβ (fun σ hσ => by
      obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Icc l u, σ = c * (s - t) := by
        refine ⟨σ / c + t, ⟨?_, ?_⟩, ?_⟩
        · have h' : c * (l - t) ≤ σ := hσ.1
          have : l - t ≤ σ / c := by rw [le_div_iff₀ hc]; nlinarith
          linarith
        · have h' : σ ≤ c * (u - t) := hσ.2
          have : σ / c ≤ u - t := by rw [div_le_iff₀ hc]; nlinarith
          linarith
        · field_simp; ring
      exact hdist s hs)
  have h3 : (∫ σ in Icc α β, S.indicator f σ) ≤ ∫ σ in S, f σ := by
    rw [setIntegral_indicator hSclosed]
    exact setIntegral_mono_set hfS (ae_of_all _ (fun σ => hfn σ)) (ae_of_all _ (fun σ hσ => hσ.2))
  have hβα : β - α = c * (u - l) := by rw [hα, hβ]; ring
  have key : (∫ σ in Icc α β, f σ) ≤ (c * (u - l)) * A1 +
      (A2 * (2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1))) + Al) := by
    calc (∫ σ in Icc α β, f σ) ≤ _ := hmono
      _ ≤ _ := by
        rw [h1, hβα]
        have := mul_le_mul_of_nonneg_left h2 hA2
        linarith
  calc c⁻¹ * (∫ σ in Icc α β, f σ)
      ≤ c⁻¹ * ((c * (u - l)) * A1 + (A2 * (2 / ((d : ℝ) - 1) * (1 + m) ^ (-((d : ℝ) - 1))) + Al)) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    _ = _ := by field_simp

/-- The distance weight integrates to at most `c⁻¹` along a box. -/
theorem outer_decay {d : ℕ} (hd : 3 ≤ d) {c v w : ℝ} (hc : 0 < c) (hvw : v ≤ w) :
    (∫ t in Icc v w, (1 + c * (t - v)) ^ (-((d : ℝ) - 1))) ≤ c⁻¹ := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hle : ∀ t ∈ Icc v w, (1 + c * (t - v)) ^ (-((d : ℝ) - 1)) ≤ ((1 + c * (t - v)) ^ 2)⁻¹ := by
    intro t ht
    have h1 : 1 ≤ 1 + c * (t - v) := by nlinarith [ht.1, mul_nonneg hc.le (sub_nonneg.mpr ht.1)]
    rw [show ((1 + c * (t - v)) ^ 2)⁻¹ = (1 + c * (t - v)) ^ (-(2 : ℝ)) by
      rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hint : IntervalIntegrable (fun t : ℝ => ((1 + c * (t - v)) ^ 2)⁻¹) volume v w := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) (fun t ht => ?_)
    rw [uIcc_of_le hvw] at ht
    exact (pow_pos (by nlinarith [ht.1, mul_nonneg hc.le (sub_nonneg.mpr ht.1)]) _).ne'
  have hder : ∀ t ∈ uIcc v w, HasDerivAt (fun t : ℝ => -(c⁻¹ * (1 + c * (t - v))⁻¹))
      (((1 + c * (t - v)) ^ 2)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hvw] at ht
    have h1 : 0 < 1 + c * (t - v) := by nlinarith [ht.1, mul_nonneg hc.le (sub_nonneg.mpr ht.1)]
    have hl : HasDerivAt (fun t : ℝ => 1 + c * (t - v)) c t := by
      have := (((hasDerivAt_id t).sub_const v).const_mul c).const_add 1
      simpa using this
    have := (hl.inv h1.ne').const_mul c⁻¹ |>.neg
    refine this.congr_deriv ?_
    field_simp
  calc (∫ t in Icc v w, (1 + c * (t - v)) ^ (-((d : ℝ) - 1)))
      ≤ ∫ t in Icc v w, ((1 + c * (t - v)) ^ 2)⁻¹ := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Icc hle
        · refine ContinuousOn.integrableOn_Icc ?_
          refine ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl ?_)
          nlinarith [ht.1, mul_nonneg hc.le (sub_nonneg.mpr ht.1)]
        · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hvw] at hint
          exact hint
    _ = ∫ t in v..w, ((1 + c * (t - v)) ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_of_le hvw, integral_Icc_eq_integral_Ioc]
    _ ≤ _ := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
        have h2 : 0 < 1 + c * (w - v) := by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hvw)]
        simp only [sub_self, mul_zero, add_zero, inv_one, mul_one]
        have : 0 ≤ c⁻¹ * (1 + c * (w - v))⁻¹ := by positivity
        linarith

/-- The reflected distance weight. -/
theorem outer_decay_rev {d : ℕ} (hd : 3 ≤ d) {c v w : ℝ} (hc : 0 < c) (hvw : v ≤ w) :
    (∫ t in Icc v w, (1 + c * (w - t)) ^ (-((d : ℝ) - 1))) ≤ c⁻¹ := by
  have h0 := outer_decay hd hc (v := 0) (w := w - v) (by linarith)
  refine le_trans (le_of_eq ?_) h0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hvw,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ w - v)]
  have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => (1 + c * (x - 0)) ^ (-((d : ℝ) - 1))) (a := v) (b := w) w
  simp only [sub_zero] at this ⊢
  rw [this]
  simp

end WaveTurbulence.LadderDecay
