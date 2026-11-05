/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma5
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
/-! Weights `(t_v - c_v)` in the forest time integrals (the factors `πi(t_v - 𝔏_v)` produced by the
elementary inequality, TARGET L2007–L2008): `t_v - c_v = ∫_0^1 1[c_v + s < t_v] ds` turns the weight into
a modified lower limit, and `Uint_bound` is uniform in the limits. -/
@[expose] public section
open MeasureTheory Set Finset Function
namespace WaveTurbulence.Ladder

noncomputable instance instProbUnit : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Weighted forest integral. -/
noncomputable def Uintw {n : ℕ} (par : Par n) (l u β c : Fin n → ℝ) (wt : Fin n → Bool) : ℂ :=
  ∫ t : Fin n → ℝ, (∏ v, (if wt v = true then (((t v - c v : ℝ)) : ℂ) else 1)) * Fd par l u β t

/-- The shifted lower limits. -/
def lShift {n : ℕ} (l c : Fin n → ℝ) (wt : Fin n → Bool) (s : Fin n → ℝ) : Fin n → ℝ :=
  fun v => if wt v = true then max (l v) (c v + s v) else l v

theorem le_lShift {n : ℕ} (l c : Fin n → ℝ) (wt : Fin n → Bool) (s : Fin n → ℝ) (v : Fin n) :
    l v ≤ lShift l c wt s v := by
  unfold lShift; split_ifs <;> simp

theorem Fd_lShift {n : ℕ} (par : Par n) (l u β c : Fin n → ℝ) (wt : Fin n → Bool) (s t : Fin n → ℝ) :
    Fd par (lShift l c wt s) u β t =
      (∏ v, (if wt v = true ∧ ¬ (c v + s v < t v) then (0 : ℂ) else 1)) * Fd par l u β t := by
  unfold Fd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  unfold Gf lShift
  by_cases hw : wt v = true
  · simp only [hw, ite_true, true_and]
    have hmem : (if t v ∈ Ioc (max (l v) (c v + s v)) (u v) then (1 : ℂ) else 0) =
        (if t v ∈ Ioc (l v) (u v) then 1 else 0) * (if c v + s v < t v then 1 else 0) := by
      by_cases h1 : t v ∈ Ioc (l v) (u v)
      · by_cases h2 : c v + s v < t v
        · have : t v ∈ Ioc (max (l v) (c v + s v)) (u v) := ⟨max_lt h1.1 h2, h1.2⟩
          simp [this, h1, h2]
        · have : t v ∉ Ioc (max (l v) (c v + s v)) (u v) := fun h => h2 (lt_of_le_of_lt (le_max_right _ _) h.1)
          simp [this, h2]
      · have : t v ∉ Ioc (max (l v) (c v + s v)) (u v) :=
          fun h => h1 ⟨lt_of_le_of_lt (le_max_left _ _) h.1, h.2⟩
        simp [this, h1]
    rw [hmem]
    by_cases h2 : c v + s v < t v <;> simp [h2]
  · simp [hw]


theorem integral_lt_ind {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    ∫ x in Icc (0 : ℝ) 1, (if x < d then (1 : ℂ) else 0) = (d : ℂ) := by
  have e : ∀ x : ℝ, (if x < d then (1 : ℂ) else 0) = (Iio d).indicator (fun _ => (1 : ℂ)) x := by
    intro x; by_cases h : x < d <;> simp [h]
  simp_rw [e]
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    setIntegral_const]
  have : Iio d ∩ Icc (0 : ℝ) 1 = Ico 0 d := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
  rw [this, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  simp

theorem integral_prod_ind {n : ℕ} (wt : Fin n → Bool) (c t : Fin n → ℝ)
    (ht : ∀ v, wt v = true → t v ∈ Ioc (c v) (c v + 1)) :
    ∫ s : Fin n → ℝ, (∏ v, (if wt v = true ∧ ¬ (c v + s v < t v) then (0 : ℂ) else 1))
      ∂(Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) =
    ∏ v, (if wt v = true then (((t v - c v : ℝ)) : ℂ) else 1) := by
  have := integral_fin_nat_prod_eq_prod (𝕜 := ℂ) (n := n)
    (μ := fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1))
    (fun v (x : ℝ) => if wt v = true ∧ ¬ (c v + x < t v) then (0 : ℂ) else 1)
  rw [this]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hw : wt v = true
  · have hv := ht v hw
    have e : ∀ x : ℝ, (if wt v = true ∧ ¬ (c v + x < t v) then (0 : ℂ) else 1) =
        if x < t v - c v then 1 else 0 := by
      intro x; simp only [hw, true_and]
      by_cases h : x < t v - c v
      · have : c v + x < t v := by linarith
        simp [h, this]
      · have : ¬ (c v + x < t v) := by intro h'; apply h; linarith
        simp [h, this]
    simp_rw [e]
    simp only [hw, ite_true]
    exact integral_lt_ind (by linarith [hv.1]) (by linarith [hv.2])
  · simp [hw]


theorem Uintw_bound {n : ℕ} (par : Par n) (hp : ParOK par) (l u β c : Fin n → ℝ) (wt : Fin n → Bool)
    (hlu : ∀ v, u v - l v ≤ 1) (hwt : ∀ v, wt v = true → c v ≤ l v ∧ u v ≤ c v + 1) :
    ‖Uintw par l u β c wt‖ ≤ 3 ^ n * Bd n par β := by
  set μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1) with hμ
  have : IsProbabilityMeasure μ := inferInstance
  have hA : ∀ t : Fin n → ℝ, (∏ v, (if wt v = true then (((t v - c v : ℝ)) : ℂ) else 1)) * Fd par l u β t =
      ∫ s, Fd par (lShift l c wt s) u β t ∂μ := by
    intro t
    simp_rw [Fd_lShift]
    rw [integral_mul_const]
    by_cases h0 : Fd par l u β t = 0
    · simp [h0]
    · congr 1
      have hmem : ∀ v, t v ∈ Ioc (l v) (u v) := fun v => by
        by_contra h; exact h0 (Fd_zero_of_notmem par l u β t v h)
      rw [integral_prod_ind wt c t (fun v hv => by
        have := hwt v hv; have := hmem v
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)]
  have hmeas : ∀ p : (Fin n → ℝ) × (Fin n → ℝ), True := fun _ => trivial
  have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Fd par (lShift l c wt p.2) u β p.1) := by
    have : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Fd par (lShift l c wt p.2) u β p.1) =
        fun p => (∏ v, (if wt v = true ∧ ¬ (c v + p.2 v < p.1 v) then (0 : ℂ) else 1)) *
          Fd par l u β p.1 := by
      funext p; exact Fd_lShift par l u β c wt p.2 p.1
    rw [this]
    refine Measurable.mul (Finset.measurable_prod _ (fun v _ => ?_))
      ((measurable_Fd par l u β).comp measurable_fst)
    refine Measurable.ite ?_ measurable_const measurable_const
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact (measurableSet_lt (measurable_const.add ((measurable_pi_apply v).comp measurable_snd))
      ((measurable_pi_apply v).comp measurable_fst)).compl
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Fd par (lShift l c wt p.2) u β p.1)
      (volume.prod μ) := by
    have hb : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ‖Fd par l u β p.1‖)
        (volume.prod μ) := (integrable_Fd par l u β).norm.comp_fst μ
    refine hb.mono' hjoint.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
    rw [Fd_lShift, norm_mul]
    have : ‖∏ v, (if wt v = true ∧ ¬ (c v + p.2 v < p.1 v) then (0 : ℂ) else 1)‖ ≤ 1 := by
      rw [norm_prod]
      refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun v _ => ?_)
      split_ifs <;> simp
    nlinarith [norm_nonneg (Fd par l u β p.1)]
  have hB : Uintw par l u β c wt = ∫ s, Uint par (lShift l c wt s) u β ∂μ := by
    unfold Uintw Uint
    simp_rw [hA]
    exact integral_integral_swap hint
  rw [hB]
  have hb : ∀ s, ‖Uint par (lShift l c wt s) u β‖ ≤ 3 ^ n * Bd n par β := fun s =>
    Uint_bound n par hp _ u β (fun v => by have := le_lShift l c wt s v; linarith [hlu v])
  calc _ ≤ (3 ^ n * Bd n par β) * μ.real univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)
    _ = _ := by simp

end WaveTurbulence.Ladder
