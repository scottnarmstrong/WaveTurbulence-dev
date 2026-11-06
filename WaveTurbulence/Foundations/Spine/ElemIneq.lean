/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
/-! # The elementary inequality (DH21 (10.5), L2428; TARGET (elementarylem), L2004–L2006)
`sup_{[0,1]^ι} |F| ≤ ∑_{A ⊆ ι} ∫_{[0,1]^ι} |∏_{v∈A}(∂_v − πi L_v) F|`.
Formulated for a family `Φ A` standing for `∏_{v∈A}(∂_v − πi L_v) F`, with
`∂_b Φ A = Φ (insert b A) + πi L_b Φ A`. -/
@[expose] public section
open MeasureTheory Set Function Finset
open scoped ENNReal
namespace WaveTurbulence.Ladder

/-- The unimodular phase `e^{-i c y}`. -/
noncomputable def ph (c y : ℝ) : ℂ := Complex.exp (((-(c * y) : ℝ) : ℂ) * Complex.I)

theorem enorm_ph (c y : ℝ) : ‖ph c y‖ₑ = 1 := by
  unfold ph
  rw [Complex.enorm_exp_ofReal_mul_I]

theorem continuous_ph (c : ℝ) : Continuous (ph c) := by unfold ph; fun_prop

theorem hasDerivAt_ph (c y : ℝ) : HasDerivAt (ph c) (ph c y * (-(c:ℂ) * Complex.I)) y := by
  have h0 : HasDerivAt (fun y : ℝ => -(c * y)) (-c) y := by
    have := HasDerivAt.neg (HasDerivAt.const_mul c (hasDerivAt_id y))
    convert this using 1
    · funext y; simp
    · simp
  have h1 := HasDerivAt.cexp (HasDerivAt.mul_const (HasDerivAt.ofReal_comp h0) Complex.I)
  unfold ph
  convert h1 using 1
  push_cast; ring

/-- One-variable form: `‖f x‖ ≤ ∫_0^1 ‖f‖ + ∫_0^1 ‖f' - πiL f‖` for `x ∈ [0,1]`. -/
theorem enorm_le_two_integrals (f g : ℝ → ℂ) (c : ℝ) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ y, HasDerivAt f (g y + (c : ℂ) * Complex.I * f y) y)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ‖f x‖ₑ ≤ ∫⁻ y in Icc (0:ℝ) 1, (‖f y‖ₑ + ‖g y‖ₑ) := by
  set h : ℝ → ℂ := fun y => ph c y * f y with hh
  have hhd : ∀ y, HasDerivAt h (ph c y * g y) y := by
    intro y
    have := HasDerivAt.mul (hasDerivAt_ph c y) (hd y)
    convert this using 1
    ring
  have hnorm : ∀ y, ‖h y‖ₑ = ‖f y‖ₑ := by
    intro y; simp only [hh, enorm_mul, enorm_ph, one_mul]
  have h3 : ∀ u, ‖ph c u * g u‖ₑ = ‖g u‖ₑ := by
    intro u; rw [enorm_mul, enorm_ph, one_mul]
  have hgc : Continuous fun y => ph c y * g y := (continuous_ph c).mul hg
  have key : ∀ y ∈ Icc (0:ℝ) 1, ‖f x‖ₑ ≤ ‖f y‖ₑ + ∫⁻ u in Icc (0:ℝ) 1, ‖g u‖ₑ := by
    intro y hy
    have hFTC : ∫ u in y..x, ph c u * g u = h x - h y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hhd u)
        (hgc.intervalIntegrable _ _)
    have h2 : ‖h x - h y‖ₑ ≤ ∫⁻ u in uIoc y x, ‖ph c u * g u‖ₑ := by
      rw [← hFTC]
      rcases le_total y x with hyx | hxy
      · rw [intervalIntegral.integral_of_le hyx, uIoc_of_le hyx]
        exact enorm_integral_le_lintegral_enorm _
      · rw [intervalIntegral.integral_of_ge hxy, uIoc_of_ge hxy, enorm_neg]
        exact enorm_integral_le_lintegral_enorm _
    simp_rw [h3] at h2
    have hsub : uIoc y x ⊆ Icc (0:ℝ) 1 := uIoc_subset_uIcc.trans (uIcc_subset_Icc hy hx)
    calc ‖f x‖ₑ = ‖h x‖ₑ := (hnorm x).symm
      _ = ‖h y + (h x - h y)‖ₑ := by rw [add_sub_cancel]
      _ ≤ ‖h y‖ₑ + ‖h x - h y‖ₑ := enorm_add_le _ _
      _ ≤ ‖f y‖ₑ + ∫⁻ u in Icc (0:ℝ) 1, ‖g u‖ₑ := by
        rw [hnorm]
        gcongr
        exact h2.trans (lintegral_mono_set hsub)
  have hmeas : Measurable fun y => ‖f y‖ₑ := hf.measurable.enorm
  calc ‖f x‖ₑ = ∫⁻ y in Icc (0:ℝ) 1, ‖f x‖ₑ := by simp
    _ ≤ ∫⁻ y in Icc (0:ℝ) 1, (‖f y‖ₑ + ∫⁻ u in Icc (0:ℝ) 1, ‖g u‖ₑ) :=
      setLIntegral_mono' measurableSet_Icc key
    _ = _ := by
      rw [lintegral_add_right _ measurable_const, lintegral_add_left hmeas]
      simp


section Multi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lebesgue measure on the unit interval in each coordinate. -/
noncomputable abbrev boxμ (ι : Type*) : ι → Measure ℝ := fun _ => volume.restrict (Icc (0:ℝ) 1)

theorem elem_aux (Φ : Finset ι → (ι → ℝ) → ℂ) (c : ι → ℝ) (hc : ∀ A, Continuous (Φ A))
    (hd : ∀ A b, b ∉ A → ∀ x : ι → ℝ,
      HasDerivAt (fun r => Φ A (update x b r))
        (Φ (insert b A) x + ((c b : ℝ) : ℂ) * Complex.I * Φ A x) (x b)) :
    ∀ (s : Finset ι) (A : Finset ι), Disjoint A s → ∀ x : ι → ℝ, (∀ i ∈ s, x i ∈ Icc (0:ℝ) 1) →
      ‖Φ A x‖ₑ ≤ ∑ B ∈ s.powerset, (∫⋯∫⁻_s, (fun y => ‖Φ (A ∪ B) y‖ₑ) ∂boxμ ι) x := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro A _ x _
    simp
  | insert b s' hb ih =>
    intro A hA x hx
    have hbA : b ∉ A := fun h => (Finset.disjoint_left.mp hA h) (Finset.mem_insert_self _ _)
    have hAs : Disjoint A s' := hA.mono_right (Finset.subset_insert _ _)
    have hbAs : Disjoint (insert b A) s' := by
      rw [Finset.disjoint_left]; intro a ha has
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hb has
      · exact (Finset.disjoint_left.mp hAs ha) has
    -- one-variable step
    have hd' : ∀ y, HasDerivAt (fun r => Φ A (update x b r))
        (Φ (insert b A) (update x b y) + ((c b : ℝ) : ℂ) * Complex.I * Φ A (update x b y)) y := by
      intro y
      have := hd A b hbA (update x b y)
      simpa using this
    have h1 := enorm_le_two_integrals (fun r => Φ A (update x b r))
      (fun r => Φ (insert b A) (update x b r)) (c b)
      ((hc A).comp (continuous_const.update b continuous_id))
      ((hc _).comp (continuous_const.update b continuous_id)) hd'
      (x := x b) (hx b (Finset.mem_insert_self _ _))
    simp only [update_eq_self] at h1
    have hmeasm : ∀ A' : Finset ι, ∀ s'' : Finset ι, Measurable
        (fun y : ℝ => (∫⋯∫⁻_s'', (fun z => ‖Φ A' z‖ₑ) ∂boxμ ι) (update x b y)) := by
      intro A' s''
      exact ((((hc A').measurable.enorm).lmarginal (boxμ ι)).comp
        (measurable_update x))
    have h2 : ∀ y, ‖Φ A (update x b y)‖ₑ + ‖Φ (insert b A) (update x b y)‖ₑ ≤
        ∑ B ∈ s'.powerset, (∫⋯∫⁻_s', (fun z => ‖Φ (A ∪ B) z‖ₑ) ∂boxμ ι) (update x b y) +
        ∑ B ∈ s'.powerset, (∫⋯∫⁻_s', (fun z => ‖Φ (insert b A ∪ B) z‖ₑ) ∂boxμ ι) (update x b y) := by
      intro y
      refine add_le_add (ih A hAs _ ?_) (ih (insert b A) hbAs _ ?_)
      all_goals
        intro i hi
        rw [update_of_ne (by rintro rfl; exact hb hi)]
        exact hx i (Finset.mem_insert_of_mem hi)
    calc ‖Φ A x‖ₑ ≤ ∫⁻ y in Icc (0:ℝ) 1, (‖Φ A (update x b y)‖ₑ + ‖Φ (insert b A) (update x b y)‖ₑ) := h1
      _ ≤ ∫⁻ y in Icc (0:ℝ) 1,
          (∑ B ∈ s'.powerset, (∫⋯∫⁻_s', (fun z => ‖Φ (A ∪ B) z‖ₑ) ∂boxμ ι) (update x b y) +
          ∑ B ∈ s'.powerset, (∫⋯∫⁻_s', (fun z => ‖Φ (insert b A ∪ B) z‖ₑ) ∂boxμ ι) (update x b y)) :=
        lintegral_mono h2
      _ = ∑ B ∈ s'.powerset, (∫⋯∫⁻_insert b s', (fun z => ‖Φ (A ∪ B) z‖ₑ) ∂boxμ ι) x +
          ∑ B ∈ s'.powerset, (∫⋯∫⁻_insert b s', (fun z => ‖Φ (insert b A ∪ B) z‖ₑ) ∂boxμ ι) x := by
        rw [lintegral_add_left (Finset.measurable_sum _ (fun B _ => hmeasm _ _)),
          lintegral_finsetSum _ (fun B _ => hmeasm _ _),
          lintegral_finsetSum _ (fun B _ => hmeasm _ _)]
        congr 1
        · refine Finset.sum_congr rfl (fun B _ => ?_)
          rw [lmarginal_insert _ (hc _).measurable.enorm hb]
        · refine Finset.sum_congr rfl (fun B _ => ?_)
          rw [lmarginal_insert _ (hc _).measurable.enorm hb]
      _ = _ := by
        rw [Finset.sum_powerset_insert hb]
        congr 1
        refine Finset.sum_congr rfl (fun B hB => ?_)
        have : A ∪ insert b B = insert b A ∪ B := by
          ext a; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        rw [this]

/-- DH21 (10.5), L2428; TARGET (elementarylem), L2004–L2006: `sup_{[0,1]^ι}|F| ≤ ∑_A ∫|D_A F|`. -/
theorem elementary_sup_le (Φ : Finset ι → (ι → ℝ) → ℂ) (c : ι → ℝ) (hc : ∀ A, Continuous (Φ A))
    (hd : ∀ A b, b ∉ A → ∀ x : ι → ℝ,
      HasDerivAt (fun r => Φ A (update x b r))
        (Φ (insert b A) x + ((c b : ℝ) : ℂ) * Complex.I * Φ A x) (x b))
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) :
    ‖Φ ∅ x‖ₑ ≤ ∑ B : Finset ι,
      (∫⋯∫⁻_(Finset.univ : Finset ι), (fun y => ‖Φ B y‖ₑ) ∂boxμ ι) x := by
  have := elem_aux Φ c hc hd Finset.univ ∅ (Finset.disjoint_empty_left _) x (fun i _ => hx i)
  simpa using this

end Multi
end WaveTurbulence.Ladder
