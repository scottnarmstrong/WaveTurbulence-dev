/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeWeights
public import WaveTurbulence.Foundations.Spine.AlphaInt
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
/-! Core estimate in the product model (TARGET L2012–L2037, Steps 3–4 of ladderl1old):
the `X` coordinates are integrated against absolute values, the `Y` coordinates by `Uintw_bound`. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder

theorem br_mono {x y : ℝ} (h : |x| ≤ |y|) : br x ≤ br y := by
  unfold br
  exact Real.sqrt_le_sqrt (by nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y])

theorem Bd_scale_le {ϖ : ℝ} (hϖ : 1 ≤ ϖ) : ∀ (n : ℕ) (par : Par n) (β : Fin n → ℝ),
    Bd n par (ϖ • β) ≤ Bd n par β
  | 0, _, _ => by simp [Bd]
  | n + 1, par, β => by
    have hab : ∀ d, absorb par (ϖ • β) d = ϖ • absorb par β d := by
      intro d; funext v
      by_cases h : d = true ∧ par 0 = some v.succ <;> simp [absorb, h, mul_add]
    simp only [Bd, hab]
    have h0 : (br ((ϖ • β) 0))⁻¹ ≤ (br (β 0))⁻¹ := by
      apply inv_anti₀ (br_pos _)
      apply br_mono
      have : |(ϖ • β) 0| = ϖ * |β 0| := by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [abs_mul, abs_of_pos (by linarith)]
      rw [this]; nlinarith [abs_nonneg (β 0)]
    have h1 := Bd_scale_le hϖ n (parTail par) (absorb par β false)
    have h2 := Bd_scale_le hϖ n (parTail par) (absorb par β true)
    have := Bd_nonneg n (parTail par) (absorb par β false)
    have := Bd_nonneg n (parTail par) (absorb par β true)
    have := Bd_nonneg n (parTail par) (ϖ • absorb par β false)
    have := Bd_nonneg n (parTail par) (ϖ • absorb par β true)
    have := inv_pos.mpr (br_pos (β 0))
    have := inv_pos.mpr (br_pos ((ϖ • β) 0))
    exact mul_le_mul h0 (add_le_add h1 h2) (by positivity) (by positivity)


/-- The product-model Fourier transform. -/
noncomputable def Bprod {k m : ℕ} (par : Par m) (c : Fin m → ℝ) (wt : Fin m → Bool)
    (lo hi : (Fin k → ℝ) → Fin m → ℝ) (R : Set (Fin k → ℝ)) (wX : (Fin k → ℝ) → ℂ)
    (α : (Fin k → ℝ) × (Fin m → ℝ)) : ℂ :=
  ∫ tx in R, wX tx * ((∏ i, ee (Real.pi * α.1 i) (tx i)) *
    Uintw par (lo tx) (hi tx) (Real.pi • α.2) c wt)

theorem enorm_Bprod_le {k m : ℕ} (par : Par m) (hp : ParOK par) (c : Fin m → ℝ) (wt : Fin m → Bool)
    (lo hi : (Fin k → ℝ) → Fin m → ℝ) (hlohi : ∀ tx v, hi tx v - lo tx v ≤ 1)
    (hwt : ∀ tx v, wt v = true → c v ≤ lo tx v ∧ hi tx v ≤ c v + 1)
    (R : Set (Fin k → ℝ)) (hRm : MeasurableSet R) (wX : (Fin k → ℝ) → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hwX : ∀ tx ∈ R, ‖wX tx‖ ≤ Cw)
    (α : (Fin k → ℝ) × (Fin m → ℝ)) :
    ‖Bprod par c wt lo hi R wX α‖ₑ ≤
      volume R * ENNReal.ofReal (Cw * (3 ^ m * Bd m par α.2)) := by
  unfold Bprod
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hb : ∀ tx ∈ R, ‖wX tx * ((∏ i, ee (Real.pi * α.1 i) (tx i)) *
      Uintw par (lo tx) (hi tx) (Real.pi • α.2) c wt)‖ₑ ≤
      ENNReal.ofReal (Cw * (3 ^ m * Bd m par α.2)) := by
    intro tx htx
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, norm_mul, norm_prod]
    simp only [norm_ee, Finset.prod_const_one, one_mul]
    have h1 := Uintw_bound par hp (lo tx) (hi tx) (Real.pi • α.2) c wt (hlohi tx) (hwt tx)
    have h2 := Bd_scale_le (ϖ := Real.pi) (by linarith [Real.pi_gt_three]) m par α.2
    exact mul_le_mul (hwX tx htx) (h1.trans (by gcongr)) (norm_nonneg _) hCw
  calc _ ≤ ∫⁻ tx in R, ENNReal.ofReal (Cw * (3 ^ m * Bd m par α.2)) := setLIntegral_mono' hRm hb
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]


theorem core1 {k m : ℕ} (par : Par m) (hp : ParOK par) (c : Fin m → ℝ) (wt : Fin m → Bool)
    (lo hi : (Fin k → ℝ) → Fin m → ℝ) (hlohi : ∀ tx v, hi tx v - lo tx v ≤ 1)
    (hwt : ∀ tx v, wt v = true → c v ≤ lo tx v ∧ hi tx v ≤ c v + 1)
    (R : Set (Fin k → ℝ)) (hRm : MeasurableSet R) (hRfin : volume R ≠ ⊤) (wX : (Fin k → ℝ) → ℂ) (Cw : ℝ)
    (hCw : 0 ≤ Cw) (hwX : ∀ tx ∈ R, ‖wX tx‖ ≤ Cw)
    (S : Fin m → Set ℝ) (hS : ∀ v, MeasurableSet (S v)) (K : ℝ≥0∞)
    (hK : ∀ v (β : ℝ), ∫⁻ a in S v, ENNReal.ofReal (br (a + β))⁻¹ ≤ K)
    (h : (Fin m → ℝ) → (Fin k → ℝ)) (hh : Measurable h) (ρ : Fin k → ℝ)
    (W0 : Set ((Fin k → ℝ) × (Fin m → ℝ)))
    (hW0 : ∀ α ∈ W0, α.2 ∈ Set.pi univ S ∧ ∀ i, |α.1 i - h α.2 i| ≤ ρ i) :
    ∫⁻ α in W0, ‖Bprod par c wt lo hi R wX α‖ₑ ≤
      (∏ i, ENNReal.ofReal (2 * ρ i)) * (volume R * ENNReal.ofReal (Cw * 3 ^ m) * (2 * K) ^ m) := by
  set G : (Fin m → ℝ) → ℝ≥0∞ := fun y => volume R * ENNReal.ofReal (Cw * (3 ^ m * Bd m par y)) with hG
  set A : Set ((Fin k → ℝ) × (Fin m → ℝ)) :=
    {α | α.2 ∈ Set.pi univ S ∧ ∀ i, |α.1 i - h α.2 i| ≤ ρ i} with hA
  have hAm : MeasurableSet A := by
    show MeasurableSet ({α : (Fin k → ℝ) × (Fin m → ℝ) | α.2 ∈ Set.pi univ S} ∩
      {α | ∀ i, |α.1 i - h α.2 i| ≤ ρ i})
    refine MeasurableSet.inter ?_ ?_
    · exact (MeasurableSet.univ_pi hS).preimage measurable_snd
    · have : {α : (Fin k → ℝ) × (Fin m → ℝ) | ∀ i, |α.1 i - h α.2 i| ≤ ρ i} =
          ⋂ i, {α | |α.1 i - h α.2 i| ≤ ρ i} := by ext α; simp
      rw [this]
      refine MeasurableSet.iInter (fun i => ?_)
      exact measurableSet_le (continuous_abs.measurable.comp
        (((measurable_pi_apply i).comp measurable_fst).sub
          ((measurable_pi_apply i).comp (hh.comp measurable_snd)))) measurable_const
  have hmeasG : Measurable G := by
    have : Measurable fun y : Fin m → ℝ => Cw * (3 ^ m * Bd m par y) :=
      (((continuous_Bd m par).measurable.const_mul ((3:ℝ) ^ m))).const_mul Cw
    exact (ENNReal.measurable_ofReal.comp this).const_mul _
  have step1 : ∫⁻ α in W0, ‖Bprod par c wt lo hi R wX α‖ₑ ≤ ∫⁻ α in A, G α.2 := by
    calc _ ≤ ∫⁻ α in A, ‖Bprod par c wt lo hi R wX α‖ₑ :=
          lintegral_mono_set (fun α hα => hW0 α hα)
      _ ≤ _ := by
          refine setLIntegral_mono' hAm (fun α _ => ?_)
          exact enorm_Bprod_le par hp c wt lo hi hlohi hwt R hRm wX Cw hCw hwX α
  have step2 : ∫⁻ α in A, G α.2 ≤ ∫⁻ y : Fin m → ℝ, (Set.pi univ S).indicator
      (fun y => (∏ i, ENNReal.ofReal (2 * ρ i)) * G y) y := by
    rw [← lintegral_indicator hAm, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine (lintegral_prod_le _).trans (lintegral_mono (fun y => ?_))
    by_cases hy : y ∈ Set.pi univ S
    · rw [Set.indicator_of_mem hy]
      have : ∀ x : Fin k → ℝ, A.indicator (fun α => G α.2) (x, y) =
          (Set.Icc (h y - ρ) (h y + ρ)).indicator (fun _ => G y) x := by
        intro x
        by_cases hx : x ∈ Set.Icc (h y - ρ) (h y + ρ)
        · have : (x, y) ∈ A := ⟨hy, fun i => by
            have := hx.1 i; have := hx.2 i
            simp only [Pi.sub_apply, Pi.add_apply] at *
            rw [abs_le]; constructor <;> linarith⟩
          simp [Set.indicator_of_mem hx, Set.indicator_of_mem this]
        · have : (x, y) ∉ A := fun h' => hx ⟨fun i => by
            have := (abs_le.mp (h'.2 i)).1; simp only [Pi.sub_apply]; linarith,
            fun i => by
            have := (abs_le.mp (h'.2 i)).2; simp only [Pi.add_apply]; linarith⟩
          simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
      simp only [Prod.swap_prod_mk]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc_pi]
      refine le_of_eq ?_
      have : ∏ i : Fin k, ENNReal.ofReal (h y i + ρ i - (h y i - ρ i)) =
          ∏ i, ENNReal.ofReal (2 * ρ i) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        congr 1; ring
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [this, mul_comm]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : Fin k → ℝ, A.indicator (fun α => G α.2) (x, y) = 0 := by
        intro x
        have : (x, y) ∉ A := fun h' => hy h'.1
        simp [Set.indicator_of_notMem this]
      simp [this]
  have step3 : ∫⁻ y : Fin m → ℝ, (Set.pi univ S).indicator
      (fun y => (∏ i, ENNReal.ofReal (2 * ρ i)) * G y) y =
      (∏ i, ENNReal.ofReal (2 * ρ i)) * (volume R * ENNReal.ofReal (Cw * 3 ^ m)) * ∫⁻ y : Fin m → ℝ, (Set.pi univ S).indicator
        (fun y => ENNReal.ofReal (Bd m par (y + 0))) y := by
    rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top))
      (ENNReal.mul_ne_top hRfin ENNReal.ofReal_ne_top))]
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ Set.pi univ S
    · simp only [Set.indicator_of_mem hy, hG, add_zero]
      rw [show Cw * (3 ^ m * Bd m par y) = (Cw * 3 ^ m) * Bd m par y by ring,
        ENNReal.ofReal_mul (by positivity)]
      ring
    · simp [Set.indicator_of_notMem hy]
  have step4 := lintegral_Bd_le K m par S hS hK 0
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ (∏ i, ENNReal.ofReal (2 * ρ i)) * (volume R * ENNReal.ofReal (Cw * 3 ^ m)) * (2 * K) ^ m := by gcongr
    _ = _ := by ring

end WaveTurbulence.Ladder
