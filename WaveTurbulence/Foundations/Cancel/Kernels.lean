/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Reg
public import WaveTurbulence.Foundations.ClassJR.Chain2

/-!
# Regularization through Volterra kernels

The operators of DH21 §5.2 are Volterra kernels (`ClassJR.kcomp`, `ClassJR.volterra`). A parametric kernel
`M : ℝ → ℝ → ℝ → ℂ` (`x ↦ M x`) is regularized in `x` by `gregK θ M t s = greg θ (x ↦ M x t s)`.

* `continuous_kcomp_param`: compositions of jointly continuous parametric kernels are jointly continuous.
* `greg_kcomp_left`, `greg_kcomp_right`, `greg_volterra`: `greg` passes through a composition with a fixed
  continuous kernel, and through a Volterra operator (Fubini, `greg_intervalIntegral`).
* `tendsto_kcomp_left`, `tendsto_kcomp_right`, `tendsto_volterra`: dominated convergence for families of
  kernels converging below the diagonal.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-- A jointly continuous parametric kernel. -/
@[expose] def PCont (M : ℝ → ℝ → ℝ → ℂ) : Prop :=
  Continuous fun p : ℝ × ℝ × ℝ => M p.1 p.2.1 p.2.2

/-- A jointly continuous kernel. -/
@[expose] def KCont (K : ℝ → ℝ → ℂ) : Prop := Continuous fun p : ℝ × ℝ => K p.1 p.2

/-- The regularized kernel `gregK θ M t s = ∫ M x t s e^{-πθ²x²} dx`. -/
@[expose] noncomputable def gregK (θ : ℝ) (M : ℝ → ℝ → ℝ → ℂ) (t s : ℝ) : ℂ :=
  greg θ fun x => M x t s

theorem PCont.const {K : ℝ → ℝ → ℂ} (hK : KCont K) : PCont fun _ => K :=
  hK.comp (continuous_snd.fst.prodMk continuous_snd.snd)

theorem PCont.apply {M : ℝ → ℝ → ℝ → ℂ} (hM : PCont M) (x : ℝ) : KCont (M x) :=
  hM.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))

/-- **Joint continuity of the composition of parametric kernels.** -/
theorem continuous_kcomp_param {A B : ℝ → ℝ → ℝ → ℂ} (hA : PCont A) (hB : PCont B) :
    PCont fun x t s => kcomp (A x) (B x) t s := by
  unfold PCont
  set f : ℝ × ℝ × ℝ → ℝ → ℂ := fun p z => A p.1 p.2.1 z * B p.1 z p.2.2 with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf]
    exact (hA.comp ((continuous_fst.fst).prodMk ((continuous_fst.snd.fst).prodMk continuous_snd))).mul
      (hB.comp ((continuous_fst.fst).prodMk (continuous_snd.prodMk continuous_fst.snd.snd)))
  have e : ∀ p : ℝ × ℝ × ℝ, kcomp (A p.1) (B p.1) p.2.1 p.2.2 =
      (∫ z in (0 : ℝ)..p.2.1, f p z) - ∫ z in (0 : ℝ)..p.2.2, f p z := by
    intro p
    have hc : Continuous (f p) := hfc.comp (continuous_const.prodMk continuous_id)
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 _)
      (hc.intervalIntegrable 0 _)]
    rfl
  simp_rw [e]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hfc
    continuous_snd.fst).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hfc continuous_snd.snd)

/-- A continuous kernel is bounded on the unit square. -/
theorem KCont.exists_bound {K : ℝ → ℝ → ℂ} (hK : KCont K) :
    ∃ C, 0 ≤ C ∧ ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ‖K t s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hK.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, fun t s ht hs => (hC (t, s) ⟨ht, hs⟩).trans (le_max_left _ _)⟩

theorem uIcc_subset_unit {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    uIcc s t ⊆ Icc 0 1 := uIcc_subset_Icc hs ht

/-- **`greg` through a composition with a fixed kernel on the left.** -/
theorem greg_kcomp_left {θ : ℝ} (hθ : 0 < θ) {K : ℝ → ℝ → ℂ} (hK : KCont K)
    {M : ℝ → ℝ → ℝ → ℂ} (hM : PCont M) {C : ℝ}
    (hMb : ∀ x z s, z ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ‖M x z s‖ ≤ C) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    greg θ (fun x => kcomp K (M x) t s) = kcomp K (gregK θ M) t s := by
  obtain ⟨CK, -, hCK⟩ := hK.exists_bound
  unfold kcomp gregK
  rw [greg_intervalIntegral hθ (C := CK * C)]
  · refine intervalIntegral.integral_congr fun z _ => ?_
    exact greg_const_mul θ _ _
  · exact (hK.comp (continuous_const.prodMk continuous_snd)).mul
      (hM.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))
  · intro x z hz
    have hz' := uIcc_subset_unit hs ht hz
    rw [norm_mul]
    exact mul_le_mul (hCK t z ht hz') (hMb x z s hz' hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hCK t z ht hz'))

/-- **`greg` through a composition with a fixed kernel on the right.** -/
theorem greg_kcomp_right {θ : ℝ} (hθ : 0 < θ) {L : ℝ → ℝ → ℂ} (hL : KCont L)
    {M : ℝ → ℝ → ℝ → ℂ} (hM : PCont M) {C : ℝ}
    (hMb : ∀ x t z, t ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → ‖M x t z‖ ≤ C) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    greg θ (fun x => kcomp (M x) L t s) = kcomp (gregK θ M) L t s := by
  obtain ⟨CL, -, hCL⟩ := hL.exists_bound
  unfold kcomp gregK
  rw [greg_intervalIntegral hθ (C := C * CL)]
  · refine intervalIntegral.integral_congr fun z _ => ?_
    exact greg_mul_const θ _ _
  · exact (hM.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
      (hL.comp (continuous_snd.prodMk continuous_const))
  · intro x z hz
    have hz' := uIcc_subset_unit hs ht hz
    rw [norm_mul]
    exact mul_le_mul (hMb x t z ht hz') (hCL z s hz' hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hMb x t z ht hz'))

/-- **`greg` through a Volterra operator.** -/
theorem greg_volterra {θ : ℝ} (hθ : 0 < θ) {M : ℝ → ℝ → ℝ → ℂ} (hM : PCont M) {C : ℝ}
    (hMb : ∀ x t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ‖M x t s‖ ≤ C) {g : ℝ → ℂ}
    (hg : Continuous g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    greg θ (fun x => volterra (M x) g t) = volterra (gregK θ M) g t := by
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc (0 : ℝ) 1))
  unfold volterra gregK
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [greg_intervalIntegral hθ (C := C * Cg)]
  · refine intervalIntegral.integral_congr fun z _ => ?_
    exact greg_mul_const θ _ _
  · exact (hM.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
      (hg.comp continuous_snd)
  · intro x z hz
    have hz' := uIcc_subset_unit h0 ht hz
    rw [norm_mul]
    exact mul_le_mul (hMb x t z ht hz') (hCg z hz') (norm_nonneg _)
      ((norm_nonneg _).trans (hMb x t z ht hz'))

/-! ### Dominated convergence -/

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

/-- Kernels `R i → R₀` below the diagonal, uniformly bounded on the square: `K ∘ R i → K ∘ R₀`. -/
theorem tendsto_kcomp_left {K : ℝ → ℝ → ℂ} (hK : KCont K) {R : ι → ℝ → ℝ → ℂ} {R₀ : ℝ → ℝ → ℂ}
    (hR : ∀ᶠ i in l, KCont (R i)) {C : ℝ}
    (hRb : ∀ᶠ i in l, ∀ z s, z ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ‖R i z s‖ ≤ C)
    (hlim : ∀ z s, 0 ≤ s → s < z → z ≤ 1 → Tendsto (fun i => R i z s) l (𝓝 (R₀ z s)))
    {t s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun i => kcomp K (R i) t s) l (𝓝 (kcomp K R₀ t s)) := by
  obtain ⟨CK, -, hCK⟩ := hK.exists_bound
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
  unfold kcomp
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => CK * C) ?_ ?_
    (intervalIntegrable_const) ?_
  · filter_upwards [hR] with i hi
    exact ((hK.comp (continuous_const.prodMk continuous_id)).mul
      (hi.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · filter_upwards [hRb] with i hi
    refine Eventually.of_forall fun z hz => ?_
    have hz' := uIcc_subset_unit hs ht (uIoc_subset_uIcc hz)
    rw [norm_mul]
    exact mul_le_mul (hCK t z ht hz') (hi z s hz' hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hCK t z ht hz'))
  · refine Eventually.of_forall fun z hz => ?_
    rw [uIoc_of_le hst] at hz
    exact (hlim z s hs0 hz.1 (hz.2.trans ht1)).const_mul _

/-- `R i ∘ L → R₀ ∘ L`. -/
theorem tendsto_kcomp_right {L : ℝ → ℝ → ℂ} (hL : KCont L) {R : ι → ℝ → ℝ → ℂ} {R₀ : ℝ → ℝ → ℂ}
    (hR : ∀ᶠ i in l, KCont (R i)) {C : ℝ}
    (hRb : ∀ᶠ i in l, ∀ t z, t ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → ‖R i t z‖ ≤ C)
    (hlim : ∀ t z, 0 ≤ z → z < t → t ≤ 1 → Tendsto (fun i => R i t z) l (𝓝 (R₀ t z)))
    {t s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun i => kcomp (R i) L t s) l (𝓝 (kcomp R₀ L t s)) := by
  obtain ⟨CL, -, hCL⟩ := hL.exists_bound
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
  unfold kcomp
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C * CL) ?_ ?_
    (intervalIntegrable_const) ?_
  · filter_upwards [hR] with i hi
    exact ((hi.comp (continuous_const.prodMk continuous_id)).mul
      (hL.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · filter_upwards [hRb] with i hi
    refine Eventually.of_forall fun z hz => ?_
    have hz' := uIcc_subset_unit hs ht (uIoc_subset_uIcc hz)
    rw [norm_mul]
    exact mul_le_mul (hi t z ht hz') (hCL z s hz' hs) (norm_nonneg _)
      ((norm_nonneg _).trans (hi t z ht hz'))
  · have hnull : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ t :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_singleton t)).mono fun z hz => hz
    filter_upwards [hnull] with z hzt hz
    rw [uIoc_of_le hst] at hz
    exact (hlim t z (hs0.trans hz.1.le) (lt_of_le_of_ne hz.2 hzt) ht1).mul_const _

/-- `volterra (R i) g t → volterra R₀ g t`. -/
theorem tendsto_volterra {R : ι → ℝ → ℝ → ℂ} {R₀ : ℝ → ℝ → ℂ}
    (hR : ∀ᶠ i in l, KCont (R i)) {C : ℝ}
    (hRb : ∀ᶠ i in l, ∀ t z, t ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → ‖R i t z‖ ≤ C)
    (hlim : ∀ t z, 0 ≤ z → z < t → t ≤ 1 → Tendsto (fun i => R i t z) l (𝓝 (R₀ t z)))
    {g : ℝ → ℂ} (hg : Continuous g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Tendsto (fun i => volterra (R i) g t) l (𝓝 (volterra R₀ g t)) := by
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc (0 : ℝ) 1))
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  unfold volterra
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C * Cg) ?_ ?_
    (intervalIntegrable_const) ?_
  · filter_upwards [hR] with i hi
    exact ((hi.comp (continuous_const.prodMk continuous_id)).mul hg).aestronglyMeasurable
  · filter_upwards [hRb] with i hi
    refine Eventually.of_forall fun z hz => ?_
    have hz' := uIcc_subset_unit h0 ht (uIoc_subset_uIcc hz)
    rw [norm_mul]
    exact mul_le_mul (hi t z ht hz') (hCg z hz') (norm_nonneg _)
      ((norm_nonneg _).trans (hi t z ht hz'))
  · have hnull : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ t :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_singleton t)).mono fun z hz => hz
    filter_upwards [hnull] with z hzt hz
    rw [uIoc_of_le ht0] at hz
    exact (hlim t z hz.1.le (lt_of_le_of_ne hz.2 hzt) ht1).mul_const _

end WaveTurbulence.Cancel
