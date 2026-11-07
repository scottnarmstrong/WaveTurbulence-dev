/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsGlue

/-! # `glueAbs_of_bounds`: absolute convergence of the glued summands from `SAbs` and `UAbs` (V5 Step 4d part C, `hAbs`) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

theorem prodInt_aux {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] (A : X → ℂ) (s : X → ℝ) (M : ℝ × Y → ℂ) (hA : Integrable A μ) (hAm : Measurable A)
    (hs : Measurable s) (hM : Measurable M) (hMi : ∀ r, Integrable (fun y => M (r, y)) ν) {CT : ℝ}
    (hMb : ∀ r, ∫ y, ‖M (r, y)‖ ∂ν ≤ CT) :
    Integrable (fun z : X × Y => A z.1 * M (s z.1, z.2)) (μ.prod ν) ∧
      ∫ z, ‖A z.1 * M (s z.1, z.2)‖ ∂(μ.prod ν) = ∫ x, ‖A x‖ * ∫ y, ‖M (s x, y)‖ ∂ν ∂μ := by
  have hmeas : Measurable (fun z : X × Y => A z.1 * M (s z.1, z.2)) :=
    (hAm.comp measurable_fst).mul (hM.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hrow : ∀ x, ∫ y, ‖A x * M (s x, y)‖ ∂ν = ‖A x‖ * ∫ y, ‖M (s x, y)‖ ∂ν := by
    intro x; simp_rw [norm_mul]; rw [integral_const_mul]
  have hInt : Integrable (fun z : X × Y => A z.1 * M (s z.1, z.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => (hMi (s x)).const_mul (A x), ?_⟩
    simp only [hrow]
    have hm : Measurable fun x => ∫ y, ‖M (s x, y)‖ ∂ν := by
      have : StronglyMeasurable (Function.uncurry fun (r : ℝ) (y : Y) => ‖M (r, y)‖) :=
        (hM.norm.comp (measurable_fst.prodMk measurable_snd)).stronglyMeasurable
      exact (this.integral_prod_right.measurable).comp hs
    refine Integrable.mono' (hA.norm.mul_const (max CT 0)) ((hAm.norm.mul hm).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left ((hMb (s x)).trans (le_max_left _ _)) (norm_nonneg _)
  refine ⟨hInt, ?_⟩
  rw [integral_prod _ hInt.norm]
  exact integral_congr_ae (Filter.Eventually.of_forall hrow)


theorem intI_aux {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] (A : X → ℂ) (s : X → ℝ) (M : ℝ × Y → ℂ) (hA : Integrable A μ) (hAm : Measurable A)
    (hs : Measurable s) (hM : Measurable M) {CT : ℝ}
    (hMb : ∀ r, ∫ y, ‖M (r, y)‖ ∂ν ≤ CT) :
    Integrable (fun x => ‖A x‖ * ∫ y, ‖M (s x, y)‖ ∂ν) μ := by
  have hm : Measurable fun x => ∫ y, ‖M (s x, y)‖ ∂ν := by
    have : StronglyMeasurable (Function.uncurry fun (r : ℝ) (y : Y) => ‖M (r, y)‖) :=
      (hM.norm.comp (measurable_fst.prodMk measurable_snd)).stronglyMeasurable
    exact (this.integral_prod_right.measurable).comp hs
  refine Integrable.mono' (hA.norm.mul_const (max CT 0)) ((hAm.norm.mul hm).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left ((hMb (s x)).trans (le_max_left _ _)) (norm_nonneg _)

theorem sumBound_aux {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] (A : X → ℂ) (s : X → ℝ) (M : ι → ℝ × Y → ℂ) (hA : Integrable A μ) (hAm : Measurable A)
    (hs : Measurable s) (hM : ∀ i, Measurable (M i)) {CT : ℝ}
    (hSum : ∀ r, Summable fun i => ∫ y, ‖M i (r, y)‖ ∂ν) (hTot : ∀ r, ∑' i, ∫ y, ‖M i (r, y)‖ ∂ν ≤ CT) :
    Summable (fun i => ∫ x, ‖A x‖ * ∫ y, ‖M i (s x, y)‖ ∂ν ∂μ) ∧
      ∑' i, ∫ x, ‖A x‖ * ∫ y, ‖M i (s x, y)‖ ∂ν ∂μ ≤ CT * ∫ x, ‖A x‖ ∂μ := by
  have hb : ∀ i r, ∫ y, ‖M i (r, y)‖ ∂ν ≤ CT := fun i r =>
    ((hSum r).le_tsum i (fun j _ => integral_nonneg fun _ => norm_nonneg _)).trans (hTot r)
  have hI := fun i => intI_aux A s (M i) hA hAm hs (hM i) (hb i)
  have hnn : ∀ i, 0 ≤ ∫ x, ‖A x‖ * ∫ y, ‖M i (s x, y)‖ ∂ν ∂μ := fun i =>
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have hfin : ∀ u : Finset ι, ∑ i ∈ u, ∫ x, ‖A x‖ * ∫ y, ‖M i (s x, y)‖ ∂ν ∂μ ≤ CT * ∫ x, ‖A x‖ ∂μ := by
    intro u
    rw [← integral_finsetSum _ (fun i _ => hI i), ← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun i _ => hI i) (hA.norm.const_mul CT) fun x => ?_
    rw [← Finset.mul_sum, mul_comm CT]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans ((hSum (s x)).sum_le_tsum u (fun i _ => integral_nonneg fun _ => norm_nonneg _)) (hTot (s x))
  exact ⟨summable_of_sum_le hnn hfin, (summable_of_sum_le hnn hfin).tsum_le_of_sum_le hfin⟩


section Glue
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (L : ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d)
  (ΨU : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
  (ΨS : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
  (ΨT : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)

theorem measurable_vec3 (t1 t2 : ℝ) : Measurable fun s : ℝ => (![s, t1, t2] : Fin 3 → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i <;> simp
  exact measurable_id

include hS hT hi hU in
/-- **Absolute convergence of the glued summands** from the S-side bound `SAbs`, the uniform T-side bound `UAbs` and measurability;
the total is at most `CS * CT`. -/
theorem glueAbs_of_bounds (hfac : GlueFactors RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT)
    (hlocS : ∀ x (u u' : GBranch G.tree → ℝ), (∀ v ∈ S, u v = u' v) → ΨS x u = ΨS x u')
    (hlocT : ∀ x t' (u u' : GBranch G.tree → ℝ), (∀ v ∈ T, u v = u' v) → ΨT x t' u = ΨT x t' u')
    (hmS : ∀ x, Measurable (ΨS x))
    (hmT : ∀ x, Measurable fun z : (Fin 3 → ℝ) × (GBranch G.tree → ℝ) => ΨT x z.1 z.2)
    {CS CT : ℝ} (hCT : 0 ≤ CT) (hSa : SAbs RS L base ΨS CS) (hTa : UAbs RT L base ΨT CT) :
    GlueAbsConv RU RS RT L base t0 t1 t2 e f g h ΨU ∧
      ∑' p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ ≤ CS * CT := by
  obtain ⟨E, hE, hf⟩ := glue_prodForm hS hT hi hU RU RS RT L base t0 t1 t2 e f g h ΨU ΨS ΨT hfac hlocS hlocT
  obtain ⟨hSi, hSs, hSb⟩ := hSa ![t0, t1, t2] e f
  have hmT' : ∀ x, Measurable fun z : ℝ × CLInternalTime RT =>
      ΨT x ![z.1, t1, t2] (clLocalClock RT ![z.1, t1, t2] z.2) := fun x =>
    (hmT x).comp (((measurable_vec3 t1 t2).comp measurable_fst).prodMk (measurable_clock_fun RT t1 t2))
  -- per summand data
  have hP : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      Integrable (fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p) ∧
      ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ =
        ∫ σ : CLInternalTime RS, ‖ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ)‖ *
          ∫ ρ : CLInternalTime RT, ‖ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] σ b, t1, t2] ρ)‖ := by
    intro p
    have hA := hSi p.1
    have hAm : Measurable fun σ : CLInternalTime RS => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ) :=
      (hmS _).comp (measurable_clock_fixed_fun RS _)
    have hs : Measurable fun σ : CLInternalTime RS => clLocalClock RS ![t0, t1, t2] σ b := measurable_clock_fixed RS _ b
    have hMi := fun r => (hTa ![r, t1, t2] (bdT RT L base p.1.1 g h)).1 p.2
    have hMs := fun r => (hTa ![r, t1, t2] (bdT RT L base p.1.1 g h)).2.1
    have hMt := fun r => (hTa ![r, t1, t2] (bdT RT L base p.1.1 g h)).2.2
    have hMb : ∀ r, ∫ ρ : CLInternalTime RT, ‖ΨT (clExtendIndices RT p.2.1) ![r, t1, t2]
        (clLocalClock RT ![r, t1, t2] ρ)‖ ≤ CT := fun r =>
      ((hMs r).le_tsum p.2 (fun j _ => integral_nonneg fun _ => norm_nonneg _)).trans (hMt r)
    obtain ⟨hI, hv⟩ := prodInt_aux (μ := (volume : Measure (CLInternalTime RS))) (ν := (volume : Measure (CLInternalTime RT)))
      (fun σ => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] σ)) (fun σ => clLocalClock RS ![t0, t1, t2] σ b)
      (fun z : ℝ × CLInternalTime RT => ΨT (clExtendIndices RT p.2.1) ![z.1, t1, t2] (clLocalClock RT ![z.1, t1, t2] z.2))
      hA hAm hs (hmT' _) hMi hMb
    have hfE : (fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p) ∘ E =
        fun z : CLInternalTime RS × CLInternalTime RT => ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] z.1) *
          ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] z.1 b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] z.1 b, t1, t2] z.2) := by
      funext z; exact hf p z.1 z.2
    refine ⟨(hE.integrable_comp_emb E.measurableEmbedding).mp (by rw [hfE]; exact hI), ?_⟩
    rw [← hE.integral_comp' (fun τ => ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖)]
    have : ∀ z : CLInternalTime RS × CLInternalTime RT,
        ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p (E z)‖ = ‖ΨS p.1.1 (clLocalClock RS ![t0, t1, t2] z.1) *
          ΨT (clExtendIndices RT p.2.1) ![clLocalClock RS ![t0, t1, t2] z.1 b, t1, t2]
            (clLocalClock RT ![clLocalClock RS ![t0, t1, t2] z.1 b, t1, t2] z.2)‖ := fun z => congrArg norm (congrFun hfE z)
    refine (integral_congr_ae (Filter.Eventually.of_forall this)).trans hv
  -- per upper decoration
  have hX : ∀ xS : ExtS RS L base e f,
      Summable (fun κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h) =>
        ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU ⟨xS, κ⟩ τ‖) ∧
      ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU ⟨xS, κ⟩ τ‖ ≤
        CT * ∫ σ : CLInternalTime RS, ‖ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ)‖ := by
    intro xS
    have hA := hSi xS
    have hAm : Measurable fun σ : CLInternalTime RS => ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ) :=
      (hmS _).comp (measurable_clock_fixed_fun RS _)
    have hs : Measurable fun σ : CLInternalTime RS => clLocalClock RS ![t0, t1, t2] σ b := measurable_clock_fixed RS _ b
    have := sumBound_aux (μ := (volume : Measure (CLInternalTime RS))) (ν := (volume : Measure (CLInternalTime RT)))
      (fun σ => ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ)) (fun σ => clLocalClock RS ![t0, t1, t2] σ b)
      (fun (κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (z : ℝ × CLInternalTime RT) =>
        ΨT (clExtendIndices RT κ.1) ![z.1, t1, t2] (clLocalClock RT ![z.1, t1, t2] z.2))
      hA hAm hs (fun κ => hmT' _) (CT := CT)
      (fun r => (hTa ![r, t1, t2] (bdT RT L base xS.1 g h)).2.1)
      (fun r => (hTa ![r, t1, t2] (bdT RT L base xS.1 g h)).2.2)
    simp_rw [fun κ => (hP ⟨xS, κ⟩).2]
    exact this
  have hnn : ∀ p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
      0 ≤ ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ := fun p => integral_nonneg fun _ => norm_nonneg _
  have hN : ∀ xS : ExtS RS L base e f, 0 ≤ ∫ σ : CLInternalTime RS, ‖ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ)‖ :=
    fun xS => integral_nonneg fun _ => norm_nonneg _
  have hSumX : Summable fun xS : ExtS RS L base e f =>
      ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
        ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU ⟨xS, κ⟩ τ‖ :=
    Summable.of_nonneg_of_le (fun xS => tsum_nonneg fun κ => hnn ⟨xS, κ⟩) (fun xS => (hX xS).2)
      (hSs.mul_left CT)
  have hsum : Summable fun p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h) =>
      ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU p τ‖ :=
    (summable_sigma_of_nonneg hnn).mpr ⟨fun xS => (hX xS).1, hSumX⟩
  refine ⟨⟨fun p => (hP p).1, hsum⟩, ?_⟩
  rw [hsum.tsum_sigma']
  · calc ∑' xS : ExtS RS L base e f, ∑' κ : CLLocalDecoration RT L base (bdT RT L base xS.1 g h),
          ∫ τ, ‖fGlue RU RS RT L base t0 t1 t2 e f g h ΨU ⟨xS, κ⟩ τ‖
        ≤ ∑' xS : ExtS RS L base e f, CT * ∫ σ : CLInternalTime RS, ‖ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ)‖ :=
          hSumX.tsum_le_tsum (fun xS => (hX xS).2) (hSs.mul_left CT)
      _ = CT * ∑' xS : ExtS RS L base e f, ∫ σ : CLInternalTime RS, ‖ΨS xS.1 (clLocalClock RS ![t0, t1, t2] σ)‖ :=
          tsum_mul_left
      _ ≤ CS * CT := by
          rw [mul_comm CS CT]
          exact mul_le_mul_of_nonneg_left hSb hCT
  · exact fun xS => (hX xS).1

end Glue

end WaveTurbulence.VineEstS5C
