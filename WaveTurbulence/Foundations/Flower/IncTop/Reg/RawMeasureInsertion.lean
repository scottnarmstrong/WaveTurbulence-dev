/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MeasureInsertion

/-! Ported by source from C2-B-TOP `Cut2BReg.RawMeasureInsertion` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Exact Fourier insertion in the normalized raw clock integral

TARGET (incohproof2), NOTES §3.2. Absolute lattice convergence, proved from
profile norms, suffices. The source domain may contain either root cut.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The normalized raw integral with its internal Fourier-measure multiplier. -/
@[expose] def MomentumTreeData.weightedSourceIntegral {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, (MomentumTreeData.weightedSourceTimeIntegrand (P := P)) F ζ L γ δ Q f k t

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact raw-kernel insertion, conditional only on absolute lattice convergence.
The eventual couple/tree applications discharge convergence from their profile bounds. -/
theorem MomentumTreeData.weightedSourceIntegral_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    (MomentumTreeData.weightedSourceIntegral (P := P)) F ζ L γ δ Q I f k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) I f k ∂F.μ := by
  have hvol : volume I < ⊤ :=
    (measure_mono hbox).trans_lt (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  let : IsFiniteMeasure (volume.restrict I) := ⟨by simpa only [Measure.restrict_apply_univ] using hvol⟩
  let G := fun a t => (MomentumTreeData.sourceTimeIntegrandSpatial (P := P)) ζ L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) f k t
  let C := ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
    ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖
  have hG : StronglyMeasurable (fun z : α × (Fin n → Fin 2 → ℝ) => G z.1 z.2) := by
    apply Measurable.stronglyMeasurable
    unfold G sourceTimeIntegrandSpatial
    apply Measurable.tsum
    intro p
    have hm := (continuous_sourceTemporalPhaseSpatial_frequency L γ δ Q p).measurable.comp
      ((F.frequency_measurable.comp measurable_fst).prodMk measurable_snd)
    exact hm.mul_const _
  have hb (a : α) (t : Fin n → Fin 2 → ℝ) : ‖G a t‖ ≤ C :=
    (MomentumTreeData.norm_sourceTimeIntegrandSpatial_le_of_summable (P := P)) ζ L γ δ _ f k hs t
  have hi : Integrable (fun z : α × (Fin n → Fin 2 → ℝ) => F.amplitude z.1 * G z.1 z.2)
      (F.μ.prod (volume.restrict I)) := by
    apply (F.amplitude_integrable.norm.mul_prod
      (integrable_const C : Integrable (fun _ : Fin n → Fin 2 → ℝ => C) (volume.restrict I))).mono'
      (F.amplitude_integrable.aestronglyMeasurable.comp_fst.mul hG.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖F.amplitude z.1 * G z.1 z.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb z.1 z.2) (norm_nonneg _))
  unfold weightedSourceIntegral
  simp_rw [(MomentumTreeData.weightedSourceTimeIntegrand_eq_integral_of_summable (P := P)) F ζ L γ δ Q f k hs]
  rw [← integral_integral_swap hi, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only [G, sourceIntegralSpatial]
  rw [integral_const_mul]
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Raw weighted regular couple, with its actual external clock cut. -/
@[expose] def MomentumTreeData.weightedSourceCoupleKernel {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegral (P := P)) F ζ L γ δ Q (I ∩ R.rootCut t) f k

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Raw weighted regular tree, with its actual external causal clock cut. -/
@[expose] def MomentumTreeData.weightedSourceTreeKernel {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegral (P := P)) F ζ L γ δ Q (I ∩ R.causalRootCut t) f k

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact internally weighted couple insertion; source absolute convergence is the only
conditional premise and is independently available from profile bounds. -/
theorem MomentumTreeData.weightedSourceCoupleKernel_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) (t : Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceCoupleKernel (P := P)) F ζ R L γ δ Q I f t k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceCoupleKernelSpatial (P := P)) ζ R L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) I f t k ∂F.μ :=
  (MomentumTreeData.weightedSourceIntegral_eq_integral_of_summable (P := P)) F ζ L γ δ Q (I ∩ R.rootCut t)
    (inter_subset_left.trans hbox) f k hs

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact internally weighted tree insertion with the original causal clock domain. -/
theorem MomentumTreeData.weightedSourceTreeKernel_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) (t : Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceTreeKernel (P := P)) F ζ R L γ δ Q I f t k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) I f t k ∂F.μ :=
  (MomentumTreeData.weightedSourceIntegral_eq_integral_of_summable (P := P)) F ζ L γ δ Q (I ∩ R.causalRootCut t)
    (inter_subset_left.trans hbox) f k hs

end WaveTurbulence.Flower.IncTop