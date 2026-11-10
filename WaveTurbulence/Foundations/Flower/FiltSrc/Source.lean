/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Phase
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawMeasureInsertion
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootInputSourceIdentity
public import WaveTurbulence.Foundations.Incoh.OneClockCouple

/-! # D5b-1 FILT-SRC: the filtered raw and weighted source operators (D5B-MAP K2–K3)

Twins (filtered phase `sourceTemporalPhaseSpatialFilt` / `sourceTemporalPhaseFilt`, multiplier `φ` after the links) of
INC-TOP's
- `Reg/RawSourceIntegral`: `sourceTimeIntegrandSpatial`, `sourceIntegralSpatial`;
- `Reg/RawCoupleAgreement`, `Reg/RawTreeAgreement`, `Top/CoupleRootRestriction` (definitions only):
  `sourceCoupleKernelSpatial`, `sourceTreeKernelSpatial`, `sourceOneClockKernelSpatial`, `weightedSourceOneClockKernel`;
- `Reg/RawModulation`: `norm_sourceTimeIntegrandSpatial_le_of_summable` (bound `Bφ ^ n · Σ‖w‖`);
- `Reg/MeasureInsertion`, `Reg/RawMeasureInsertion` (K2, K3: the star Fourier measure `F` is inserted exactly as
  before; its frequency moves only the link shifts, never `φ`);
- `Reg/RootInputSourceIdentity`.

Copied by source (sha256 in COPIED-SHA256SUMS); the only edits are the multiplier and, in every domination step, the
phase bound `1 → Bφ ^ n` (`‖φ i u‖ ≤ Bφ`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop
open Cut2A

/-! ### `Reg/RawSourceIntegral` and the kernel definitions -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered raw source lattice series (twin of `sourceTimeIntegrandSpatial`). -/
def MomentumTreeData.sourceTimeIntegrandSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t *
    ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered unlocalized normalized lattice/time source operator (twin of `sourceIntegralSpatial`). -/
def MomentumTreeData.sourceIntegralSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f k t

/-- The filtered raw couple with its root cut (twin of `sourceCoupleKernelSpatial`). -/
def MomentumTreeData.sourceCoupleKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ (I ∩ R.rootCut t) f k

/-- The filtered raw tree with its causal root cut (twin of `sourceTreeKernelSpatial`). -/
def MomentumTreeData.sourceTreeKernelSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ (I ∩ R.causalRootCut t) f k

/-- The filtered one-clock raw operator (twin of INC-TOP `Top/CoupleRootRestriction.sourceOneClockKernelSpatial`). -/
def sourceOneClockKernelSpatialFilt {d n m w : ℕ} (P : MomentumTreeData n m w) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ (I ∩ R.oneClockCut a (t a)) f k

/-! ### `Reg/RawModulation`: the character-independent bound -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Absolute lattice convergence gives a character-independent bound, with the filter bound `Bφ ^ n`. -/
theorem MomentumTreeData.norm_sourceTimeIntegrandSpatialFilt_le_of_summable {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖))
    (t : Fin n → Fin 2 → ℝ) :
    ‖(MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f k t‖ ≤
      Bφ ^ n * ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
  have hb (p : (Fin n × Fin 2) → Fin d → ℤ) :
      ‖sourceTemporalPhaseSpatialFilt L γ δ Q φ p t *
        ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))‖ ≤
      Bφ ^ n * ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖ := by
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_leSpatialFilt L γ δ Q φ hφ p t) (norm_nonneg _)
  have hs' := hs.mul_left (Bφ ^ n)
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    ((hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hb).tsum_le_tsum hb hs')

/-! ### `Reg/MeasureInsertion` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered weighted raw lattice sum (twin of `weightedSourceTimeIntegrand`). -/
def MomentumTreeData.weightedSourceTimeIntegrandFilt {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
    F.value (pairedLattice L p) * sourceTemporalPhaseFilt L γ δ Q φ p t *
      ((ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j))))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Filtered literal insertion before clock integration (twin of
`weightedSourceTimeIntegrand_eq_integral_of_summable`). -/
theorem MomentumTreeData.weightedSourceTimeIntegrandFilt_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {Bφ : ℝ}
    (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖))
    (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceTimeIntegrandFilt (P := P)) F ζ L γ δ Q φ f k t =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) φ f k t ∂F.μ := by
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    (ζ : ℂ) * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))
  let G := fun p a => F.amplitude a *
    (Real.fourierChar (inner ℝ (F.frequency a) (pairedLattice L p)) : ℂ) *
      (sourceTemporalPhaseFilt L γ δ Q φ p t * W p)
  have hi (p : (Fin n × Fin 2) → Fin d → ℤ) : Integrable (G p) F.μ :=
    (F.integrable_character (pairedLattice L p)).mul_const _
  have hn (p : (Fin n × Fin 2) → Fin d → ℤ) :
      (∫ a, ‖G p a‖ ∂F.μ) ≤ F.mass * (Bφ ^ n * ‖P.sourceLeafWeight f k
        (fun i j => latticePoint L (p (i, j)))‖) := by
    simp only [G, norm_mul, Circle.norm_coe, mul_one, W, one_mul,
      integral_mul_const, SpatialMeasure.mass]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_leFilt L γ δ Q φ hφ p t)
        (norm_nonneg _)) F.mass_nonneg
  have hsum : Summable (fun p => ∫ a, ‖G p a‖ ∂F.μ) :=
    ((hs.mul_left (Bφ ^ n)).mul_left F.mass).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  have he := (hasSum_integral_of_summable_integral_norm hi hsum).tsum_eq
  calc
    _ = ∑' p, ∫ a, G p a ∂F.μ := by
      apply tsum_congr
      intro p
      rw [integral_mul_const, ← SpatialMeasure.value]
      dsimp only [weightedSourceTimeIntegrandFilt, W]
      ring
    _ = ∫ a, ∑' p, G p a ∂F.μ := he
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro a
      dsimp only
      unfold sourceTimeIntegrandSpatialFilt
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      rw [sourceTemporalPhaseSpatialFilt_eq_character]
      dsimp only [G, W]
      ring

/-! ### `Reg/RawMeasureInsertion` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered normalized raw integral with its internal Fourier-measure multiplier. -/
def MomentumTreeData.weightedSourceIntegralFilt {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, (MomentumTreeData.weightedSourceTimeIntegrandFilt (P := P)) F ζ L γ δ Q φ f k t

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact filtered raw-kernel insertion, conditional only on absolute lattice convergence. -/
theorem MomentumTreeData.weightedSourceIntegralFilt_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {Bφ : ℝ}
    (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) :
    (MomentumTreeData.weightedSourceIntegralFilt (P := P)) F ζ L γ δ Q φ I f k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) φ I f k ∂F.μ := by
  have hvol : volume I < ⊤ :=
    (measure_mono hbox).trans_lt (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  let : IsFiniteMeasure (volume.restrict I) := ⟨by simpa only [Measure.restrict_apply_univ] using hvol⟩
  let G := fun a t => (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) φ f k t
  let C := Bφ ^ n * ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
    ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖
  have hG : StronglyMeasurable (fun z : α × (Fin n → Fin 2 → ℝ) => G z.1 z.2) := by
    apply Measurable.stronglyMeasurable
    unfold G sourceTimeIntegrandSpatialFilt
    apply Measurable.tsum
    intro p
    have hm := (continuous_sourceTemporalPhaseSpatialFilt_frequency L γ δ Q φ p).measurable.comp
      ((F.frequency_measurable.comp measurable_fst).prodMk measurable_snd)
    exact hm.mul_const _
  have hb (a : α) (t : Fin n → Fin 2 → ℝ) : ‖G a t‖ ≤ C :=
    (MomentumTreeData.norm_sourceTimeIntegrandSpatialFilt_le_of_summable (P := P)) ζ L γ δ _ φ hφ f k hs t
  have hi : Integrable (fun z : α × (Fin n → Fin 2 → ℝ) => F.amplitude z.1 * G z.1 z.2)
      (F.μ.prod (volume.restrict I)) := by
    apply (F.amplitude_integrable.norm.mul_prod
      (integrable_const C : Integrable (fun _ : Fin n → Fin 2 → ℝ => C) (volume.restrict I))).mono'
      (F.amplitude_integrable.aestronglyMeasurable.comp_fst.mul hG.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖F.amplitude z.1 * G z.1 z.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb z.1 z.2) (norm_nonneg _))
  unfold weightedSourceIntegralFilt
  simp_rw [(MomentumTreeData.weightedSourceTimeIntegrandFilt_eq_integral_of_summable (P := P))
    F ζ L γ δ Q φ hφ f k hs]
  rw [← integral_integral_swap hi, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only [G, sourceIntegralSpatialFilt]
  rw [integral_const_mul]
  ring

/-- Raw weighted filtered regular couple, with its actual external clock cut. -/
def MomentumTreeData.weightedSourceCoupleKernelFilt {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegralFilt (P := P)) F ζ L γ δ Q φ (I ∩ R.rootCut t) f k

/-- Raw weighted filtered regular tree, with its actual external causal clock cut. -/
def MomentumTreeData.weightedSourceTreeKernelFilt {d n m w : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegralFilt (P := P)) F ζ L γ δ Q φ (I ∩ R.causalRootCut t) f k

/-- The weighted filtered one-clock raw operator (twin of INC-TOP `weightedSourceOneClockKernel`). -/
def weightedSourceOneClockKernelFilt {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegralFilt (P := P)) F ζ L γ δ Q φ (I ∩ R.oneClockCut a (t a)) f k

/-- Exact internally weighted filtered couple insertion. -/
theorem MomentumTreeData.weightedSourceCoupleKernelFilt_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) (t : Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceCoupleKernelFilt (P := P)) F ζ R L γ δ Q φ I f t k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceCoupleKernelSpatialFilt (P := P)) ζ R L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) φ I f t k ∂F.μ :=
  (MomentumTreeData.weightedSourceIntegralFilt_eq_integral_of_summable (P := P)) F ζ L γ δ Q φ hφ
    (I ∩ R.rootCut t) (inter_subset_left.trans hbox) f k hs

/-- Exact internally weighted filtered tree insertion with the original causal clock domain. -/
theorem MomentumTreeData.weightedSourceTreeKernelFilt_eq_integral_of_summable
    {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (k : Mom d)
    (hs : Summable (fun p : (Fin n × Fin 2) → Fin d → ℤ =>
      ‖P.sourceLeafWeight f k (fun i j => latticePoint L (p (i, j)))‖)) (t : Fin 2 → ℝ) :
    (MomentumTreeData.weightedSourceTreeKernelFilt (P := P)) F ζ R L γ δ Q φ I f t k =
      ∫ a, F.amplitude a * (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ
        (spatialFrequencyLinks Q (F.frequency a)) φ I f t k ∂F.μ :=
  (MomentumTreeData.weightedSourceIntegralFilt_eq_integral_of_summable (P := P)) F ζ L γ δ Q φ hφ
    (I ∩ R.causalRootCut t) (inter_subset_left.trans hbox) f k hs

/-! ### `Reg/RootInputSourceIdentity` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered raw lattice integrand retains the appended root factor. -/
theorem MomentumTreeData.sourceTimeIntegrand_withRootInputSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P.withRootInput)) ζ L γ δ Q φ
        (appendRootInputSpatial f h) k t =
      (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f k t * h k := by
  unfold MomentumTreeData.sourceTimeIntegrandSpatialFilt
  rw [← tsum_mul_right]
  apply tsum_congr
  intro p
  rw [(MomentumTreeData.sourceLeafWeight_withRootInputSpatial (P := P))]
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered source integral is multiplied by the appended root value. -/
theorem MomentumTreeData.sourceIntegral_withRootInputSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ) (k : Mom d) :
    (MomentumTreeData.sourceIntegralSpatialFilt (P := P.withRootInput)) ζ L γ δ Q φ I
        (appendRootInputSpatial f h) k =
      (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f k * h k := by
  simp only [MomentumTreeData.sourceIntegralSpatialFilt,
    (MomentumTreeData.sourceTimeIntegrand_withRootInputSpatialFilt (P := P))]
  rw [integral_mul_const]
  ring

/-- The filtered causal tree source kernel has exactly the same root factor. -/
theorem MomentumTreeData.sourceTreeKernel_withRootInputSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (h : Mom d → ℂ)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P.withRootInput)) ζ R L γ δ Q φ I
        (appendRootInputSpatial f h) t k =
      (MomentumTreeData.sourceTreeKernelSpatialFilt (P := P)) ζ R L γ δ Q φ I f t k * h k :=
  (MomentumTreeData.sourceIntegral_withRootInputSpatialFilt (P := P)) ζ L γ δ Q φ (I ∩ R.causalRootCut t) f h k

/-! ### `φ ≡ 1` is INC-TOP's operator -/

end WaveTurbulence.Flower.FiltSrc
