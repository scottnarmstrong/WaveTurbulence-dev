/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Source
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceRootMaskAgreement

/-! # D5b-1 FILT-SRC: filtered source cells and localization (D5B-MAP K4, first half)

Twins (multiplier `φ` after the links) of INC-TOP's
- `Reg/SourceCellTimeIntegrand`: `sourceCellTimeIntegrandSpatial`, its continuity and absolute bound;
- `Reg/RawSourceCellSeries`: `sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatial`;
- `Reg/RawSourceCellIntegral`: `sourceIntegral_eq_tsum_localizedSourceIntegral(_of_cover_at)Spatial`;
- `Reg/LocalizedSourceIntegral`: `localizedSourceIntegralSpatial`, `localizedSourceIntegral_eq_spectralIntegralSpatial`;
- `Reg/SourceRootMaskAgreement`: `sourceRootMask_mul_localizedSourceIntegralSpatial`.

Copied by source (sha256 in COPIED-SHA256SUMS). Edits: the multiplier; the phase bound `1 → Bφ ^ n` in the absolute
bounds (`‖φ i u‖ ≤ Bφ`); the cell continuity is proved from the finite lattice support alone (no bound needed). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop

/-! ### `Reg/SourceCellTimeIntegrand` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered signed time series of one actual source cell. -/
def MomentumTreeData.sourceCellTimeIntegrandSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  ∑' p : (Fin n × Fin 2) → Fin d → ℤ, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t *
    ((ζ : ℂ) * P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Every filtered cell time series is continuous, by its proved finite lattice support. -/
theorem MomentumTreeData.continuous_sourceCellTimeIntegrandSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) :
    Continuous ((MomentumTreeData.sourceCellTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f S k u) := by
  let T := ((MomentumTreeData.finite_support_sourceCellWeight_latticeSpatial (P := P)) hL f S k u).toFinset
  have he : (MomentumTreeData.sourceCellTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f S k u =
      fun t => ∑ p ∈ T, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t *
        ((ζ : ℂ) * P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) := by
    funext t
    apply tsum_eq_sum
    intro p hp
    have hz : P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u = 0 := by
      by_contra hn
      exact hp (by simpa only [T, Set.Finite.mem_toFinset, Function.mem_support] using hn)
    rw [hz, mul_zero, mul_zero]
  rw [he]
  exact continuous_finsetSum _ (fun p _ =>
    (continuous_sourceTemporalPhaseSpatialFilt L γ δ Q φ p).mul continuous_const)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- A clock-independent absolute bound for every filtered source cell time series. -/
theorem MomentumTreeData.enorm_sourceCellTimeIntegrand_leSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) (t : Fin n → Fin 2 → ℝ) :
    ‖(MomentumTreeData.sourceCellTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f S k u t‖ₑ ≤
      ENNReal.ofReal (Bφ ^ n) * ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ := by
  apply enorm_tsum_le_tsum_enorm.trans
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro p
  have hφp : ‖sourceTemporalPhaseSpatialFilt L γ δ Q φ p t‖ₑ ≤ ENNReal.ofReal (Bφ ^ n) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_sourceTemporalPhase_leSpatialFilt L γ δ Q φ hφ p t)
  have hζ : ‖(ζ : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
  rw [enorm_mul, enorm_mul, hζ, one_mul]
  exact mul_le_mul' hφp le_rfl

/-! ### `Reg/RawSourceCellSeries` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact filtered source lattice/cell rearrangement from the proved absolute source majorant. -/
theorem MomentumTreeData.sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (t : Fin n → Fin 2 → ℝ) :
    (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f k t =
      ∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * ((ζ : ℂ) *
          P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) := by
  have hn : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i, j))) q.1‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    rw [ENNReal.tsum_prod']
    exact ((MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P))
      f S hS hL hK hM hB h k).ne
  have hs : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      sourceTemporalPhaseSpatialFilt L γ δ Q φ q.2 t * ((ζ : ℂ) *
        P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i, j))) q.1)) := by
    apply Summable.of_norm_bounded (hn.mul_left (Bφ ^ n))
    intro q
    simp only [norm_mul, Circle.norm_coe, one_mul]
    exact mul_le_mul_of_nonneg_right (norm_sourceTemporalPhase_leSpatialFilt L γ δ Q φ hφ q.2 t)
      (norm_nonneg _)
  calc
    _ = ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∑' u : SourceCellIndex S,
        sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * ((ζ : ℂ) *
          P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u) := by
      unfold sourceTimeIntegrandSpatialFilt
      apply tsum_congr
      intro p
      simp_rw [← mul_assoc]
      rw [tsum_mul_left]
      rw [(P.hasSum_sourceCellWeight_of_cover_at f S k (fun i j => latticePoint L (p (i, j)))
        (fun c => hcover c _)).tsum_eq]
    _ = _ := hs.tsum_comm

/-! ### `Reg/LocalizedSourceIntegral` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered normalized localized source operator on a source time domain. -/
def MomentumTreeData.localizedSourceIntegralSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) (k : Mom d) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * ((ζ : ℂ) * P.localizedLeafWeight f c k
        (fun i j => latticePoint L (p (i, j))) * halfCellArrayWeight z (latticeMomentumArray L p))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact filtered source identity after both lattice and time exchange with the actual spectral density. -/
theorem MomentumTreeData.localizedSourceIntegral_eq_spectralIntegralSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f c z k =
      ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
        ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
          ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
            ((∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) *
              linkArrayCutoff z (latticeMomentumArray L p)) *
              P.localizedSourceSpectralDensity ζ f c z k
                (fun i j => latticePoint L (p (i, j))) ξ := by
  classical
  let W := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    (ζ : ℂ) * P.localizedLeafWeight f c k (fun i j => latticePoint L (p (i, j))) *
      halfCellArrayWeight z (latticeMomentumArray L p)
  let S := (finite_linkCellLatticeSet hL z).toFinset
  have hW (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) : W p = 0 := by
    have hz : halfCellArrayWeight z (latticeMomentumArray L p) = 0 := by
      by_contra hn
      apply hp
      simpa only [S, Set.Finite.mem_toFinset] using
        mem_linkCellLatticeSet_of_halfCellArrayWeight_ne_zero L z p hn
    exact mul_eq_zero_of_right _ hz
  have hs (t : Fin n → Fin 2 → ℝ) :
      (∑' p, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * W p) =
        ∑ p ∈ S, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * W p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hW p hp, mul_zero])
  unfold localizedSourceIntegralSpatialFilt
  congr 1
  change (∫ t in I, ∑' p, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * W p) = _
  simp_rw [hs]
  rw [integral_finsetSum S (fun p _ =>
    (integrableOn_sourceTemporalPhaseSpatialFilt L γ δ Q φ p hI).mul_const (W p))]
  simp_rw [integral_mul_const]
  have ht : (∑' p, (∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) * W p) =
      ∑ p ∈ S, (∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) * W p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hW p hp, mul_zero])
  rw [← ht]
  exact P.localized_lattice_sum_eq_spectralIntegral ζ f c z hL hK hB h k
    (fun p => ∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t)

/-! ### `Reg/RawSourceCellIntegral` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered normalized source operator is exactly its countable smooth localization. -/
theorem MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegral_of_cover_atSpatialFilt
    {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f k = ∑' u : SourceCellIndex S,
      (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f u.1 u.2.val k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hvol : volume I < ⊤ := (measure_mono hI).trans_lt
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).measure_lt_top
  have hmass := (MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_lt_topSpatial (P := P))
    f S hS hL hK hM hB h k
  have hsum : (∑' u : SourceCellIndex S, ∫⁻ t in I,
      ‖(MomentumTreeData.sourceCellTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f S k u t‖ₑ) < ⊤ := by
    calc
      _ ≤ ∑' u : SourceCellIndex S, ENNReal.ofReal (Bφ ^ n) *
          (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
            ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I := by
        apply ENNReal.tsum_le_tsum
        intro u
        apply (lintegral_mono (fun t => (MomentumTreeData.enorm_sourceCellTimeIntegrand_leSpatialFilt (P := P))
          ζ L γ δ Q φ hφ f S k u t)).trans_eq
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ = ENNReal.ofReal (Bφ ^ n) * (∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
          ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) * volume I := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass) hvol
  have he : (MomentumTreeData.sourceTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f k =
      fun t => ∑' u : SourceCellIndex S,
        (MomentumTreeData.sourceCellTimeIntegrandSpatialFilt (P := P)) ζ L γ δ Q φ f S k u t := by
    funext t
    exact (MomentumTreeData.sourceTimeIntegrand_eq_tsum_cells_of_cover_atSpatialFilt (P := P))
      ζ L γ δ Q φ hφ f S k hcover hS hL hK hM hB h t
  unfold sourceIntegralSpatialFilt
  rw [he, integral_tsum (fun u =>
    ((MomentumTreeData.continuous_sourceCellTimeIntegrandSpatialFilt (P := P)) ζ hLp γ δ Q φ f S k u
      ).aestronglyMeasurable) hsum.ne,
    ← tsum_mul_left]
  apply tsum_congr
  intro u
  unfold localizedSourceIntegralSpatialFilt
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold sourceCellTimeIntegrandSpatialFilt
  apply tsum_congr
  intro p
  unfold sourceCellWeight latticeMomentumArray
  ring

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Compatibility form for a cover uniform in every root momentum. -/
theorem MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) {Bφ : ℝ} (hφ : ∀ i u, ‖φ i u‖ ≤ Bφ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.sourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f k = ∑' u : SourceCellIndex S,
      (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f u.1 u.2.val k :=
  (MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegral_of_cover_atSpatialFilt (P := P))
    ζ L γ δ Q φ hφ I hI f S k (fun c x => hcover c k x) hS hL hK hM hB h

/-! ### `Reg/SourceRootMaskAgreement` -/

open WaveTurbulence.Incoh.RootInputCoordinates in
/-- The smooth root mask changes none of the filtered localized source operators. -/
theorem RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatialFilt {d n m w : ℕ}
    {P : MomentumTreeData n m w} (C : RootInputCoordinates P)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (k : Mom d) :
    sourceRootMask c k * (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f c z k =
      (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f c z k := by
  by_cases hm : sourceRootMask c k = 1
  · rw [hm, one_mul]
  · have hz (x : Fin n → Fin 2 → Mom d) : P.localizedLeafWeight f c k x = 0 := by
      have hc : P.inputCellWeight c k x = 0 := by
        by_contra hn
        exact hm (C.sourceRootMask_eq_one c k x hn)
      simp only [P.localizedLeafWeight_eq, hc, mul_zero]
    have hi : (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f c z k = 0 := by
      simp only [MomentumTreeData.localizedSourceIntegralSpatialFilt, hz, mul_zero, zero_mul, tsum_zero,
        integral_zero]
    rw [hi, mul_zero]

/-! ### `φ ≡ 1` is INC-TOP's operator -/

theorem MomentumTreeData.localizedSourceIntegralSpatialFilt_one {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) (k : Mom d) :
    (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q (fun _ _ => 1) I f c z k =
      (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q I f c z k := by
  simp only [MomentumTreeData.localizedSourceIntegralSpatialFilt, MomentumTreeData.localizedSourceIntegralSpatial,
    sourceTemporalPhaseSpatialFilt_one]

end WaveTurbulence.Flower.FiltSrc
