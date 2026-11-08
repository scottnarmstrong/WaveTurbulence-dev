/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Cells
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceLinkKernelIdentity
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralLinkContinuity

/-! # D5b-1 FILT-SRC: the filtered spectral link identity (D5B-MAP K4, K5 continuity)

Twins (multiplier `φ` after the links) of INC-TOP's
- `Reg/SpectralArraySummand`: `sourceTemporalPhase_mul_cutoff_mul_characterSpatial` (now landing in
  `linkArraySummandFilt`);
- `Reg/SpectralLinkIntegral`: `spectral_link_integral_eqSpatial`;
- `Reg/SourceLinkKernelIdentity`: `localizedSourceIntegral_eq_linkKernelMixtureSpatial`, whose right side is the
  **interface object** `normalizedLinkIntegralFilt` (`Link.lean`);
- `Reg/SpectralLinkContinuity`: `continuous_spectral_linkTimeFactorSpatial` (from D5a
  `continuous_filtLinkLatticeSum_shifts`).

K4: `φ_i` depends only on `p (i, ·)`, so it rides in factor `i` of the finite-support factorization; the spectral links
move centers and shifts only, never the link index. Copied by source (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop

/-- The filtered array summand is the unfiltered one times the array filter factor. -/
theorem linkArraySummandFilt_eq {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (t : Fin n → Fin 2 → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    linkArraySummandFilt L γ δ Q φ t p = linkArraySummand L γ δ Q t p * arrayFiltWeight L φ p := by
  rw [linkArraySummandFilt, linkArraySummand, arrayFiltWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-! ### `Reg/SpectralArraySummand` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered source time factor times cutoff and link Fourier phase is the filtered analytic link-array summand
with computed centers and shifts. -/
theorem MomentumTreeData.sourceTemporalPhase_mul_cutoff_mul_characterSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * linkArrayCutoff z (latticeMomentumArray L p) *
      (∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
        (latticePoint L (p q))) : ℂ)) =
      linkArraySummandFilt L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ t p := by
  rw [linkArraySummandFilt_eq, ← (MomentumTreeData.sourceTemporalPhase_mul_cutoff_mul_characterSpatial (P := P))
    L γ δ Q z ξ p t, sourceTemporalPhaseSpatialFilt_eq]
  ring

/-! ### `Reg/SpectralLinkIntegral` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The filtered temporal phase integral with the computed Fourier shifts is the filtered link-product integral. -/
theorem MomentumTreeData.spectral_link_integral_eqSpatialFilt {d n m w : ℕ} (P : MomentumTreeData n m w)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (hL : 0 < L)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ((∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) *
        linkArrayCutoff z (latticeMomentumArray L p)) *
        ∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
          (latticePoint L (p q))) : ℂ)) =
      ∫ t in I, ∏ i, filtLinkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ i)
        (φ i) (t i) := by
  classical
  let S := (finite_linkCellLatticeSet hL z).toFinset
  let b := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    linkArrayCutoff z (latticeMomentumArray L p) *
      ∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
        (latticePoint L (p q))) : ℂ)
  have hb (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) : b p = 0 := by
    dsimp only [b]
    rw [linkArrayCutoff_eq_zero_of_not_mem L z p
      (by simpa only [S, Set.Finite.mem_toFinset] using hp), zero_mul]
  have hs (t : Fin n → Fin 2 → ℝ) :
      (∑' p, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * b p) =
        ∑ p ∈ S, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * b p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hb p hp, mul_zero])
  have hts : (∑' p, (∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) * b p) =
      ∑ p ∈ S, (∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) * b p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hb p hp, mul_zero])
  calc
    _ = ∑' p, (∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) * b p := by
      apply tsum_congr
      intro p
      exact mul_assoc _ _ _
    _ = ∫ t in I, ∑' p, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t * b p := by
      rw [hts]
      simp_rw [hs]
      rw [integral_finsetSum S (fun p _ =>
        (integrableOn_sourceTemporalPhaseSpatialFilt L γ δ Q φ p hI).mul_const (b p))]
      simp only [integral_mul_const]
    _ = ∫ t in I, ∑' p, linkArraySummandFilt L γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ t p := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      apply tsum_congr
      intro p
      exact (mul_assoc _ _ _).symm.trans
        ((MomentumTreeData.sourceTemporalPhase_mul_cutoff_mul_characterSpatialFilt (P := P)) L γ δ Q φ z ξ p t)
    _ = _ := by simp_rw [tsum_linkArraySummandFilt hL]

/-! ### `Reg/SourceLinkKernelIdentity` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- **K4, the filtered source/link-kernel identity** (TARGET (incohproof8–10) with filters): the localized filtered
source operator is the spectral mixture of the filtered normalized link integrals `normalizedLinkIntegralFilt`. -/
theorem MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatialFilt {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    (MomentumTreeData.localizedSourceIntegralSpatialFilt (P := P)) ζ L γ δ Q φ I f c z k =
      ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ *
          normalizedLinkIntegralFilt L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) φ I := by
  rw [(MomentumTreeData.localizedSourceIntegral_eq_spectralIntegralSpatialFilt (P := P))
    ζ L γ δ Q φ I hI f c z hL hK hB h k, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  have hs : (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ((∫ t in I, sourceTemporalPhaseSpatialFilt L γ δ Q φ p t) *
        linkArrayCutoff z (latticeMomentumArray L p)) *
        P.localizedSourceSpectralDensity ζ f c z k (fun i j => latticePoint L (p (i, j))) ξ) =
      (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c z k ξ *
        ∫ t in I, ∏ i, filtLinkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ i)
          (φ i) (t i) := by
    rw [← (MomentumTreeData.spectral_link_integral_eqSpatialFilt (P := P)) L γ δ Q φ hL z ξ I hI,
      ← tsum_mul_left]
    apply tsum_congr
    intro p
    rw [P.localizedSourceSpectralDensity_eq_root_link_phase ζ f c z k
      (fun i j => latticePoint L (p (i, j))) ξ]
    unfold MomentumTreeData.sourceSpectralAmplitudeSpatial
    ring
  rw [hs]
  unfold normalizedLinkIntegralFilt
  ring

/-! ### `Reg/SpectralLinkContinuity` -/

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint continuity of the filtered link factor in time and all Fourier variables. -/
theorem MomentumTreeData.continuous_spectral_linkTimeFactorSpatialFilt {d n m w : ℕ}
    (P : MomentumTreeData n m w) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (z : (Fin n × Fin 2) → Fin d → ℤ) (i : Fin n) :
    Continuous (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      filtLinkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i) (φ i) v.1) :=
  continuous_filtLinkLatticeSum_shifts hL (halfCellCenter (z (i, 0))) (halfCellCenter (z (i, 1))) (φ i)
    (s := fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      (((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (v.1 0 - v.1 1))
    (ξ := fun v => P.spectralShift v.2 (some (i, 0)) + (Q i).leftShift)
    (ζ := fun v => P.spectralShift v.2 (some (i, 1)) + (Q i).rightShift)
    (by fun_prop) (by fun_prop) (by fun_prop)

end WaveTurbulence.Flower.FiltSrc
