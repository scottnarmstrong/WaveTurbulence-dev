/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedTreeExtension
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeLatticeConvergence
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawMeasureInsertion
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.PointwiseProduct

/-! Ported by source from C2-B-TOP `Cut2BReg.WeightedTreeAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Pointwise agreement of the Fourier extension and internally weighted raw tree -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Actual root partition amplitudes are integrable at every external root momentum. -/
theorem MomentumTreeData.integrable_treeRootAmplitudeSum
    {d n m w K M : ℕ} (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) :
    Integrable (rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k) (sourceCellMeasure S) := by
  let A := (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S
  have hi (q : Fin d → ℤ) : Integrable (A q k) (sourceCellMeasure S) := by
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
    exact ((MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P.withRootInput)) ζ
      (appendRootInputSpatial f (treeRootPartitionSpatial q)) S hS hK hM hBq.le hq k).const_mul
      (treeRootCutoffSpatial q k)
  have he (u : SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) :
      rootAmplitudeSumSpatial A k u = ∑ q ∈ rootLocalCoverSpatial k, A q k u :=
    (rootAmplitudeSum_eventuallyEq_modelSpatial A ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S) k).self_of_nhds u
  change Integrable (fun u => rootAmplitudeSumSpatial A k u) (sourceCellMeasure S)
  simp_rw [he]
  exact integrable_finsetSum _ (fun q _ => hi q)

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional pointwise Fubini/agreement helper. Every physical root bound is supplied
independently by the analytic core in the final source theorem. -/
theorem MomentumTreeData.fourierRootPartitionSourceTreeExtension_agrees_on_cutoff
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    (ζ : Circle) (R : RootCoordinates n) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχroot : ∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ z ξ a, eLpNorm (R.linkDensity L γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency a)) z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.fourierRootPartitionSourceTreeExtension (P := P)) F ζ R χ L γ δ Q I f S t k =
      (MomentumTreeData.weightedSourceTreeKernel (P := P)) F ζ R L γ δ Q I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := rootAmplitudeSumSpatial ((MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S) k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S t u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_treeSpatialFrequency (P := P.withRootInput)) F.frequency F.frequency_measurable
    hχ.continuous.measurable R hLp γ δ Q I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_treeRootAmplitudeSum (P := P)) ζ f S hS hK hM hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (enorm_cutoffTriangleIntegral_le hχ hc
      (R.integrable_linkDensity hLp γ δ
        ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2)
        hI hbox) t).trans (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  rw [(MomentumTreeData.weightedSourceTreeKernel_eq_integral_of_summable (P := P)) F ζ R L γ δ Q I hbox f k
    ((MomentumTreeData.summable_norm_treeLeafWeight_lattice (P := P)) f S hcover hS hL hK hM hf k)]
  unfold fourierRootPartitionSourceTreeExtension
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a * z)
  exact (MomentumTreeData.rootPartitionSourceTreeExtension_agrees_on_cutoffSpatial (P := P)) ζ R hχ hc L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) I hI hbox hχroot f S hcover hS hL hK hM hf
    hN (fun z ξ => hroot z ξ a) t ht hord k

end WaveTurbulence.Flower.IncTop