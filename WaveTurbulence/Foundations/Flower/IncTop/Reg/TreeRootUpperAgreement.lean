/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpatialDecay
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedRawTreeUpperAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.TreeRootUpperAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Exact source recovery from the locally finite tree root partition -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual tree extension equals the literal source on the whole forward source domain.
The physical envelope is used only for the finite-model pointwise Fubini step. -/
theorem MomentumTreeData.rootPartitionSourceTreeExtension_agrees_on_cutoffSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχroot : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P.withRootInput)) Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.rootPartitionSourceTreeExtensionSpatial (P := P)) ζ R χ L γ δ Q I f S t k =
      (MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k := by
  classical
  let A := (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S
  let G := (MomentumTreeData.allCellTreeKernelSpatial (P := P.withRootInput)) R χ L γ δ Q I S t
  have hi (q : Fin d → ℤ) : Integrable (fun u => A q k u * G u) (sourceCellMeasure S) := by
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
    have h := (MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1Spatial (P := P.withRootInput)) hχ hc ζ R L γ δ Q I
      hI hbox (appendRootInputSpatial f (treeRootPartitionSpatial q)) S hS (zero_lt_one.trans_le hL) hK hM
      hBq.le hq hN hb t k
    simpa only [A, treeRootSpectralAmplitudeSpatial, rootCutoffSpectralAmplitudeSpatial, mul_assoc, G] using
      h.const_mul (treeRootCutoffSpatial q k)
  have hloc := (rootAmplitudeSum_eventuallyEq_modelSpatial A
    ((MomentumTreeData.treeRootSpectralAmplitude_eq_zeroSpatial (P := P)) ζ f S) k).self_of_nhds
  have he : (MomentumTreeData.rootPartitionSourceTreeExtensionSpatial (P := P)) ζ R χ L γ δ Q I f S t k =
      ∑ q ∈ rootLocalCoverSpatial k, treeRootCutoffSpatial q k *
        (MomentumTreeData.sourceTreeKernelSpatial (P := P.withRootInput)) ζ R L γ δ Q I (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k := by
    unfold rootPartitionSourceTreeExtensionSpatial
    change (∫ u, rootAmplitudeSumSpatial A k u * G u ∂sourceCellMeasure S) = _
    have hfun : (fun u => rootAmplitudeSumSpatial A k u * G u) =
        fun u => ∑ q ∈ rootLocalCoverSpatial k, A q k u * G u := by
      funext u
      rw [hloc u]
      exact Finset.sum_mul _ _ _
    rw [hfun, integral_finsetSum _ (fun q _ => hi q)]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
    change (∫ u, (treeRootCutoffSpatial q k * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P.withRootInput)) ζ
      (appendRootInputSpatial f (treeRootPartitionSpatial q)) S k u) * G u ∂sourceCellMeasure S) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact (MomentumTreeData.allCellMaskedSourceTreeExtension_agrees_on_cutoffSpatial (P := P.withRootInput)) hχ hc P.withRootInputCoordinates ζ R
      L γ δ Q I hI hbox _ S hcover hS hL hK hM hBq.le hq hN hb hχroot t ht hord k
  rw [he]
  have hs := (MomentumTreeData.hasSum_sourceTreeKernel_rootPartitionSpatial (P := P)) ζ R L γ δ Q I f t k
  have hz (q : Fin d → ℤ) (hq : q ∉ rootLocalCoverSpatial k) :
      treeRootCutoffSpatial q k * (MomentumTreeData.sourceTreeKernelSpatial (P := P.withRootInput)) ζ R L γ δ Q I
        (appendRootInputSpatial f (treeRootPartitionSpatial q)) t k = 0 := by
    rw [treeRootCutoff_eq_zero_on_ball_of_notMemSpatial k q hq (by simp), zero_mul]
  exact (hasSum_sum_of_ne_finset_zero hz).unique hs

end WaveTurbulence.Flower.IncTop