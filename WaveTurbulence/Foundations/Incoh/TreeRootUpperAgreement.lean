/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootSpatialDecay
public import WaveTurbulence.Foundations.Incoh.MaskedRawTreeUpperAgreement

/-! # Exact source recovery from the locally finite tree root partition -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual tree extension equals the literal source on the whole forward source domain.
The physical envelope is used only for the finite-model pointwise Fubini step. -/
theorem MomentumTreeData.rootPartitionSourceTreeExtension_agrees_on_cutoff {d n m w K M : ℕ}
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
      eLpNorm (R.linkDensity L γ δ (P.withRootInput.spectralLinks Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    P.rootPartitionSourceTreeExtension ζ R χ L γ δ Q I f S t k =
      P.sourceTreeKernel ζ R L γ δ Q I f t k := by
  classical
  let A := P.treeRootSpectralAmplitude ζ f S
  let G := P.withRootInput.allCellTreeKernel R χ L γ δ Q I S t
  have hi (q : Fin d → ℤ) : Integrable (fun u => A q k u * G u) (sourceCellMeasure S) := by
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
    have h := P.withRootInput.integrable_allCellMaskedTreeSlice_of_uniformRootL1 hχ hc ζ R L γ δ Q I
      hI hbox (appendRootInput f (treeRootPartition q)) S hS (zero_lt_one.trans_le hL) hK hM
      hBq.le hq hN hb t k
    simpa only [A, treeRootSpectralAmplitude, rootCutoffSpectralAmplitude, mul_assoc, G] using
      h.const_mul (treeRootCutoff q k)
  have hloc := (rootAmplitudeSum_eventuallyEq_model A
    (P.treeRootSpectralAmplitude_eq_zero ζ f S) k).self_of_nhds
  have he : P.rootPartitionSourceTreeExtension ζ R χ L γ δ Q I f S t k =
      ∑ q ∈ rootLocalCover k, treeRootCutoff q k *
        P.withRootInput.sourceTreeKernel ζ R L γ δ Q I (appendRootInput f (treeRootPartition q)) t k := by
    unfold rootPartitionSourceTreeExtension
    change (∫ u, rootAmplitudeSum A k u * G u ∂sourceCellMeasure S) = _
    have hfun : (fun u => rootAmplitudeSum A k u * G u) =
        fun u => ∑ q ∈ rootLocalCover k, A q k u * G u := by
      funext u
      rw [hloc u]
      exact Finset.sum_mul _ _ _
    rw [hfun, integral_finsetSum _ (fun q _ => hi q)]
    apply Finset.sum_congr rfl
    intro q _
    obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
    change (∫ u, (treeRootCutoff q k * P.withRootInput.allCellMaskedSpectralAmplitude ζ
      (appendRootInput f (treeRootPartition q)) S k u) * G u ∂sourceCellMeasure S) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact P.withRootInput.allCellMaskedSourceTreeExtension_agrees_on_cutoff hχ hc P.withRootInputCoordinates ζ R
      L γ δ Q I hI hbox _ S hcover hS hL hK hM hBq.le hq hN hb hχroot t ht hord k
  rw [he]
  have hs := P.hasSum_sourceTreeKernel_rootPartition ζ R L γ δ Q I f t k
  have hz (q : Fin d → ℤ) (hq : q ∉ rootLocalCover k) :
      treeRootCutoff q k * P.withRootInput.sourceTreeKernel ζ R L γ δ Q I
        (appendRootInput f (treeRootPartition q)) t k = 0 := by
    rw [treeRootCutoff_eq_zero_on_ball_of_notMem k q hq (by simp), zero_mul]
  exact (hasSum_sum_of_ne_finset_zero hz).unique hs

end WaveTurbulence.Incoh
