/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedCoupleExtension
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawMeasureInsertion
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.PointwiseProduct
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedRawCoupleUpperAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.WeightedCoupleAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Pointwise agreement of the common Fourier extension and weighted raw couple -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional Fubini/agreement helper. The source theorem supplies its uniform physical
root bound independently from the analytic core; this is not a decay assumption. -/
theorem MomentumTreeData.fourierMaskedSourceCoupleExtension_agrees_above
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (Croot : RootInputCoordinates P) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n)
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hroot : ∀ z ξ a, eLpNorm (R.linkDensity L γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency a)) z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) F χ ζ R L γ δ Q I f S 0 t k =
      (MomentumTreeData.weightedSourceCoupleKernel (P := P)) F ζ R L γ δ Q I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S t u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_coupleSpatialFrequency (P := P)) F.frequency F.frequency_measurable
    hχ.continuous.measurable R hLp γ δ Q I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (R.enorm_coupleExtension_le hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2) hI hbox t).trans
      (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  rw [(MomentumTreeData.weightedSourceCoupleKernel_eq_integral_of_summable (P := P)) F ζ R L γ δ Q I hbox f k
    ((MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P)) f S hcover hS hL hK hM hB hf k)]
  unfold fourierMaskedSourceCoupleExtension
  simp only [add_zero]
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a * z)
  simpa only [allCellMaskedSourceCoupleExtensionSpatial, add_zero] using
    (MomentumTreeData.allCellMaskedSourceCoupleExtension_agrees_aboveSpatial (P := P)) hχ hc Croot ζ R L γ δ
    (spatialFrequencyLinks Q (F.frequency a)) I hI hbox f S hcover hS hL hK hM hB hf
    hN (fun z ξ => hroot z ξ a) t ht hχone k

end WaveTurbulence.Flower.IncTop