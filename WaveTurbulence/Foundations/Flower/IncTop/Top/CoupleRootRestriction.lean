/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootExtension
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.WeightedCoupleAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ExponentialCoefficientAbsorption
public import WaveTurbulence.Foundations.Incoh.OneClockCouple
public import WaveTurbulence.Foundations.Incoh.FinalExponentLoss

/-! Ported by source from C2-B-TOP `C2BTop.CoupleRootRestriction` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Root-modulated raw couples: restriction decay at the printed Proposition 5.1 rate

Two raw couple operators, each with the root-modulated internal weight `(G.at k).value` inside the
literal lattice sum:
* the two-clock couple `weightedSourceCoupleKernel (G.at k)` (C2-B-REG);
* the one-clock couple `weightedSourceOneClockKernel (G.at k)` (one trivial tree; main's
  `sourceOneClockKernel` with the weight), recovered from the translated two-clock extension.

The agreement with the common extension is pointwise in `k`, so C2-B-REG's agreement applied to the
measure `G.at k` gives it; the extension bound is `exists_rootMaskedCoupleExtension_bound`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh

/-- The spatial one-clock raw operator (main's `sourceOneClockKernel` for spatial links). -/
def sourceOneClockKernelSpatial {d n m w : ℕ} (P : MomentumTreeData n m w) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.oneClockCut a (t a)) f k

/-- The weighted one-clock raw operator. -/
def weightedSourceOneClockKernel {d n m w : ℕ} {α : Type*} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.weightedSourceIntegral (P := P)) F ζ L γ δ Q (I ∩ R.oneClockCut a (t a)) f k

/-- Main's one-clock masked recovery (`allCellMaskedSourceCoupleExtension_agrees_oneClock_above`)
for spatial links. -/
theorem allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatial
    {d n m w K M : ℕ} (P : MomentumTreeData n m w) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ) (Croot : RootInputCoordinates P) (ζ : Circle)
    (R : RootCoordinates n) (a : Fin 2) (b : ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ)
    (ht : R.baseRootTimes Q ≤ t + R.oneClockShift a Q b)
    (hpass : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceCoupleExtensionSpatial (P := P)) χ ζ R L γ δ Q I f S
      (R.oneClockShift a Q b) t k = sourceOneClockKernelSpatial P ζ R a L γ δ Q I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellMaskedSourceCoupleExtension_eq_tsumSpatial (P := P)) hχ hc ζ R L γ δ Q I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold sourceOneClockKernelSpatial
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.oneClockCut a (t a))
    (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  calc
    _ = sourceRootMask u.1 k * (MomentumTreeData.localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q
        (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k := by
      rw [(MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatial (P := P)) ζ L γ δ Q (I ∩ R.oneClockCut a (t a))
        (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k, ← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      dsimp only
      have hbase : R.baseRootTimes ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) = R.baseRootTimes Q := rfl
      have hshift : R.oneClockShift a ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) b =
          R.oneClockShift a Q b := rfl
      have he := R.coupleExtension_agrees_above hLp γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ)
        hI hbox (t + R.oneClockShift a Q b) (hbase ▸ ht) (by simpa only [hbase] using hχone)
      rw [R.cumulativeKernel_eq_oneClockKernel a L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) hbox
        (by simpa only [hbase] using hpass)] at he
      change R.coupleExtension χ L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) I
        (t + R.oneClockShift a Q b) = _ at he
      rw [he]
      simp only [RootCoordinates.oneClockKernel, Pi.add_apply, RootCoordinates.oneClockShift,
        ite_true, add_zero]
      unfold MomentumTreeData.maskedSourceSpectralAmplitudeSpatial
      ring
    _ = _ := (RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatial (C := Croot)) ζ L γ δ Q
      (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k

/-- Weighted one-clock agreement of the translated common Fourier extension (any measure `F`). -/
theorem fourierMaskedSourceCoupleExtension_agrees_oneClock
    {d n m w K M : ℕ} {α : Type} [MeasurableSpace α]
    (P : MomentumTreeData n m w) (F : Cut2A.SpatialMeasure (PairedMomentum d n) α)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (Croot : RootInputCoordinates P) (ζ : Circle) (R : RootCoordinates n) (a : Fin 2) (b : ℝ)
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
    (t : Fin 2 → ℝ)
    (ht : R.baseRootTimes Q ≤ t + R.oneClockShift a Q b)
    (hpass : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    (MomentumTreeData.fourierMaskedSourceCoupleExtension (P := P)) F χ ζ R L γ δ Q I f S (R.oneClockShift a Q b) t k =
      weightedSourceOneClockKernel P F ζ R a L γ δ Q I f t k := by
  have hLp := zero_lt_one.trans_le hL
  let A := (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k
  let G := fun u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α =>
    (MomentumTreeData.allCellCutoffCoupleKernelSpatial (P := P)) χ R L γ δ (spatialFrequencyLinks Q (F.frequency u.2)) I S
      (t + R.oneClockShift a Q b) u.1
  have hmG := ((MomentumTreeData.stronglyMeasurable_coupleSpatialFrequency (P := P)) F.frequency F.frequency_measurable
    hχ.continuous.measurable R hLp γ δ Q I hI S).comp_measurable
      (g := fun u => (t + R.oneClockShift a Q b, u)) (measurable_const.prodMk measurable_id)
  have hiA := (MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB hf k
  have hb (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      ‖G u‖ₑ ≤ ENNReal.ofReal hc.bound ^ 4 * N :=
    (R.enorm_coupleExtension_le hχ hc hLp γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) (spatialFrequencyLinks Q (F.frequency u.2)) u.1.1.2.val u.1.2) hI hbox
        (t + R.oneClockShift a Q b)).trans
      (mul_le_mul' le_rfl (hroot u.1.1.2.val u.1.2 u.2))
  have he := integral_product_amplitude_kernel (sourceCellMeasure S) F A hiA G hmG.aestronglyMeasurable
    (ENNReal.mul_lt_top (by finiteness) hN) hb
  have hsum := (MomentumTreeData.summable_norm_sourceLeafWeight_latticeSpatial (P := P)) f S hcover hS hL hK hM hB hf k
  unfold weightedSourceOneClockKernel
  rw [(MomentumTreeData.weightedSourceIntegral_eq_integral_of_summable (P := P)) F ζ L γ δ Q (I ∩ R.oneClockCut a (t a))
    (inter_subset_left.trans hbox) f k hsum]
  unfold MomentumTreeData.fourierMaskedSourceCoupleExtension
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro a'
  dsimp only
  apply congrArg (fun z : ℂ => F.amplitude a' * z)
  have hbox' : I ⊆ univ.pi (fun i => linkBox (spatialFrequencyLinks Q (F.frequency a') i)) := hbox
  have hq := allCellMaskedSourceCoupleExtension_agrees_oneClock_aboveSpatial P hχ hc Croot ζ R a b L γ δ
    (spatialFrequencyLinks Q (F.frequency a')) I hI hbox' f S hcover hS hL hK hM hB hf
    hN (fun z ξ => hroot z ξ a') t ht hpass hχone k
  exact hq

end WaveTurbulence.Flower.IncTop