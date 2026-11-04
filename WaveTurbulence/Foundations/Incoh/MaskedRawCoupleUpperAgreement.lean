/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedCouplePointwise
public import WaveTurbulence.Foundations.Incoh.RawSourceCellIntegral
public import WaveTurbulence.Foundations.Incoh.RawCoupleAgreement
public import WaveTurbulence.Foundations.Incoh.CoupleUpperBoxAgreement
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement

/-! # Exact agreement of the fully weighted source extension with the raw couple kernel -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The actual masked extension agrees with the unlocalized source on the whole root box.
The only additional structural datum is the finite integer row recovering the root momentum. -/
theorem MomentumTreeData.allCellMaskedSourceCoupleExtension_agrees_above {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ) (Croot : RootInputCoordinates P) (ζ : Circle) (R : RootCoordinates n)
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
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (ht : R.baseRootTimes Q ≤ t)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    P.allCellMaskedSourceCoupleExtension χ ζ R L γ δ Q I f S 0 t k =
      P.sourceCoupleKernel ζ R L γ δ Q I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [P.allCellMaskedSourceCoupleExtension_eq_tsum hχ hc ζ R L γ δ Q I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold sourceCoupleKernel
  rw [P.sourceIntegral_eq_tsum_localizedSourceIntegral ζ L γ δ Q (I ∩ R.rootCut t)
    (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  rw [← Croot.sourceRootMask_mul_localizedSourceIntegral ζ L γ δ Q
    (I ∩ R.rootCut t) f u.1 u.2.val k]
  rw [P.localizedSourceIntegral_eq_linkKernelMixture ζ L γ δ Q (I ∩ R.rootCut t)
    (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  dsimp only
  simp only [add_zero, maskedSourceSpectralAmplitude]
  have hbase : R.baseRootTimes (P.spectralLinks Q u.2.val ξ) = R.baseRootTimes Q := rfl
  rw [R.coupleExtension_agrees_above hLp γ δ (P.spectralLinks Q u.2.val ξ) hI hbox t
    (hbase ▸ ht) (by simpa only [hbase] using hχone)]
  simp only [RootCoordinates.cumulativeKernel, mul_assoc]

end WaveTurbulence.Incoh
