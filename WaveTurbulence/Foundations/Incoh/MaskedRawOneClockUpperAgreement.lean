/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MaskedCouplePointwise
public import WaveTurbulence.Foundations.Incoh.CoupleUpperBoxAgreement
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement
public import WaveTurbulence.Foundations.Incoh.RawSourceCellIntegral
public import WaveTurbulence.Foundations.Incoh.OneClockCouple
public import WaveTurbulence.Foundations.Incoh.RawOneClockAgreement

/-! # Exact raw source recovery for a couple with one genuine root clock

TARGET L1049, audit P-1. The passive external time is removed from the
source domain. The auxiliary selected branching clock is fully integrated.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Actual countable spectral recovery on the full genuine/passive external unit box. -/
theorem MomentumTreeData.allCellMaskedSourceCoupleExtension_agrees_oneClock_above
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
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ)
    (ht : R.baseRootTimes Q ≤ t + R.oneClockShift a Q b)
    (hpass : ∀ j, j ≠ a → R.baseRootTimes Q j + 1 ≤ (t + R.oneClockShift a Q b) j)
    (hχone : ∀ j : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ)
      ((t + R.oneClockShift a Q b - R.baseRootTimes Q) j), χ s = 1) (k : Mom d) :
    P.allCellMaskedSourceCoupleExtension χ ζ R L γ δ Q I f S
      (R.oneClockShift a Q b) t k = P.sourceOneClockKernel ζ R a L γ δ Q I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [P.allCellMaskedSourceCoupleExtension_eq_tsum hχ hc ζ R L γ δ Q I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold sourceOneClockKernel
  rw [P.sourceIntegral_eq_tsum_localizedSourceIntegral ζ L γ δ Q (I ∩ R.oneClockCut a (t a))
    (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  calc
    _ = sourceRootMask u.1 k * P.localizedSourceIntegral ζ L γ δ Q
        (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k := by
      rw [P.localizedSourceIntegral_eq_linkKernelMixture ζ L γ δ Q (I ∩ R.oneClockCut a (t a))
        (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k, ← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      dsimp only
      have he := R.coupleExtension_agrees_above hLp γ δ (P.spectralLinks Q u.2.val ξ)
        hI hbox (t + R.oneClockShift a Q b) ht hχone
      rw [R.cumulativeKernel_eq_oneClockKernel a L γ δ (P.spectralLinks Q u.2.val ξ) hbox hpass] at he
      change R.coupleExtension χ L γ δ (P.spectralLinks Q u.2.val ξ) I
        (t + R.oneClockShift a Q b) = _ at he
      rw [he]
      simp only [RootCoordinates.oneClockKernel, Pi.add_apply, RootCoordinates.oneClockShift,
        ite_true, add_zero]
      unfold MomentumTreeData.maskedSourceSpectralAmplitude
      ring
    _ = _ := Croot.sourceRootMask_mul_localizedSourceIntegral ζ L γ δ Q
      (I ∩ R.oneClockCut a (t a)) f u.1 u.2.val k

end WaveTurbulence.Incoh
