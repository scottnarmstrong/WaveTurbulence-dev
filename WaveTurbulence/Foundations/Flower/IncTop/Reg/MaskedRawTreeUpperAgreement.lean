/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedTreePointwise
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeUpperBoxAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceCellIntegral
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawTreeAgreement
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceRootMaskAgreement

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedRawTreeUpperAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Exact agreement of the fully weighted source extension with the raw couple kernel -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual masked extension agrees with the unlocalized source on the whole root box.
The only additional structural datum is the finite integer row recovering the root momentum. -/
theorem MomentumTreeData.allCellMaskedSourceTreeExtension_agrees_on_cutoffSpatial {d n m w K M : ℕ}
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
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N)
    (hχroot : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceTreeExtensionSpatial (P := P)) χ ζ R L γ δ Q I f S t k =
      (MomentumTreeData.sourceTreeKernelSpatial (P := P)) ζ R L γ δ Q I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellMaskedSourceTreeExtension_eq_tsumSpatial (P := P)) hχ hc ζ R L γ δ Q I
    hI hbox f S hS hLp hK hM hB h hN hb]
  unfold sourceTreeKernelSpatial
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.causalRootCut t)
    (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  rw [← (RootInputCoordinates.sourceRootMask_mul_localizedSourceIntegralSpatial (C := Croot)) ζ L γ δ Q
    (I ∩ R.causalRootCut t) f u.1 u.2.val k]
  rw [(MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixtureSpatial (P := P)) ζ L γ δ Q (I ∩ R.causalRootCut t)
    (Set.inter_subset_left.trans hbox) f u.1 u.2.val hLp hK hB h k]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  have he := (MomentumTreeData.unrestrictedTreeKernel_agrees_on_cutoffSpatial (P := P)) R L γ δ Q I hI hbox hχroot hLp
    t ht hord ((u.1, u.2.val), ξ)
  change Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) I) t = _ at he
  dsimp only
  rw [he]
  simp only [maskedSourceSpectralAmplitudeSpatial]
  ring

end WaveTurbulence.Flower.IncTop