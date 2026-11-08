/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellCouplePointwise
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawSourceCellIntegral

/-! Ported by source from C2-B-TOP `Cut2BReg.RawCoupleAgreement` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Exact agreement of the recombined extension with the raw source couple

The source kernel is the original unlocalized normalized lattice/time
operator with its two literal external root constraints. Agreement is
pointwise on the whole source box, including its boundary.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The literal raw source couple kernel with genuine external root-clock constraints. -/
@[expose] def MomentumTreeData.sourceCoupleKernelSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ) (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  (MomentumTreeData.sourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.rootCut t) f k

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Exact pointwise raw-source agreement; the physical root envelope is solely a Fubini typing
premise, independently supplied by the analytic core in the final source bound. -/
theorem MomentumTreeData.allCellSourceCoupleExtension_agrees_rawSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
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
    (t : Fin 2 → ℝ) (ht : t ∈ R.rootBox Q) (k : Mom d) :
    (MomentumTreeData.allCellSourceCoupleExtensionSpatial (P := P)) ζ R L γ δ Q I f S t k =
      (MomentumTreeData.sourceCoupleKernelSpatial (P := P)) ζ R L γ δ Q I f t k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [(MomentumTreeData.allCellSourceCoupleExtension_eq_tsumSpatial (P := P)) ζ R L γ δ Q I hI hbox f S hS hLp hK hM hB h hN hb t k]
  unfold sourceCoupleKernelSpatial
  rw [(MomentumTreeData.sourceIntegral_eq_tsum_localizedSourceIntegralSpatial (P := P)) ζ L γ δ Q (I ∩ R.rootCut t)
    (Set.inter_subset_left.trans hbox) f S hcover hS hL hK hM hB h k]
  apply tsum_congr
  intro u
  exact (MomentumTreeData.sourceCoupleExtension_agreesSpatial (P := P)) ζ R L γ δ Q I hI hbox f u.1 u.2.val hLp hK hB h t ht k

end WaveTurbulence.Flower.IncTop