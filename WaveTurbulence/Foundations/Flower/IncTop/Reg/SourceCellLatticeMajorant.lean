/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourcePointwiseLocalization
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceLinkKernelIdentity
public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoffMass

/-! Ported by source from C2-B-TOP `Cut2BReg.SourceCellLatticeMajorant` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Absolute lattice majorant of each actual source localization cell

Actual Fourier inversion gives the pointwise envelope. Exact cutoff
insertion then supplies summable lattice domination with no hard cutoff.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Each actual source cell has the previously computed spectral mass as pointwise envelope. -/
theorem MomentumTreeData.enorm_sourceCellWeight_le_referenceMassSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) (u : SourceCellIndex S) :
    ‖P.sourceCellWeight f S k x u‖ₑ ≤
      ∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ := by
  have he := P.signed_localizedLeafWeight_eq_spectralIntegral (1 : Circle) f u.1 u.2.val hK hB h k x
  simp only [Circle.coe_one, one_mul] at he
  change ‖P.localizedLeafWeight f u.1 k x * halfCellArrayWeight u.2.val (fun p => x p.1 p.2)‖ₑ ≤ _
  rw [he]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro ξ
  exact (P.enorm_localizedSourceSpectralDensity (1 : Circle) f u.1 u.2.val k x ξ).le

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The same envelope times the literal compact analytic cutoff is a lattice majorant. -/
theorem MomentumTreeData.enorm_sourceCellWeight_le_cutoff_majorantSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) (u : SourceCellIndex S) :
    ‖P.sourceCellWeight f S k x u‖ₑ ≤
      (∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) *
        ‖linkArrayCutoff u.2.val (fun p => x p.1 p.2)‖ₑ := by
  have he : P.sourceCellWeight f S k x u * linkArrayCutoff u.2.val (fun p => x p.1 p.2) =
      P.sourceCellWeight f S k x u := by
    unfold sourceCellWeight
    rw [mul_assoc, halfCellArrayWeight_mul_linkArrayCutoff]
  calc
    _ = ‖P.sourceCellWeight f S k x u‖ₑ * ‖linkArrayCutoff u.2.val (fun p => x p.1 p.2)‖ₑ := by
      rw [← enorm_mul, he]
    _ ≤ _ := mul_le_mul' ((MomentumTreeData.enorm_sourceCellWeight_le_referenceMassSpatial (P := P)) f S hK hB h k x u) le_rfl

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Every actual localization cell has an absolute summable lattice majorant uniform in its center. -/
theorem MomentumTreeData.tsum_enorm_sourceCellWeight_lattice_leSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {B L : ℝ} (hL : 1 ≤ L) (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (k : Mom d) (u : SourceCellIndex S) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (p (i, j))) u‖ₑ) ≤
      (∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) *
        ENNReal.ofReal ((5 * L) ^ d) ^ (2 * n) := by
  calc
    _ ≤ ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        (∫⁻ ξ, ‖localizedSpectralReference (n := n) f u.1 ξ‖ₑ) *
          ‖linkArrayCutoff u.2.val (latticeMomentumArray L p)‖ₑ :=
      ENNReal.tsum_le_tsum (fun p => (MomentumTreeData.enorm_sourceCellWeight_le_cutoff_majorantSpatial (P := P)) f S hK hB h k
        (fun i j => latticePoint L (p (i, j))) u)
    _ = _ := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using tsum_enorm_linkArrayCutoff_le hL u.2.val)

end WaveTurbulence.Flower.IncTop