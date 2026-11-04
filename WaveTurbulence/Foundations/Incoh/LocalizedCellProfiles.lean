/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FiniteCellProductFourier
public import WaveTurbulence.Foundations.Incoh.LocalizedLeafDecomposition

/-!
# Actual spectral profiles for localized source products

Leaf profiles and half-width link profiles form one finite family. All
continuity and Fourier integrability follow from the source spatial norms.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- One spectral variable for every input and every link momentum coordinate. -/
abbrev LocalizedCellIndex (n m : ℕ) := Fin m ⊕ (Fin n × Fin 2)

/-- The literal leaf and link profiles, with coordinate Lebesgue measures. -/
@[expose] def localizedCellProfiles {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    LocalizedCellIndex n m → (Fin d → ℝ) → ℂ
  | .inl a => fun y => leafCell (f a) (c a) (toLp 2 y)
  | .inr p => fun y => halfLinkCell (z p) (toLp 2 y)

/-- Source spatial norms prove continuity of every actual spectral profile. -/
theorem continuous_localizedCellProfiles {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ} (hK : 0 < K)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (i : LocalizedCellIndex n m) : Continuous (localizedCellProfiles f c z i) := by
  cases i with
  | inl a =>
      exact (contDiff_leafCell (contDiff_of_spatialNorm_le hK (h a)) (c a)).continuous.comp
        (PiLp.continuous_toLp 2 _)
  | inr p => exact (contDiff_halfLinkCell (z p)).continuous.comp (PiLp.continuous_toLp 2 _)

/-- Source spatial norms, rather than assumed Fourier estimates, prove profile integrability. -/
theorem timeFourierNorm_localizedCellProfiles_lt_top {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (i : LocalizedCellIndex n m) : Fourier.timeFourierNorm 0 (localizedCellProfiles f c z i) < ⊤ := by
  cases i with
  | inl a => exact lt_of_le_of_lt (timeFourierNorm_leafCell_le hK hB (h a) (c a)) ENNReal.ofReal_lt_top
  | inr p => exact timeFourierNorm_halfLinkCell_lt_top 0 (z p)

/-- Actual momenta at which the leaf and link profiles are evaluated. -/
@[expose] def MomentumTreeData.localizedCellMomenta {d n m w : ℕ} (P : MomentumTreeData n m w)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) : LocalizedCellIndex n m → Fin d → ℝ
  | .inl a => ofLp (P.inputMomentum k x a)
  | .inr p => ofLp (x p.1 p.2)

/-- The finite profile product is exactly the localized source product times its link cell. -/
theorem MomentumTreeData.prod_localizedCellProfiles {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (∏ i, localizedCellProfiles f c z i (P.localizedCellMomenta k x i)) =
      P.localizedLeafWeight f c k x * halfCellArrayWeight z (fun p => x p.1 p.2) := by
  rw [Fintype.prod_sum_type]
  simp only [localizedCellProfiles, localizedCellMomenta, toLp_ofLp,
    localizedLeafWeight, halfCellArrayWeight]

end WaveTurbulence.Incoh
