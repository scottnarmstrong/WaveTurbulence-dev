/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MomentumSpectralShift
public import WaveTurbulence.Foundations.Incoh.LocalizedSpectralIdentity

/-!
# Exact Fourier phase factorization in root and link coordinates

TARGET (incohproof6–10). The actual density factors into its Fourier
coefficient and the root/link characters computed by the integer rows.
-/

public section
noncomputable section
open WithLp

namespace WaveTurbulence.Incoh

/-- Finite multiplicativity of the source positive Fourier character. -/
theorem coe_fourierChar_sum {I : Type*} [Fintype I] (a : I → ℝ) :
    (Real.fourierChar (∑ i, a i) : ℂ) = ∏ i, (Real.fourierChar (a i) : ℂ) := by
  classical
  have h (s : Finset I) : (Real.fourierChar (∑ i ∈ s, a i) : ℂ) =
      ∏ i ∈ s, (Real.fourierChar (a i) : ℂ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        AddChar.map_add_eq_mul, Circle.coe_mul, ih]
  exact h Finset.univ

/-- Coordinate pairing is the actual Euclidean inner product on momenta. -/
theorem timePairing_eq_inner {d : ℕ} (ξ : Fin d → ℝ) (x : Mom d) :
    Fourier.timePairing d ξ (ofLp x) = inner ℝ (toLp 2 ξ) x := by
  simp [Fourier.timePairing, PiLp.inner_apply, dotProduct, mul_comm]

/-- Actual joint coefficient before any oscillatory integral is estimated. -/
@[expose] def localizedSpectralCoefficient {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) : ℂ :=
  ∏ i, Fourier.timeFourier (localizedCellProfiles f c z i) (ξ i)

/-- The computed source density has exactly the root and link phase shifts supplied by the
transpose of the integer node map. -/
theorem MomentumTreeData.localizedSourceSpectralDensity_eq_shift_phase {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    P.localizedSourceSpectralDensity ζ f c z k x ξ =
      (ζ : ℂ) * (Real.fourierChar (∑ j : MomentumCoordinate n,
        inner ℝ (P.spectralShift ξ j) (rootLinkMomenta k x j)) : ℂ) *
          localizedSpectralCoefficient f c z ξ := by
  unfold localizedSourceSpectralDensity cellProductFourierIntegrand localizedSpectralCoefficient
  simp only [Circle.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  rw [← coe_fourierChar_sum]
  have hp : (∑ i, Fourier.timePairing d (ξ i) (P.localizedCellMomenta k x i)) =
      ∑ j : MomentumCoordinate n, inner ℝ (P.spectralShift ξ j) (rootLinkMomenta k x j) := by
    rw [← P.sum_inner_localizedCellMomenta ξ k x]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [ofLp_toLp] using timePairing_eq_inner (ξ i) (toLp 2 (P.localizedCellMomenta k x i))
  rw [hp, mul_assoc]

/-- The global root modulation and each free link modulation are separated exactly. -/
theorem MomentumTreeData.localizedSourceSpectralDensity_eq_root_link_phase {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
    P.localizedSourceSpectralDensity ζ f c z k x ξ =
      (ζ : ℂ) * (Real.fourierChar (inner ℝ (P.spectralShift ξ none) k) : ℂ) *
        (∏ p : Fin n × Fin 2,
          (Real.fourierChar (inner ℝ (P.spectralShift ξ (some p)) (x p.1 p.2)) : ℂ)) *
            localizedSpectralCoefficient f c z ξ := by
  rw [P.localizedSourceSpectralDensity_eq_shift_phase ζ f c z k x ξ]
  simp only [Fintype.sum_option, rootLinkMomenta, AddChar.map_add_eq_mul,
    Circle.coe_mul, coe_fourierChar_sum]
  ring

end WaveTurbulence.Incoh
