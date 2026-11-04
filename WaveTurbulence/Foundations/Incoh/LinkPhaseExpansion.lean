/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink
public import WaveTurbulence.Foundations.Incoh.LinkAbsoluteBounds

/-!
# Literal finite phase expansion of selected links

TARGET between (incohproof26) and (incohproof27). The phase coefficients
have absolute mass at most `(5L)^(2d)` per removed link. Keeping that mass
avoids an unnecessary enumeration of a momentum-dependent finite support.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The time-independent coefficient, including the literal squared Wick mask. -/
@[expose] def linkPhaseCoefficient {d : ℕ} (L : ℝ) (Q : LayerLink d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  linkAmplitude L Q.toLinkParameters p * WeylSums.e (linkPhase L 0 Q.toLinkParameters p)

/-- The temporal phase frequency in the convention `exp(i Γ (t-s))`. -/
@[expose] def linkTemporalFrequency {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  2 * Real.pi * ((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
    inner ℝ (latticePoint L p.1) (latticePoint L p.2)

/-- Exact expansion of the actual localized lattice factor into time phases. -/
theorem linkTimeFactor_eq_phase_sum {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
    (t : Fin 2 → ℝ) :
    linkTimeFactor L γ δ Q t = ∑' p, linkPhaseCoefficient L Q p *
      Complex.exp ((linkTemporalFrequency L γ δ Q p * (t 0 - t 1) : ℝ) * Complex.I) := by
  unfold linkTimeFactor linkLatticeSum
  apply tsum_congr
  intro p
  have he : linkPhase L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) Q.toLinkParameters p =
      linkPhase L 0 Q.toLinkParameters p +
        (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) *
          inner ℝ (latticePoint L p.1) (latticePoint L p.2) := by
    unfold linkPhase
    ring
  rw [he, WeylSums.e_add, ← mul_assoc]
  have hfreq : 2 * Real.pi *
      ((((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) *
        inner ℝ (latticePoint L p.1) (latticePoint L p.2)) =
      linkTemporalFrequency L γ δ Q p * (t 0 - t 1) := by
    unfold linkTemporalFrequency
    ring
  simp only [WeylSums.e, hfreq, linkPhaseCoefficient]

/-- Absolute phase coefficient mass is uniformly bounded, including moving centers and shifts. -/
theorem tsum_norm_linkPhaseCoefficient_le {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (Q : LayerLink d) :
    (∑' p, ‖linkPhaseCoefficient L Q p‖) ≤ (5 * L) ^ (2 * d) :=
  (Summable.tsum_le_tsum (norm_linkTerm_le L 0 Q.toLinkParameters)
    (summable_norm_linkTerm (zero_lt_one.trans_le hL) 0 Q.toLinkParameters)
    (summable_norm_cutoffAmplitude (zero_lt_one.trans_le hL) Q.toLinkParameters)).trans
    (tsum_norm_cutoffAmplitude_le hL Q.toLinkParameters)

/-- The expansion has finite support, even when its center depends on an external parameter. -/
theorem finite_support_linkPhaseCoefficient {d : ℕ} {L : ℝ} (hL : 0 < L) (Q : LayerLink d) :
    (Function.support (linkPhaseCoefficient L Q)).Finite := by
  apply (finite_support_linkAmplitude hL Q.toLinkParameters).subset
  intro p hp hz
  exact hp (by simp only [linkPhaseCoefficient, hz, zero_mul])

end WaveTurbulence.Incoh
