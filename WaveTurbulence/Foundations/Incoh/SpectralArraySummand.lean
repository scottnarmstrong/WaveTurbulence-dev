/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralLinkParameters
public import WaveTurbulence.Foundations.Incoh.LinkArraySummation
public import WaveTurbulence.Foundations.Incoh.LinkArrayCutoff

/-!
# Exact identification of the source spectral summand

TARGET (incohproof9–10). The inserted compact cutoffs and computed linear
Fourier characters give precisely the literal analytic link summands.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The two positive exponential conventions agree character for character. -/
theorem e_eq_coe_fourierChar (s : ℝ) : WeylSums.e s = (Real.fourierChar s : ℂ) := by
  rw [WeylSums.e, Real.fourierChar_apply]

/-- Actual array cutoff is the product of the two-coordinate link cutoffs. -/
theorem MomentumTreeData.linkArrayCutoff_eq_prod {d n m w : ℕ} (P : MomentumTreeData n m w)
    (L : ℝ) (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    linkArrayCutoff z (latticeMomentumArray L p) =
      ∏ i, cutoffAmplitude L (P.spectralLinks Q z ξ i).toLinkParameters (p (i, 0), p (i, 1)) := by
  simp only [linkArrayCutoff, latticeMomentumArray, Fintype.prod_prod_type, Fin.prod_univ_two,
    cutoffAmplitude, spectralLinks, Complex.ofReal_mul]

/-- The free link Fourier characters regroup into the two linear shifts of each analytic link. -/
theorem MomentumTreeData.prod_link_character_eq {d n m w : ℕ} (P : MomentumTreeData n m w)
    (ξ : LocalizedCellIndex n m → Fin d → ℝ) (x : Fin n → Fin 2 → Mom d) :
    (∏ p : Fin n × Fin 2, (Real.fourierChar
      (inner ℝ (P.spectralShift ξ (some p)) (x p.1 p.2)) : ℂ)) =
      ∏ i, WeylSums.e (inner ℝ (x i 0) (P.spectralShift ξ (some (i, 0))) +
        inner ℝ (x i 1) (P.spectralShift ξ (some (i, 1)))) := by
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two, e_eq_coe_fourierChar,
    AddChar.map_add_eq_mul, Circle.coe_mul, real_inner_comm]

/-- The literal source time factor times cutoff and link Fourier phase equals the analytic
link-array summand with computed centers and shifts. -/
theorem MomentumTreeData.sourceTemporalPhase_mul_cutoff_mul_character {d n m w : ℕ}
    (P : MomentumTreeData n m w) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ)
    (p : (Fin n × Fin 2) → Fin d → ℤ) (t : Fin n → Fin 2 → ℝ) :
    sourceTemporalPhase L γ δ Q p t * linkArrayCutoff z (latticeMomentumArray L p) *
      (∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
        (latticePoint L (p q))) : ℂ)) =
      linkArraySummand L γ δ (P.spectralLinks Q z ξ) t p := by
  rw [P.linkArrayCutoff_eq_prod L Q z ξ p,
    P.prod_link_character_eq ξ (fun i j => latticePoint L (p (i, j)))]
  unfold sourceTemporalPhase linkArraySummand
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact temporal_phase_mul_linear_phase L γ δ (P.spectralLinks Q z ξ i)
    (p (i, 0), p (i, 1)) (t i)

end WaveTurbulence.Incoh
