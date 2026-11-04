/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearIntegral
public import WaveTurbulence.Foundations.WeylSums.MinorArcExponents

/-!
# TARGET Lemma 5.3: the bilinear minor-arc exponential sum

Source L970–L977, `lemlayer2`, in the exact quantifier order of the audited
tier-B1 `quadExpSum2` draft. The fixed cutoff is `latticeCutoff`, the tensor
product of the landed `Fourier.chi0`. `MinorArcSums` proves agreement with
the scalar draft formula and finiteness of the lattice sums.
-/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- TARGET Lemma 5.3 (`lemlayer2`), the Foundations counterpart of the
tier-B1 draft `quadExpSum2`. Uniform in all four real vector parameters. -/
theorem quadExpSum2_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → ∀ T₀ : ℝ, 0 < T₀ →
      ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d,
        (∫ s : ℝ in {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀*L^(2*γ)},
          ‖bilinearLatticeSum L s a b ξ ζ‖) ≤
          C*L^(2*(d : ℝ)-2*((d : ℝ)-1)*(1-γ)+η) := by
  intro d hd γ hγ η hη T₀ hT₀
  obtain ⟨ε,hε,hεd,hεη⟩ := exists_minor_arc_loss d hd hη
  obtain ⟨C,hC,hb⟩ := exists_bilinear_minor_integral_bound d hd ε hε hεd
  let A := C*(T₀/4)^((d : ℝ)-1-ε)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,2,?_⟩
  intro L hL a b ξ ζ
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hB : 0 < T₀*L^(2*γ) := mul_pos hT₀ (Real.rpow_pos_of_pos hLp _)
  have hh := (hb L (T₀*L^(2*γ)) hL hB a b ξ ζ).2
  calc
    _ ≤ C*L^(2*(d : ℝ))*(T₀*L^(2*γ)/(4*L^2))^((d : ℝ)-1-ε) := hh
    _ = A*L^(2*(d : ℝ)+(2*γ-2)*((d : ℝ)-1-ε)) := by
      rw [mul_assoc, bilinear_minor_scale_identity hLp hT₀.le]
      dsimp [A]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1
        (bilinear_minor_exponent_le (d : ℝ) γ ε η hγ.1.le hε.le hεη)) hA

end WaveTurbulence.WeylSums
