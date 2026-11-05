/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitudeSupport
public import WaveTurbulence.Foundations.RegAsymp.CrudeNormalizedApproximation

/-! # Derivative-only crude NT bound for the actual fixed-cell amplitude

All spatial amplitude hypotheses of NT are discharged here. Only the
literal temporal-symbol smoothness/derivative/moment premises remain;
they are supplied by the separately proved coefficient normalization.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh
open scoped ENNReal ContDiff

/-- Fixed-cell approximation with a true first modulation moment, valid
uniformly in every logarithmic-order range. -/
theorem halfCell_crude_normalized_approximation {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L ^ (-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
        ContDiff ℝ ∞ Ψ₁ → WordDerivL1 Ψ₁ (fun k => ((4*k).factorial:ℝ)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ₁) -
            approxApp L δ γ J Ψ₁ (halfCellAmplitude z β γ'))‖ ≤
          (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(C*δ/4)^n := by
  obtain ⟨C₁,hC₁,hNT⟩ := crude_normalized_approximation hd hγ hη0 hη hηγ hηγ'
  let r : ℝ := max 1 (Real.sqrt d)
  let D : ℝ := halfLinkFirstMomentConstant d
  let C : ℝ := C₁*r^(2*d)*D^2
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD : 0 < D := halfLinkFirstMomentConstant_pos d
  refine ⟨C,by dsimp only [C]; positivity,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨L₀,?_⟩
  intro L hL δ hδ hδ1 n hnp hn z β γ' J Ψ₁ hΨ hDer
  let H : ℝ := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*D^(2*n)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hW : (∫⁻ τ : (Fin n → Mom d) × (Fin n → Mom d),
      ‖fourierW (halfCellAmplitude z β γ') τ.1 τ.2‖ₑ *
        ENNReal.ofReal (1+2*Real.pi*freqNorm τ.1 τ.2)) ≤ ENNReal.ofReal H := by
    apply (halfCellAmplitude_fourier_budget z β γ').trans_eq
    dsimp only [H,D]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (halfLinkFirstMomentConstant_pos d).le]
    exact (mul_assoc (ENNReal.ofReal (1+2*Real.pi))
      (ENNReal.ofReal (1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖))))
      (ENNReal.ofReal (halfLinkFirstMomentConstant d)^(2*n))).symm
  have hh := hL₀ L hL δ hδ hδ1 n hnp hn H hH (fun i j : Fin n => i<j)
    (fun _ => .zero) (fun _ => .zero) (fun _ => trivial) (fun _ => trivial)
    (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
    (fun _ => r) (fun _ => le_max_left _ _) (halfCellAmplitude z β γ')
    (continuous_halfCellAmplitude z β γ') (halfCellAmplitude_support z β γ') hW
    J Ψ₁ hΨ hDer
  have hscale : (∏ _j : Fin n, r)^(2*d)*((C₁*δ/4)^n*H) =
      (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(C*δ/4)^n := by
    have he : (C*δ/4)^n = (r^(2*d))^n*(C₁*δ/4)^n*(D^2)^n := by
      dsimp only [C]
      rw [show C₁*r^(2*d)*D^2*δ/4 = r^(2*d)*(C₁*δ/4)*D^2 by ring,mul_pow,mul_pow]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    dsimp only [H]
    rw [pow_right_comm r n (2*d),pow_mul D 2 n,he]
    ring
  exact hh.trans_eq (by simpa only [mul_assoc] using hscale)

end WaveTurbulence.RegAsymp
