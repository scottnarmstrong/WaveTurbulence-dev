/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeSum
public import WaveTurbulence.Foundations.RegAsymp.NormalizedZeroOrderSum

/-! # Uniform crude half-cell bounds including the empty surviving order -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh
open scoped ENNReal ContDiff

/-- Fixed-cell lattice sum with a true first modulation moment, valid
uniformly in every logarithmic-order range. -/
theorem halfCell_crude_normalized_sum_all_orders {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L ^ (-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
        ContDiff ℝ ∞ Ψ₁ → WordDerivL1 Ψ₁ (fun k => ((4*k).factorial:ℝ)) →
        ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
          approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ₁)‖ ≤
          (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(C*δ/4)^n := by
  obtain ⟨C,hC,hNT⟩ := halfCell_crude_normalized_sum hd hγ hη0 hη hηγ hηγ'
  refine ⟨C,hC,fun A => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT A
  refine ⟨L₀,?_⟩
  intro L hL δ hδ hδ1 n hn z β γ' J Ψ₁ hΨ hD
  by_cases hzero : n = 0
  · subst n
    have hz := norm_approxSum_zero_order_le L (L^(2*γ)*δ) (halfCellAmplitude z β γ') J Ψ₁ hΨ hD
      (H := 1) (by simp [halfCellAmplitude])
    simp only [Nat.mul_zero,pow_zero,Complex.ofReal_one,one_mul]
    simpa only [Finset.univ_eq_empty,Finset.sum_empty,zero_add,add_zero,pow_zero,mul_one] using
      hz.trans (by linarith [Real.pi_pos] : (1:ℝ) ≤ 1+2*Real.pi)
  · exact hL₀ L hL δ hδ hδ1 n (Nat.pos_of_ne_zero hzero) hn z β γ' J Ψ₁ hΨ hD

end WaveTurbulence.RegAsymp
