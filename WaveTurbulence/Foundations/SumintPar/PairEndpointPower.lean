/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.StrictPowerAbsorption
public import WaveTurbulence.Foundations.SumintPar.SourceScalePowers

/-!
# The pair endpoint strip gives a beta/2 incoherence reserve

The three reserves relative to the ordinary pair scale are beta,
2 gamma, and the Weyl reserve 2(d-1)(1-gamma)-eta. The threshold may
absorb any fixed nonnegative coefficient, including a source gap factor.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Numerical normalization of the actual physical pair endpoint estimate. -/
theorem exists_pair_endpoint_power_bound (d : ℕ) (γ η β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η)
    (Cs Cm k δ : ℝ) (hCs : 0 ≤ Cs) (hCm : 0 ≤ Cm) (hk : 0 ≤ k) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      k*((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)*(4*L^(-β)+2/(16*sourceHalfScale L γ δ)))+
        (1+2*L^(-β))*(16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) ≤
      L^(2*((d:ℝ)-γ)-β/2) := by
  let As := Cs*(8:ℝ)⁻¹*δ⁻¹*4^(2*d)
  let Ai := 2*Cs*(8:ℝ)^(-2:ℝ)*δ^(-2:ℝ)*4^(2*d)
  let Am := Cm*(8:ℝ)⁻¹*δ⁻¹*4^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)
  have hAs : 0 ≤ As := by dsimp [As]; positivity
  have hAi : 0 ≤ Ai := by dsimp [Ai]; positivity
  have hAm : 0 ≤ Am := by dsimp [Am]; positivity
  obtain ⟨R,hR,hbound⟩ := exists_three_plain_power_sum_le (4*k*As) (k*Ai) (3*k*Am)
    (2*(d:ℝ)-2*γ-β) (2*(d:ℝ)-4*γ) (2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ)
    (2*((d:ℝ)-γ)-β/2) (by linarith only [hβ]) (by linarith only [hβγ]) (by linarith only [hβη])
  refine ⟨R,hR,?_⟩
  intro L hL
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hsmall : L^(-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])
  have hs : (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)) = As*L^(2*(d:ℝ)-2*γ) := by
    have he := source_scale_inv_mul_nat_pow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 4) γ (2*d)
    have hn : ((2*d:ℕ):ℝ)-2*γ = 2*(d:ℝ)-2*γ := by push_cast; ring
    rw [hn] at he
    calc
      _ = Cs*((16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*d)) := by ring
      _ = _ := by rw [he]; dsimp [As]; norm_num; ring
  have hi : (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d))*
      (2/(16*sourceHalfScale L γ δ)) = Ai*L^(2*(d:ℝ)-4*γ) := by
    have he := source_scale_inv_sq_mul_nat_pow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 4) γ (2*d)
    have hn : ((2*d:ℕ):ℝ)-4*γ = 2*(d:ℝ)-4*γ := by push_cast; ring
    rw [hn] at he
    calc
      _ = 2*Cs*((16*sourceHalfScale L γ δ)⁻¹*(16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*d)) := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [he]; dsimp [Ai]; norm_num; ring
  have hm : (16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η) =
      Am*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ) := by
    have he := source_scale_rpow hLp (by norm_num : (0:ℝ) < 16) hδ
      (by norm_num : (0:ℝ) ≤ 4) γ 1 (2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)
    simp only [Real.rpow_neg_one,mul_one] at he
    calc
      _ = Cm*((16*sourceHalfScale L γ δ)⁻¹*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η)) := by ring
      _ = _ := by rw [he]; dsimp [Am]; norm_num; ring
  have hp : L^(2*(d:ℝ)-2*γ)*L^(-β) = L^(2*(d:ℝ)-2*γ-β) := by
    rw [← Real.rpow_add hLp]
    congr 1
  calc
    _ = k*(4*As*L^(2*(d:ℝ)-2*γ-β)+Ai*L^(2*(d:ℝ)-4*γ)+
        (1+2*L^(-β))*(Am*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ))) := by
      calc
        _ = k*(4*((16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d)))*L^(-β)+
          (16*sourceHalfScale L γ δ)⁻¹*(Cs*(4*L)^(2*d))*(2/(16*sourceHalfScale L γ δ))+
          (1+2*L^(-β))*((16*sourceHalfScale L γ δ)⁻¹*Cm*(4*L)^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η))) := by ring
        _ = _ := by rw [hi,hs,hm]; rw [show 4*(As*L^(2*(d:ℝ)-2*γ))*L^(-β) = 4*As*(L^(2*(d:ℝ)-2*γ)*L^(-β)) by ring,hp]
    _ ≤ k*(4*As*L^(2*(d:ℝ)-2*γ-β)+Ai*L^(2*(d:ℝ)-4*γ)+
        3*(Am*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ))) := by
      apply mul_le_mul_of_nonneg_left _ hk
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right (by linarith only [hsmall]) (by positivity)
    _ = (4*k*As)*L^(2*(d:ℝ)-2*γ-β)+(k*Ai)*L^(2*(d:ℝ)-4*γ)+
        (3*k*Am)*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η-2*γ) := by ring
    _ ≤ _ := hbound L hL

end WaveTurbulence.SumintPar
