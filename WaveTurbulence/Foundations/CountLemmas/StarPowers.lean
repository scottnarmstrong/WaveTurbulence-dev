/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.StarMonomials

/-! # Comparing the three full-star contributions with the target power -/

public section
namespace WaveTurbulence.CountLemmas

/-- No logarithmic loss is introduced in the zero/zero contribution. The
small auxiliary moment parameter is absorbed only in the other two terms. -/
theorem star_power_bound (d : ℕ) {L δ γ ε : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ 1-γ) (hε1 : 4*ε ≤ 1) :
    let τ := δ⁻¹*L^(-2*γ)
    τ^2*(4*L)^(3*(d : ℝ)+1)*((48*L)^(2*ε)*(1/(4*τ*L^2))^2+
      (48*L)^(-1+4*ε)*(1/(4*τ*L^2))+(48*L)^(-1 : ℝ)) ≤
    ((4 : ℝ)^(3*(d : ℝ)+1)*(48^(2*ε)+48^(-1+4*ε)+48^(-1 : ℝ)))*
      δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let A : ℝ := 3*(d : ℝ)+1
  let E : ℝ := 3*((d : ℝ)-γ)-min γ (1-γ)
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ) (Real.rpow_pos_of_pos hLp _)
  have hnn : L^(A+2*ε-4) ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL (by
    dsimp only [A,E]
    linarith only [hε,min_le_right γ (1-γ)])
  have hnz : L^(A-3+4*ε-2*γ) ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL (by
    dsimp only [A,E]
    linarith only [hε1,min_le_right γ (1-γ)])
  have hzz : L^(A-1-4*γ) ≤ L^E := Real.rpow_le_rpow_of_exponent_le hL (by
    dsimp only [A,E]
    linarith only [min_le_left γ (1-γ)])
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hδsq : 1 ≤ δ⁻¹^2 := by nlinarith only [hδi]
  have hδle : δ⁻¹ ≤ δ⁻¹^2 := by nlinarith only [hδi]
  have h₁ : L^(A+2*ε-4)/16 ≤ δ⁻¹^2*L^E :=
    (div_le_self (by positivity) (by norm_num : (1 : ℝ) ≤ 16)).trans
      ((by simpa only [one_mul] using mul_le_mul hδsq hnn (by positivity : 0 ≤ L^(A+2*ε-4)) (sq_nonneg δ⁻¹)))
  have h₂ : τ*L^(A-3+4*ε)/4 ≤ δ⁻¹^2*L^E := by
    rw [bandwidth_mul_rpow hLp]
    exact (div_le_self (by positivity) (by norm_num : (1 : ℝ) ≤ 4)).trans
      (mul_le_mul hδle hnz (by positivity) (sq_nonneg δ⁻¹))
  have h₃ : τ^2*L^(A-1) ≤ δ⁻¹^2*L^E := by
    rw [bandwidth_sq_mul_rpow hLp]
    exact mul_le_mul_of_nonneg_left hzz (sq_nonneg _)
  have hexpand : τ^2*(4*L)^A*((48*L)^(2*ε)*(1/(4*τ*L^2))^2+
      (48*L)^(-1+4*ε)*(1/(4*τ*L^2))+(48*L)^(-1 : ℝ)) =
      (4 : ℝ)^A*(48^(2*ε)*(L^(A+2*ε-4)/16)+
        48^(-1+4*ε)*(τ*L^(A-3+4*ε)/4)+48^(-1 : ℝ)*(τ^2*L^(A-1))) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hLp.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 48) hLp.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 48) hLp.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 48) hLp.le]
    have hz : τ^2*L^A*L^(-1 : ℝ) = τ^2*L^(A-1) := by
      rw [mul_assoc,← Real.rpow_add hLp]
      congr 2
    calc
      _ = (4 : ℝ)^A*(48^(2*ε)*(τ^2*L^A*L^(2*ε)*(1/(4*τ*L^2))^2)+
        48^(-1+4*ε)*(τ^2*L^A*L^(-1+4*ε)*(1/(4*τ*L^2)))+
        48^(-1 : ℝ)*(τ^2*L^A*L^(-1 : ℝ))) := by ring
      _ = _ := by rw [star_nn_monomial hLp hτ.ne',star_nz_monomial hLp hτ.ne',hz]
  rw [hexpand]
  calc
    _ ≤ (4 : ℝ)^A*(48^(2*ε)*(δ⁻¹^2*L^E)+48^(-1+4*ε)*(δ⁻¹^2*L^E)+
        48^(-1 : ℝ)*(δ⁻¹^2*L^E)) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
        (mul_le_mul_of_nonneg_left h₂ (by positivity))) (mul_le_mul_of_nonneg_left h₃ (by positivity))) (by positivity)
    _ = _ := by dsimp only [A,E]; ring

end WaveTurbulence.CountLemmas
