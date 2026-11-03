/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.StarTripleRaw
public import WaveTurbulence.Foundations.CountLemmas.StarPowers

/-! # The exact target power for the star triple count -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8, the selector `x-v`, with its exact power of L and δ.
The moment parameter depends only on γ, never on the bandwidth. -/
theorem coupledTriple_star_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 2 ≤ L → ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ a b c v : Mom d, ∀ α β : ℝ,
      ((coupledTripleSet L a b c v α β (δ⁻¹*L^(-2*γ)) 0).ncard : ℝ) ≤
      C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  let ε := (1-γ)/100
  have hε : 0 < ε := div_pos (sub_pos.mpr hγ.2) (by norm_num)
  have hε1 : ε < 1 := by dsimp only [ε]; linarith only [hγ.1]
  obtain ⟨C,hC,hb⟩ := exists_star_triple_raw_bound d hd ε hε hε1
  let K : ℝ := (4 : ℝ)^(3*(d : ℝ)+1)*(48^(2*ε)+48^(-1+4*ε)+48^(-1 : ℝ))
  refine ⟨C*K,by dsimp only [K]; positivity,?_⟩
  intro L hL δ hδ a b c v α β
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hτ : 0 < δ⁻¹*L^(-2*γ) := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hwin : 1/(δ⁻¹*L^(-2*γ)) ≤ 4*L^2 := by
    have hid : 1/(δ⁻¹*L^(-2*γ)) = δ*L^(2*γ) := by
      rw [show -2*γ = -(2*γ) by ring,Real.rpow_neg hLp.le]
      field_simp [hδ.1.ne',(Real.rpow_pos_of_pos hLp (2*γ)).ne']
    rw [hid]
    calc
      _ ≤ L^(2*γ) := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδ.2 (by positivity : 0 ≤ L^(2*γ))
      _ ≤ L^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hγ.2])
      _ ≤ 4*L^2 := by rw [Real.rpow_two]; nlinarith only [sq_nonneg L]
  have hc := hb L _ hL hτ hwin a b c v α β
  have hp := star_power_bound d hL1 hδ.1 hδ.2
    (show ε ≤ 1-γ by dsimp only [ε]; linarith only [hγ.2])
    (show 4*ε ≤ 1 by dsimp only [ε]; linarith only [hγ.1])
  have hh := mul_le_mul_of_nonneg_left hp hC.le
  exact hc.trans (by simpa only [K,mul_assoc] using hh)

end WaveTurbulence.CountLemmas
