/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtom
import Mathlib.Tactic

/-! # DH23 basiccount(1), the sharp same-sign exponent -/

@[expose] public section
set_option autoImplicit false
open Set
namespace WaveTurbulence.MoleProp

/-- DH23 Lemma A.3(1), first item, TeX L2099. The underlying shell estimate
retains both terms, rather than weakening them to TARGET's coarse endpoint. -/
theorem positive_pair_sharp_bound {d : ℕ} (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1)
    (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) :
    ((CountLemmas.atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) 1).ncard : ℝ) ≤
      (3^(d-2)*(2*(6*Real.pi+1284002)))*δ⁻¹*
        L^((d : ℝ)-γ-min γ (1-γ)) := by
  obtain ⟨m,hm⟩ : ∃ m, d = m+2 := ⟨d-2,by omega⟩
  subst d
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hW : (δ⁻¹*L^(-2*γ))*L^2 = δ⁻¹*L^(2-2*γ) := by
    rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hLp]
    congr 2
    ring
  have hW1 : 1 ≤ (δ⁻¹*L^(-2*γ))*L^2 := by
    rw [hW]
    exact one_le_mul_of_one_le_of_one_le hδi (Real.one_le_rpow hL (by linarith only [hγ]))
  have hc := CountLemmas.positive_atom_shell_bound (τ := δ⁻¹*L^(-2*γ)) hLp (by positivity) hW1 a b nk β
  have he0 : 2-2*γ ≤ 2-γ-min γ (1-γ) := by have := min_le_left γ (1-γ); linarith only [this]
  have he1 : 1 ≤ 2-γ-min γ (1-γ) := by have := min_le_right γ (1-γ); linarith only [this]
  have htail : (δ⁻¹*L^(-2*γ))*L^2+L ≤ 2*δ⁻¹*L^(2-γ-min γ (1-γ)) := by
    rw [hW]
    have h₁ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he0) (inv_nonneg.mpr hδ.1.le)
    have h₂ : L ≤ L^(2-γ-min γ (1-γ)) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL he1
    have h₃ : L^(2-γ-min γ (1-γ)) ≤ δ⁻¹*L^(2-γ-min γ (1-γ)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hδi (by positivity : 0 ≤ L^(2-γ-min γ (1-γ)))
    linarith only [h₁,h₂,h₃]
  have hb := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ (2*L+1)^m*(6*Real.pi+1284002))
  have hr := CountLemmas.box_times_rpow_bound m hL
    (by positivity : 0 ≤ 2*(6*Real.pi+1284002)) (inv_nonneg.mpr hδ.1.le) (e := 2-γ-min γ (1-γ))
  have hscale : (m : ℝ)+(2-γ-min γ (1-γ)) = ((m+2 : ℕ) : ℝ)-γ-min γ (1-γ) := by push_cast; ring
  rw [hscale] at hr
  simpa only [Nat.add_sub_cancel] using (hc.trans hb).trans (by convert hr using 1; ring)

end WaveTurbulence.MoleProp
