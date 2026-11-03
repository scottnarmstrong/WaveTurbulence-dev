/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtomReduction
public import WaveTurbulence.Foundations.CountLemmas.StripPowers

/-! # The same-sign atomic bound -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.9, same-sign energy bound. The coarse planar shell estimate
suffices; no Huxley or improved discrepancy exponent is needed. -/
theorem positive_atom_energy_bound {d : ℕ} (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1)
    (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) :
    ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) 1).ncard : ℝ) ≤
      (3^(d-2)*(2*(6*Real.pi+1284002)))*δ⁻¹*L^((d : ℝ)+1-2*γ) := by
  obtain ⟨m,hm⟩ : ∃ m, d = m+2 := ⟨d-2,by omega⟩
  subst d
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hW : (δ⁻¹*L^(-2*γ))*L^2 = δ⁻¹*L^(2-2*γ) := by
    rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hLp]
    congr 2
    ring
  have hW1 : 1 ≤ (δ⁻¹*L^(-2*γ))*L^2 := by
    rw [hW]
    exact one_le_mul_of_one_le_of_one_le hδi
      (Real.one_le_rpow hL (by linarith only [hγ]))
  have hc := positive_atom_shell_bound (τ := δ⁻¹*L^(-2*γ)) hLp (by positivity) hW1 a b nk β
  have htail : (δ⁻¹*L^(-2*γ))*L^2+L ≤ 2*δ⁻¹*L^(3-2*γ) := by
    rw [hW]
    have h₁ : L^(2-2*γ) ≤ L^(3-2*γ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have h₂ : L ≤ L^(3-2*γ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL (show (1 : ℝ) ≤ 3-2*γ by linarith only [hγ])
    have h₃ : L^(3-2*γ) ≤ δ⁻¹*L^(3-2*γ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hδi (by positivity : 0 ≤ L^(3-2*γ))
    have h₄ := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr hδ.1.le)
    linarith only [h₂,h₃,h₄]
  have hb := mul_le_mul_of_nonneg_left htail
    (by positivity : 0 ≤ (2*L+1)^m*(6*Real.pi+1284002))
  have hr := box_times_rpow_bound m hL
    (by positivity : 0 ≤ 2*(6*Real.pi+1284002)) (inv_nonneg.mpr hδ.1.le) (e := 3-2*γ)
  have hscale : ((m : ℝ)+(3-2*γ)) = ((m+2 : ℕ) : ℝ)+1-2*γ := by push_cast; ring
  rw [hscale] at hr
  simpa only [Nat.add_sub_cancel] using (hc.trans hb).trans (by convert hr using 1; ring)

end WaveTurbulence.CountLemmas
