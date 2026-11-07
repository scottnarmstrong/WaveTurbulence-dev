/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PositiveAtomReduction
public import WaveTurbulence.Foundations.CountLemmas.StripPowers
import Mathlib.Tactic

/-! # DH23 basiccount(1): the sharp same-sign pair exponent

The already proved planar shell bound gives W+L. Keeping this sum instead
of replacing it by the coarser TARGET exponent gives precisely the
Appendix B saving gamma0 = min(gamma,1-gamma).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set CountLemmas

/-- DH23 Lemma A.3 basiccount(1), same-sign case, for actual localized
lattice pairs and arbitrary conservation and energy centers. -/
theorem appb_positive_pair_bound {d : ℕ} (hd : 2 ≤ d) {L δ γ : ℝ}
    (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ≤ 1)
    (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) :
    ((atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) 1).ncard : ℝ) ≤
      (2*3^(d-2)*(6*Real.pi+1284002))*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
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
  let e := 2-γ-min γ (1-γ)
  have hea : 2-2*γ ≤ e := by dsimp only [e]; linarith only [min_le_left γ (1-γ)]
  have heb : 1 ≤ e := by dsimp only [e]; linarith only [min_le_right γ (1-γ)]
  have hpa := Real.rpow_le_rpow_of_exponent_le hL hea
  have hpb : L ≤ L^e := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL heb
  have hpd : L^e ≤ δ⁻¹*L^e := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hδi (by positivity : 0 ≤ L^e)
  have htail : (δ⁻¹*L^(-2*γ))*L^2+L ≤ 2*δ⁻¹*L^e := by
    rw [hW]
    have ha := mul_le_mul_of_nonneg_left hpa (inv_nonneg.mpr hδ.1.le)
    linarith only [ha,hpb,hpd]
  have hbox : (2*L+1)^m ≤ 3^m*L^m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) m
  have hK : 0 ≤ (6*Real.pi+1284002 : ℝ) := by positivity
  calc
    _ ≤ (2*L+1)^m*(6*Real.pi+1284002)*((δ⁻¹*L^(-2*γ))*L^2+L) := hc
    _ ≤ (3^m*L^m)*(6*Real.pi+1284002)*(2*δ⁻¹*L^e) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hbox hK) htail (by positivity) (by positivity)
    _ = _ := by
      have hpow : L^m*L^e = L^(((m+2 : ℕ) : ℝ)-γ-min γ (1-γ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_add hLp]
        congr 1
        dsimp only [e]
        push_cast
        ring
      have hm : m+2-2 = m := by omega
      rw [hm]
      calc
        _ = (2*3^m*(6*Real.pi+1284002))*δ⁻¹*(L^m*L^e) := by ring
        _ = _ := by rw [hpow]

end WaveTurbulence.Mole
