/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SharpPositivePair
public import WaveTurbulence.Foundations.CountLemmas.AtomCount
public import WaveTurbulence.Foundations.CountLemmas.CountLemma
public import Mathlib.Algebra.Ring.GeomSum
public import WaveTurbulence.Foundations.VdCB.CircleCountingBridge
import Mathlib.Tactic

/-! # DH23 basiccount(1) uniformly over the two actual sign cases -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem large_gap_pair_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (a b : Mom d) (nk : Fin d → ℤ) (β : ℝ) (ε : ℤˣ),
      (ε = -1 → L^(-γ+η) ≤ ‖latticePoint L nk‖) →
      (CountLemmas.atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) ε).Finite ∧
      ((CountLemmas.atomPairSet L a b nk β (δ⁻¹*L^(-2*γ)) ε).ncard : ℝ) ≤
        C*δ⁻¹*L^((d : ℝ)-γ-η) := by
  obtain ⟨Cn,R,hB⟩ := CountLemmas.atomCountLemma_bound d hd γ hγ η hη hηmax
  let Cp : ℝ := 3^(d-2)*(2*(6*Real.pi+1284002))
  let C : ℝ := max Cp (max Cn 0)
  have hC : 0 ≤ C := (le_max_right Cn 0).trans (le_max_right Cp (max Cn 0))
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ a b nk β ε hgap
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨CountLemmas.finite_atomPairSet hLp a b nk β _ ε,?_⟩
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have hp := positive_pair_sharp_bound (by omega : 2 ≤ d) hL1 hδ hγ.2.le a b nk β
    have hη0 : η ≤ min γ (1-γ) := by linarith only [hη,hηmax]
    have hpow := Real.rpow_le_rpow_of_exponent_le hL1
      (by linarith only [hη0] : (d : ℝ)-γ-min γ (1-γ) ≤ (d : ℝ)-γ-η)
    have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
    have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le))
    have hc : Cp ≤ C := le_max_left _ _
    exact hp.trans (hm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hδ.1.le)) (by positivity)))
  · have hb := (hB L ((le_max_left R 1).trans hL) δ hδ β nk a b (0 : Mom d)).2.2.1 (hgap rfl)
    have hc : Cn ≤ C := (le_max_left Cn 0).trans (le_max_right Cp (max Cn 0))
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hδ.1.le)) (by positivity))

end WaveTurbulence.MoleProp
