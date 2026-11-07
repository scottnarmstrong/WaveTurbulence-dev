/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! # Finite energy-center bins without enlarging every atomic window -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset

/-- A cut energy window of size N atomic windows is covered by a finite
number of original-width windows. This is used only at changed vertices. -/
def appbEnergyBins (N : ℕ) : Finset ℤ := Icc (-(N : ℤ)-1) N

theorem appbEnergyBins_card (N : ℕ) : (appbEnergyBins N).card = 2*N+2 := by
  simp only [appbEnergyBins,Int.card_Icc]
  omega

theorem appb_exists_energy_bin (N : ℕ) {τ : ℝ} (hτ : 0 < τ) (x β : ℝ)
    (hx : |x-β| ≤ N*τ) :
    ∃ i ∈ appbEnergyBins N, |x-(β+(i : ℝ)*τ)| ≤ τ := by
  let y := (x-β)/τ
  let i := Int.floor y
  have hfloor : (i : ℝ) ≤ y := Int.floor_le y
  have hceil : y < (i : ℝ)+1 := Int.lt_floor_add_one y
  have hy : -(N : ℝ) ≤ y ∧ y ≤ N := by
    obtain ⟨hl,hr⟩ := abs_le.mp hx
    constructor
    · apply (le_div_iff₀ hτ).mpr
      nlinarith only [hl]
    · exact (div_le_iff₀ hτ).mpr hr
  have hiL : -(N : ℤ)-1 ≤ i := by
    have hh : -(N : ℝ)-1 ≤ (i : ℝ) := by linarith only [hy.1,hceil]
    exact_mod_cast hh
  have hiR : i ≤ (N : ℤ) := by exact_mod_cast hfloor.trans hy.2
  refine ⟨i,mem_Icc.mpr ⟨hiL,hiR⟩,?_⟩
  have he : x-(β+(i : ℝ)*τ) = (y-(i : ℝ))*τ := by
    dsimp only [y]
    field_simp
    ring
  rw [he,abs_mul,abs_of_pos hτ,abs_of_nonneg (sub_nonneg.mpr hfloor)]
  have hh : y-(i : ℝ) ≤ 1 := by linarith only [hceil]
  exact (mul_le_mul_of_nonneg_right hh hτ.le).trans_eq (one_mul τ)

end WaveTurbulence.Mole
