/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairGrowth
import Mathlib.Tactic

/-! # Power saving from the small internal-gap radius -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Asymptotics CountLemmas

noncomputable def appbSmallGapMajorant (d : ℕ) (δ γ : ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  let R := L^(-γ+2*min γ (1-γ)/3)
  let A := (3^d*L^d)*(3^(d-1)*L^(d-1))
  15^d*L^d+2*A*R^d+2*(A*(4*(d : ℝ)*appbWidth δ γ m L*L))*R^(d-1)

theorem appb_small_gap_exponents (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    (d : ℝ) ≤ 2*((d : ℝ)-γ)-2*min γ (1-γ)/3 ∧
    (d : ℝ)+(d-1 : ℕ)+(-γ+2*min γ (1-γ)/3)*d ≤
      2*((d : ℝ)-γ)-2*min γ (1-γ)/3 ∧
    (d : ℝ)+(d-1 : ℕ)+1-2*γ+(-γ+2*min γ (1-γ)/3)*(d-1 : ℕ) ≤
      2*((d : ℝ)-γ)-2*min γ (1-γ)/3 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsub : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hg0 := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hleft := min_le_left γ (1-γ)
  have hright := min_le_right γ (1-γ)
  have hhalf : min γ (1-γ) ≤ 1/2 := by linarith only [hleft,hright]
  have ha : 0 ≤ γ-2*min γ (1-γ)/3 := by linarith only [hg0,hleft]
  have hmul3 := mul_le_mul_of_nonneg_right hdR ha
  have hmul2 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (d : ℝ)-1 by linarith only [hdR]) ha
  rw [hsub]
  constructor
  · linarith only [hdR,hγ.2,hhalf]
  constructor
  · nlinarith only [hmul3,hleft,hhalf]
  · nlinarith only [hmul2,hleft]

theorem appb_growth_small_gap_majorant (d : ℕ) (hd : 3 ≤ d) (δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    appbSmallGapMajorant d δ γ m =O[atTop]
      (fun L => L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3+min γ (1-γ)/100)) := by
  let ε := min γ (1-γ)/100
  let r := -γ+2*min γ (1-γ)/3
  have hε : 0 < ε := div_pos (lt_min hγ.1 (sub_pos.mpr hγ.2)) (by norm_num)
  obtain ⟨h0,h1,h2⟩ := appb_small_gap_exponents d hd γ hγ
  have hA := growth_mul ((growth_natpow d).const_mul_left ((3 : ℝ)^d))
    ((growth_natpow (d-1)).const_mul_left ((3 : ℝ)^(d-1)))
    (c := (d : ℝ)+(d-1 : ℕ)) le_rfl
  have hR := growth_rpow r
  have hfirst := growth_mul (hA.const_mul_left 2) (growth_pow hR d)
    (c := 2*((d : ℝ)-γ)-2*min γ (1-γ)/3+ε) (by dsimp only [r]; linarith only [h1,hε])
  have hwidth := appb_growth_width δ γ m hε
  have hτL := growth_mul (hwidth.const_mul_left (4*(d : ℝ))) growth_id
    (c := 1-2*γ+ε) (by ring_nf; exact le_rfl)
  have hsecond := growth_mul ((growth_mul hA hτL le_rfl).const_mul_left 2)
    (growth_pow hR (d-1))
    (c := 2*((d : ℝ)-γ)-2*min γ (1-γ)/3+ε) (by dsimp only [r]; linarith only [h2])
  have htotal := growth_add
    (growth_add ((growth_natpow d).const_mul_left ((15 : ℝ)^d)) hfirst
      (by linarith only [h0,hε]) le_rfl) hsecond le_rfl le_rfl
  convert htotal using 1
  funext L
  unfold appbSmallGapMajorant
  dsimp only [r]

theorem appb_small_gap_majorant_eventual (d : ℕ) (hd : 3 ≤ d) (δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, appbSmallGapMajorant d δ γ m L ≤
      L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  apply growth_eventually_le (appb_growth_small_gap_majorant d hd δ γ hγ m)
  have hpos := lt_min hγ.1 (sub_pos.mpr hγ.2)
  linarith only [hpos]

end WaveTurbulence.Mole
