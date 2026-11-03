/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairMajorants

/-! # The strict power saving of the small-radius pair majorant -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

theorem growth_pairStripFactor (d : ℕ) (c δ γ : ℝ) (hγ : γ ≤ 1) :
    (pairStripFactor d c δ γ) =O[atTop] (fun L : ℝ => L^(2-2*γ)) := by
  have hh := growth_mul (growth_bandwidth δ γ) (growth_natpow 2)
    (by norm_num : -2*γ+(2 : ℝ) ≤ 2-2*γ)
  have hg := growth_one_add (hh.const_mul_left (2*(d : ℝ)*c)) le_rfl
    (show 0 ≤ 2-2*γ by linarith only [hγ])
  convert hg using 1
  ext L
  dsimp only [pairStripFactor]
  ring

theorem growth_pairRadialFactor (d : ℕ) (hd : 1 ≤ d) (c δ γ : ℝ) (hγ : γ ≤ 1) :
    (pairRadialFactor d c δ γ) =O[atTop] (fun L : ℝ => L^(2*(d : ℝ)-2*γ)) := by
  have hh := growth_pow ((growth_natpow (d-1)).const_mul_left ((3 : ℝ)^(d-1))) 2
  have hg := growth_mul hh (growth_pairStripFactor d c δ γ hγ) (c := 2*(d : ℝ)-2*γ) (by
    rw [Nat.cast_sub hd]
    norm_num
    ring_nf
    exact le_rfl)
  exact hg

theorem growth_pairSmallMajorant (d : ℕ) (hd : 3 ≤ d) (c δ γ ε : ℝ)
    (hγ : (1 : ℝ)/2 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (pairSmallMajorant d c δ γ ε) =O[atTop] (fun L : ℝ => L^(2*(d : ℝ)-2*γ-ε)) := by
  let E := 2*(d : ℝ)-2*γ-ε
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hA := growth_pairRadialFactor d (by omega) c δ γ hγ1
  have hzero := (growth_natpow d).const_mul_left ((15 : ℝ)^d)
  have hfirst := growth_mul (hA.const_mul_left 2) (growth_pow (growth_rpow (-ε)) (d-1))
    (c := E) (by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
      have hh := mul_nonneg hε (by linarith only [hdR] : 0 ≤ (d : ℝ)-2)
      dsimp only [E]
      nlinarith only [hh])
  have hτ := growth_mul ((growth_bandwidth δ γ).const_mul_left (4*(d : ℝ))) growth_id
    (c := 1-2*γ) (by ring_nf; exact le_rfl)
  have hsecond := growth_mul (growth_mul hA hτ (by rfl : (2*(d : ℝ)-2*γ)+(1-2*γ) ≤ (2*(d : ℝ)-2*γ)+(1-2*γ)) |>.const_mul_left 2)
    (growth_pow (growth_rpow (-ε)) (d-2)) (c := E) (by
      rw [Nat.cast_sub (by omega : 2 ≤ d)]
      norm_num
      have hh := mul_nonneg hε (by linarith only [hdR] : 0 ≤ (d : ℝ)-3)
      dsimp only [E]
      nlinarith only [hh,hγ])
  have hsum := growth_add (growth_add hzero hfirst (c := E)
    (by dsimp only [E]; linarith only [hdR,hγ1,hε1]) le_rfl) hsecond le_rfl le_rfl
  exact hsum

end WaveTurbulence.CountLemmas
