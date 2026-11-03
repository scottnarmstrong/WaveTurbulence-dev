/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.SmallPairGrowth

/-! # The strict power saving of the sparse/dense pair majorant -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

/-- Choosing θ=L^ε and R=L^(-ε), with four ε smaller than 2γ-1,
leaves a strict power saving in both the sparse and dense contributions. -/
theorem growth_pairDenseMajorant (d : ℕ) (hd : 3 ≤ d) (c δ γ ε : ℝ)
    (hγ : γ ≤ 1) (hε : 0 < ε) (hgap : 4*ε ≤ 2*γ-1) :
    (pairDenseMajorant d c δ γ ε) =O[atTop] (fun L : ℝ => L^(2*(d : ℝ)-2*γ-ε)) := by
  let E := 2*(d : ℝ)-2*γ-ε
  have hbox := growth_box 2 (d-1)
  have hU := growth_pairStripFactor d c δ γ hγ
  have hfirst := growth_mul (growth_mul hbox hU (c := (d : ℝ)+1-2*γ) (by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    ring_nf
    exact le_rfl)) (growth_div_rpow (growth_natpow (d-1)) ε) (c := E) (by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
      dsimp only [E]
      ring_nf
      exact le_rfl)
  have hτ := growth_mul ((growth_bandwidth δ γ).const_mul_left (2*(d : ℝ))) growth_id
    (c := 1-2*γ) (by ring_nf; exact le_rfl)
  have hdiv := growth_div_rpow hτ (-ε)
  have hone := growth_add hdiv (growth_const 1) (c := 0)
    (by linarith only [hgap,hε]) le_rfl
  have hcap := growth_mul hbox hone (c := (d : ℝ)-1) (by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num)
  have hW := growth_mul (growth_bandwidth δ γ) (growth_natpow 2)
    (c := 2-2*γ) (by norm_num)
  have hW2 := growth_pow hW 2
  have hcoeff := (growth_natpow (d-2)).const_mul_left (densePairConstant d)
  have hmain := growth_mul hcoeff hW2 (c := (d : ℝ)+2-4*γ) (by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
    ring_nf
    exact le_rfl)
  have hθ := growth_pow (growth_rpow ε) 2
  have hθmain := growth_mul hmain hθ (c := (d : ℝ)+2-4*γ+2*ε) (by
    norm_num
    ring_nf
    exact le_rfl)
  have hlogmain := growth_mul hθmain (growth_log_sq hε)
    (c := (d : ℝ)+2-4*γ+3*ε) (by ring_nf; exact le_rfl)
  have hsecond := growth_mul hlogmain hcap (c := E) (by
    dsimp only [E]
    linarith only [hgap])
  exact growth_add hfirst hsecond le_rfl le_rfl

end WaveTurbulence.CountLemmas
