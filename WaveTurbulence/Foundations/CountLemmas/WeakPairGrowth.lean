/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DensePairGrowth
public import WaveTurbulence.Foundations.CountLemmas.PairFiberCap

/-! # Growth of the dyadically summed density majorant -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

/-- The low-density contribution and the weighted estcross contribution. -/
@[expose] noncomputable def pairWeakMajorant (d : ℕ) (c δ γ r L : ℝ) : ℝ :=
  2*((2*L+1)^(d-1)*pairStripFactor d c δ γ L)*(L^(d-1)/L^r)+
    4*(densePairConstant d*L^(d-2)*((δ⁻¹*L^(-2*γ))*L^2)^2*(1+Real.log L)^2)*
      (pairFiberCap d)^2*L^(d-1)*L^r

/-- Dyadic density summation leaves only one θ power. A free positive log
slack is kept for the final source-scale comparison. -/
theorem growth_pairWeakMajorant (d : ℕ) (hd : 3 ≤ d) (c δ γ r η A : ℝ)
    (hγ : γ ≤ 1) (hη : 0 < η)
    (hfirst : 2*(d : ℝ)-2*γ-r ≤ A)
    (hsecond : 2*(d : ℝ)+1-4*γ+r+η ≤ A) :
    pairWeakMajorant d c δ γ r =O[atTop] (fun L : ℝ => L^A) := by
  have hbox := growth_box 2 (d-1)
  have hU := growth_pairStripFactor d c δ γ hγ
  have hlo := growth_mul (growth_mul hbox hU (c := (d : ℝ)+1-2*γ) (by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    ring_nf
    exact le_rfl) |>.const_mul_left 2) (growth_div_rpow (growth_natpow (d-1)) r) (c := A) (by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
      linarith only [hfirst])
  have hW := growth_mul (growth_bandwidth δ γ) (growth_natpow 2)
    (c := 2-2*γ) (by norm_num)
  have hmain := growth_mul ((growth_natpow (d-2)).const_mul_left (densePairConstant d))
    (growth_pow hW 2) (c := (d : ℝ)+2-4*γ) (by
      rw [Nat.cast_sub (by omega : 2 ≤ d)]
      norm_num
      ring_nf
      exact le_rfl)
  have hlog := growth_mul hmain (growth_log_sq hη) (c := (d : ℝ)+2-4*γ+η) le_rfl
  have hconst : (fun L => 4*(densePairConstant d*L^(d-2)*((δ⁻¹*L^(-2*γ))*L^2)^2*(1+Real.log L)^2)*(pairFiberCap d)^2) =O[atTop]
      (fun L => L^((d : ℝ)+2-4*γ+η)) := by
    convert hlog.const_mul_left (4*(pairFiberCap d)^2) using 1
    ext L
    ring
  have hdim := growth_mul hconst (growth_natpow (d-1))
    (c := 2*(d : ℝ)+1-4*γ+η) (by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
      ring_nf
      exact le_rfl)
  have hhi := growth_mul hdim (growth_rpow r) (c := A) (by linarith only [hsecond])
  exact growth_add hlo hhi le_rfl le_rfl

end WaveTurbulence.CountLemmas
