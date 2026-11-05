/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormGeometricTail
public import WaveTurbulence.Foundations.XChain.GeometricInputBound
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! The source layergarden estimates bound the actual finite couple-remainder sum in the full spatial norm. -/
public section
namespace WaveTurbulence.Induct
open Finset Set
open scoped ENNReal

theorem coupleRemainder_sum_SNorm_bound (P : WTParams) (hG : LayergardenBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hδ : 0 < P.δ)
    (hsmall : P.δ ^ (2 * P.ν) ≤ 1 / 2) (Ncut : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (fun k => ∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) ≤
      ENNReal.ofReal (2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)) := by
  let C : ℝ := P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)
  let r : ℝ := P.δ ^ (2 * P.ν)
  have hC : 0 ≤ C := Real.rpow_nonneg hL.le _
  have hr : 0 ≤ r := Real.rpow_nonneg hδ.le _
  have hA : 4 * P.Lambda (p + 1) ≠ 0 := by
    have h := lambda_succ_ge P hd hp
    omega
  have horder (N : ℕ) (hN : N ∈ range (Ncut + 1)) :
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (C * r ^ N) := by
    have h := (hG p hp R hR t ht N (by
      have hn := mem_range.mp hN
      omega)).2.2
    have he : P.δ ^ (2 * P.ν * N) = r ^ N := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    rw [he] at h
    exact h
  have hcont (N : ℕ) (hN : N ∈ range (Ncut + 1)) :
      ContDiff ℝ (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) :=
    contDiff_of_SNorm_bound hA _ _ (horder N hN)
  have hsum := SNorm_finset_sum_bound (range (Ncut + 1))
    (fun N => coupleRemainder P R p N t) (fun N => C * r ^ N) hcont
    (fun N _ => mul_nonneg hC (pow_nonneg hr _)) horder
  refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← mul_sum]
  have h := mul_le_mul_of_nonneg_left (sum_geometric_le_two hr hsmall (Ncut + 1)) hC
  simpa only [mul_comm C 2] using h

end WaveTurbulence.Induct
