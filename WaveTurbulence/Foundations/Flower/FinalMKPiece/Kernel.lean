/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.FinalMKPiece.Interp

/-! # C5a PIECE-MK: the pointwise kernel bound of a marked piece

Crude (`CoarseSplicedAtMK`, split `= joints ∪ prot`) and fine (`FineSplicedAtMK`, `E = prot`) bounds interpolated at
`θ = 40ν` (`mk_interpolation`). The extra exponent fits `markedExtra` once `1 ≤ d` (SCOPE §4.4). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open scoped Classical

theorem joints_card_le {w : ℕ} {G : Garden w} (S : SurvivorData G) : S.joints.card ≤ 2 * S.m := by
  unfold SurvivorData.joints
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ i : Fin S.m, ({(S.surv i).upper, (S.surv i).lower} : Finset _).card ≤ ∑ _i : Fin S.m, 2 :=
        Finset.sum_le_sum fun i _ => Finset.card_le_two
    _ = 2 * S.m := by simp [mul_comm]

/-- The arithmetic of the extras: coarse `40ν · 80d · |split|` and fine `2m + 2(5d+4)|E|` fit `markedExtra`. -/
theorem extra_le {d ν m np K E : ℝ} (hd : 1 ≤ d) (_hν0 : 0 ≤ ν) (hν : 40 * ν ≤ 1 / 100) (hm : 0 ≤ m)
    (hnp : 0 ≤ np) (hK0 : 0 ≤ K) (hK : K ≤ 2 * m + 2 * np) (_hE0 : 0 ≤ E) (hE : E ≤ 2 * np) :
    40 * ν * (80 * d * K) + (2 * m + 2 * ((5 * d + 4) * E)) ≤
      (60 * d + 2) * (2 * m + 2 * np) + 2 * m := by
  have h1 : 40 * ν * (80 * d * K) ≤ (1 / 100) * (80 * d * K) :=
    mul_le_mul_of_nonneg_right hν (by positivity)
  have h2 : d * K ≤ d * (2 * m + 2 * np) := mul_le_mul_of_nonneg_left hK (by linarith)
  have h3 : (5 * d + 4) * E ≤ (5 * d + 4) * (2 * np) :=
    mul_le_mul_of_nonneg_left hE (by linarith)
  have h4 : 0 ≤ (d - 1) * np := mul_nonneg (by linarith) hnp
  have h5 : 0 ≤ d * m := by positivity
  nlinarith


theorem pow_card_le {N : ℕ} {L o : ℝ} (hL : 1 ≤ L) (ho : o + 1 ≤ L) (ho0 : 0 ≤ o) :
    ((o + 1) * L) ^ N ≤ L ^ ((2 * N : ℕ) : ℝ) := by
  have hL0 : 0 < L := by linarith
  have h1 : (o + 1) * L ≤ L * L := mul_le_mul_of_nonneg_right ho hL0.le
  calc ((o + 1) * L) ^ N ≤ (L * L) ^ N := pow_le_pow_left₀ (by positivity) h1 N
    _ = L ^ ((2 * N : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, pow_mul, sq]

end WaveTurbulence.Flower.FinalMKPiece
