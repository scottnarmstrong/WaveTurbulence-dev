/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPiece.Bound
public import WaveTurbulence.Foundations.Spine.ClassSumBound

/-! # C5a PIECE-MK: the class sum (`MarkedSumBoundAt`)

Main's `stage1_sum_bound_int` with marked pieces: the per-piece extra is a uniform `L^X`, divided out before
`class_sum_bound`, with the class count `Stage1Counts` of the forgetful data. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open scoped Classical

/-- **The marked class sum** from the marked piece bound. -/
theorem markedSumBoundAt {P : WTParams} (hs : PieceSmall P) {cP cθ : ℝ} (X : ℝ) (hcθ : 1 ≤ cθ)
    (hpb : MarkedPieceBoundAt cP cθ P) : MarkedSumBoundAt cP cθ X P := by
  intro p R n hp hR hRmax S tt base roots C₀ Cl hCl cls s hs0 hsound hnsb hnL hrep hX hcnt hT2 hS2
  let _ := S.fin
  obtain ⟨hrb, hgb, hpc⟩ := hcnt
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hC1 : 0 < P.C₁ := by linarith [hs.c1_ge]
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  have hLX : 0 < P.L ^ X := Real.rpow_pos_of_pos hL0 _
  have hsX : 0 < s * P.L ^ X := mul_pos hs0 hLX
  have hcq1 : 0 ≤ cθ ^ (40 * P.ν) := Real.rpow_nonneg (by linarith) _
  have hpiece : ∀ π, ‖S.val π / ((s * P.L ^ X : ℝ) : ℂ)‖ ≤ P.C₂ *
      (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
      (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    intro π
    have h := hpb hp hR hRmax (S.piece π) tt base roots (hsound π) (hnsb π) hnL (S.val π) s hs0 (hrep π)
    have hme : P.L ^ markedExtra cP (S.piece π) ≤ P.L ^ X :=
      Real.rpow_le_rpow_of_exponent_le hL1 (hX π)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsX.le, div_le_iff₀ hsX]
    have hRn : R ≤ 2 * n := by
      have h1 := (hsound π).bond_count
      have h2 := hnsb π
      omega
    have hCn : P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤ P.C₁ ^ (5 * n) :=
      pow_le_pow_right₀ hs.c1_ge (by have := hnsb π; omega)
    have hδp : (0 : ℝ) ≤ P.δ ^ (10 * P.ν) := Real.rpow_nonneg hs.delta_pos.le _
    have hcore : (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) ≤
        (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by
      calc (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)
          ≤ (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (5 * n) :=
            mul_le_mul_of_nonneg_left hCn (by positivity)
        _ = (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n := by
            rw [pow_mul, ← mul_pow]; congr 1; ring
    have hrw : P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        (P.L ^ (-(P.ν * P.η))) ^ (S.piece π).gbar * (P.L ^ (-P.η ^ 6 / 4)) ^ (S.piece π).rbar *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) =
        P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
      rw [← Real.rpow_mul_natCast hL0.le, ← Real.rpow_mul_natCast hL0.le]
      simp only [Stage1PieceD.gbar, Stage1PieceD.rbar, Nat.cast_add]
      ring_nf
    rw [hrw]
    have hL1' : 0 ≤ P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) :=
      Real.rpow_nonneg hL0.le _
    have hL2 : 0 ≤ P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
        (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) := Real.rpow_nonneg hL0.le _
    have hL3 : 0 ≤ P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := Real.rpow_nonneg hL0.le _
    have hmain : P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
        P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) ≤
        P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
      calc _ = P.C₂ * ((cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
              P.C₁ ^ ((S.piece π).Gsb.order + 2 * R)) *
            (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
            P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
              (((S.piece π).Cs.hinges.card : ℕ) : ℝ)) / 4) *
            P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by ring
        _ ≤ _ := by gcongr
    have hpos : 0 ≤ P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n *
        P.C₁ ^ ((S.piece π).Gsb.order + 2 * R) *
        (P.L ^ (-(P.ν * P.η) * (((S.piece π).gsk : ℝ) + ((S.piece π).gsb : ℝ)))) *
        P.L ^ (-P.η ^ 6 * ((((S.piece π).Gsb.molecule.rho : ℝ)) +
          (((S.piece π).Cs.hinges.card : ℝ))) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by positivity
    have key : ∀ T T' : ℝ, 0 ≤ T → T ≤ T' → ‖S.val π‖ ≤ s * P.L ^ markedExtra cP (S.piece π) * T →
        ‖S.val π‖ ≤ T' * (s * P.L ^ X) := by
      intro T T' hT hTT' hh
      calc ‖S.val π‖ ≤ s * P.L ^ markedExtra cP (S.piece π) * T := hh
        _ ≤ s * P.L ^ X * T := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hme hs0.le) hT
        _ ≤ s * P.L ^ X * T' := mul_le_mul_of_nonneg_left hTT' hsX.le
        _ = T' * (s * P.L ^ X) := by ring
    exact key _ _ hpos hmain h
  have hdelta : (0 : ℝ) ≤ cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν) :=
    mul_nonneg (mul_nonneg hcq1 (by positivity)) (Real.rpow_nonneg hs.delta_pos.le _)
  have hcls := class_sum_bound (fun π => S.val π / ((s * P.L ^ X : ℝ) : ℂ))
    (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R (6 * C₀)
    P.C₂ (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) (P.L ^ (-(P.ν * P.η))) (P.L ^ (-P.η ^ 6 / 4))
    (P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) P.C₂ hC2 hdelta (Real.rpow_nonneg hL0.le _)
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _) hC2 hpiece hrb hgb
    (piece_count_of_direct_count (fun π => (S.piece π).gbar) (fun π => (S.piece π).rbar) n R C₀ P.C₂
      hC2 (by exact hpc)) hT2 hS2
  have hsum : ∑ π, S.val π / ((s * P.L ^ X : ℝ) : ℂ) = (∑ π, S.val π) / ((s * P.L ^ X : ℝ) : ℂ) := by
    rw [Finset.sum_div]
  rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hsX.le, div_le_iff₀ hsX] at hcls
  refine hcls.trans_eq ?_
  ring

end WaveTurbulence.Flower.FinalMKPiece
