/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPiece.Kernel
public import WaveTurbulence.Foundations.Spine.PieceArithmetic

/-! # C5a PIECE-MK: the marked piece bound (`MarkedPieceBoundAt`)

Main's `stage1_piece_bound_int` with the pointwise bound `kernel_bound` and the pin loss `L^{cP d nProt}` of the weight
mass moved into `markedExtra`. The extra exponent needs `1 ≤ P.d` (`extra_le`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKPiece
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open scoped Classical

/-- **The marked piece bound**, for parameters with `1 ≤ d`. -/
theorem markedPieceBoundAt_of_one_le_d {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (_hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P) :
    MarkedPieceBoundAt cP cθ P := by
  intro p R n hp hR hRmax π tt base roots hπ hnsb hnL val s hs0 hval
  obtain ⟨Ξ, _, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwbound, hD⟩ := hval
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  set M : ℝ := P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) with hM
  set cq : ℝ := cθ ^ (40 * P.ν) with hcq
  set Ek : ℝ := (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) with hEk
  set a0 : ℝ := cP * P.d * (π.nProt : ℝ) with ha0
  have hcq1 : 1 ≤ cq := Real.one_le_rpow hcθ (by have := hs.nu_pos; linarith)
  have hM0 : 0 ≤ M := by rw [hM]; exact mul_nonneg hC2 (Real.exp_pos _).le
  have hKle : ∀ ξ, ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ M * cq ^ π.Gsb.order * P.L ^ Ek := fun ξ =>
    kernel_bound hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt (ctr ξ) (edge ξ)
      (hinge ξ) (freq ξ) (hD ξ)
  have hMt0 : 0 ≤ M * cq ^ π.Gsb.order * P.L ^ Ek := by positivity
  have hnorm : ‖val‖ ≤ (∫ ξ, ‖w ξ‖ ∂μ) * (M * cq ^ π.Gsb.order * P.L ^ Ek) := by
    rw [hv]
    have h := norm_integral_le_of_norm_le (hwint.mul_const (M * cq ^ π.Gsb.order * P.L ^ Ek))
      (Filter.Eventually.of_forall (fun ξ => by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hKle ξ) (norm_nonneg _))))
    simpa only [integral_mul_const] using h
  set W : ℝ := ∫ ξ, ‖w ξ‖ ∂μ with hW
  have hW0 : 0 ≤ W := integral_nonneg fun ξ => norm_nonneg _
  have hLa : 0 < P.L ^ a0 := Real.rpow_pos_of_pos hL0 _
  have hden : 0 < s * P.L ^ a0 := mul_pos hs0 hLa
  set W' : ℝ := W / (s * P.L ^ a0) with hW'
  have hW'0 : 0 ≤ W' := div_nonneg hW0 hden.le
  have hwb : W' ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    rw [hW', div_le_iff₀ hden]
    calc W ≤ _ := hwbound
      _ = _ := by ring
  have hcls := class_piece_bound (C := P.C₁) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν)
    (n := n) (nsb := π.Gsb.order) (R := R) (m := π.Gsb.order + 2 * R) (W := W') (X := M) (H := P.C₂)
    (gsk := (π.gsk : ℝ)) (bsk := (π.bsk : ℝ)) (qsk := (π.Cs.hinges.card : ℝ))
    (gsb := (π.gsb : ℝ)) (ρsb := (π.Gsb.molecule.rho : ℝ))
    hs.c1_ge hs.delta_pos hs.delta_le hL1 hs.nu_pos (by linarith [hs.nu_small]) hs.nu_eta
    hs.eta_pos hs.eta_le hnsb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC2 hW'0 hM0 hwb (by rw [hM])
  have hcqn : cq ^ π.Gsb.order ≤ cq ^ n := pow_le_pow_right₀ hcq1 hnsb
  have hWeq : W = W' * (s * P.L ^ a0) := by rw [hW']; field_simp
  have hT0 : 0 ≤ P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    have := hs.c1_ge; have := hs.delta_pos; positivity
  have hmext : P.L ^ markedExtra cP π = P.L ^ a0 * P.L ^ Ek := by
    rw [← Real.rpow_add hL0]; congr 1; unfold markedExtra; simp only [ha0, hEk]; ring
  calc ‖val‖ ≤ W * (M * cq ^ π.Gsb.order * P.L ^ Ek) := hnorm
    _ = s * P.L ^ a0 * P.L ^ Ek * cq ^ π.Gsb.order * (W' * M) := by rw [hWeq]; ring
    _ ≤ s * P.L ^ a0 * P.L ^ Ek * cq ^ n *
        (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) := by
        gcongr
    _ = _ := by rw [hmext, mul_pow, mul_pow, hcq]; ring

end WaveTurbulence.Flower.FinalMKPiece
