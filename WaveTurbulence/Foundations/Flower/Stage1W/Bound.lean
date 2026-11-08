/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.ThreeInputs
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # STAGE1W-GLUE: Bound (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 9. R5: the consumer of the internal `(C₁ δ^{10ν})^n` stage (statement only) -/

/-- The frontier-weighted analogue of main's `LGSpine.stage1_type_bound` (Spine/Stage1TypeBound.lean): the gate's
`RepresentsInt` conjunct (size `cψ^{16N} s`) feeds main's `stage1_core_bound_int` unchanged, so the weighted garden
sum keeps main's internal `δ^{8νN}` (from `(C₁⁶δ^{10ν})^N`, Spine/Stage1SumBound.lean), not the `δ^{2νN}` export.
STAGE1W-impl proves it (weighted `sum_eq_sum_pieces` + summability from `‖g‖ ≤ cψ`). -/
def Stage1TypeBoundFW : Prop :=
  ∀ (C₀ : ℕ) (P : WTParams), PieceSmall P → CoarseSplicedAt P → LadderFourierAt P → FinalCountAt P →
    FinalAbsorptionAt (6 * C₀) P → 1 ≤ Real.log P.L → 1 ≤ P.d → Stage1ReductionAtFW C₀ P →
    ∀ {p R N : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) → 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
    ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
    ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
      (∀ j x, (g j x).im = 0) →
    ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
    ‖∑ LG ∈ A, valueW U.toLF tt base roots LG (fwWeight p g base LG)‖ ≤ cψ ^ (16 * N) * s *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70))))

/-- The δ-budget the cores ask for (`δ^{6νN}`), once `cψ^{16} δ^{2ν} ≤ 1` (cψ depends on `d` only, so this is a
δ-threshold chosen after `d`, before `L`): the arithmetic step after `Stage1TypeBoundFW` (probe proof). -/
theorem stage1TypeBoundFW6_arith (δ ν cψ s Y : ℝ) (N : ℕ) (hδ : 0 < δ) (hcψ : 1 ≤ cψ) (hs : 0 ≤ s) (hY : 0 ≤ Y)
    (hsmall : cψ ^ 16 * δ ^ (2 * ν) ≤ 1) :
    cψ ^ (16 * N) * s * (δ ^ (8 * ν * N) * Y) ≤ s * δ ^ (6 * ν * N) * Y := by
  have e1 : δ ^ (8 * ν * (N : ℝ)) = (δ ^ (2 * ν)) ^ N * δ ^ (6 * ν * (N : ℝ)) := by
    rw [← Real.rpow_natCast (δ ^ (2 * ν)) N, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    congr 1; ring
  have e2 : cψ ^ (16 * N) * (δ ^ (2 * ν)) ^ N = (cψ ^ 16 * δ ^ (2 * ν)) ^ N := by
    rw [mul_pow, pow_mul]
  have h0 : 0 ≤ cψ ^ 16 * δ ^ (2 * ν) := by positivity
  have hle : (cψ ^ 16 * δ ^ (2 * ν)) ^ N ≤ 1 := pow_le_one₀ h0 hsmall
  have h6 : 0 ≤ δ ^ (6 * ν * (N : ℝ)) := by positivity
  calc cψ ^ (16 * N) * s * (δ ^ (8 * ν * N) * Y)
      = (cψ ^ (16 * N) * (δ ^ (2 * ν)) ^ N) * (s * δ ^ (6 * ν * (N : ℝ)) * Y) := by rw [e1]; ring
    _ = (cψ ^ 16 * δ ^ (2 * ν)) ^ N * (s * δ ^ (6 * ν * (N : ℝ)) * Y) := by rw [e2]
    _ ≤ 1 * (s * δ ^ (6 * ν * (N : ℝ)) * Y) := by gcongr
    _ = s * δ ^ (6 * ν * N) * Y := one_mul _


end WaveTurbulence.Flower.Stage1W
