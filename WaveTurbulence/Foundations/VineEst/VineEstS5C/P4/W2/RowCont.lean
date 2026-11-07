/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ClockCont
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.LeafPar
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.OfModes

/-! # P4-W2 (session 11, R100 F5): the clocked expression of a row family with Fourier-sum weights is continuous on the cube

`expr_continuousOn_cube`: for a family of `RowData` whose weights are the Fourier sums of their modes (as `RowData.ofModes`), the
multiplied clocked expression is continuous in the output times on the closed cube `cubeSet D.qOut`, for every `E`.  The majorant is the
product of the mode sizes and the decay weights; the phase bound `hCph` is only needed on the box, since a nonempty time domain forces
`max (tt 1) (tt 2) < tt 0`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- A nonempty time domain over a point of the cube forces the point into the box. -/
theorem mem_outBox_of_timeDom {D : SumintPar.SumintDatum d} (hI : 0 < D.S.I) {tt : Fin 3 → ℝ}
    (htt : tt ∈ WaveTurbulence.VineEstS3.cubeSet D.qOut) {τ : D.S.TVar → ℝ}
    (hτ : τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2)) : tt ∈ outBox D := by
  refine ⟨fun c => htt c, ?_⟩
  obtain ⟨h1, h2, -⟩ := hτ
  have h3 := (h1 (.inl ⟨⟨0, hI⟩, 0⟩)).2.2
  exact lt_trans h2 h3

theorem expr_continuousOn_cube {P : WTParams} (hL : 0 < P.L) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I)
    (Mx : CharMix D.S P.d) (hη3 : 3 * P.η ≤ 1) (hη0 : 0 < P.η) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec) (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ)
    (hWsum : ∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * fsPhase m cl) (E : Fin 4 → Mom P.d) :
    ContinuousOn (fun tt => clockedExprMul3 Mx (allCR Rw) hI P.L P.γ (2 * P.δ) P.η tt E)
      (WaveTurbulence.VineEstS3.cubeSet D.qOut) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  set M := allCM Rw with hM
  have hsn : ∀ ρ r k, Summable fun m => ‖(Rw ρ).c m r k‖ := fun ρ r k =>
    summable_norm_modes hθfs (Rw ρ).c (Rw ρ).b_ne_top (Rw ρ).fs r k
  have hcont : ∀ ρ r k, Continuous fun cl => (allCR Rw).W ρ cl r k := by
    intro ρ r k
    have : (fun cl => (allCR Rw).W ρ cl r k) = fun cl => ∑' m, (Rw ρ).c m r k * fsPhase m cl :=
      funext fun cl => hWsum ρ cl r k
    rw [this]
    refine continuous_tsum (u := fun m => ‖(Rw ρ).c m r k‖) (fun m => continuous_const.mul (continuous_fsPhase_t m))
      (hsn ρ r k) (fun m cl => ?_)
    rw [norm_mul, norm_fsPhase3, mul_one]
  set St : Row D → ℝ := fun ρ => ∑' m, M.S ρ m with hSt
  have hSt0 : ∀ ρ, 0 ≤ St ρ := fun ρ => tsum_nonneg fun m => M.S_nonneg ρ m
  have hWb : ∀ ρ cl r k, ‖(Rw ρ).W cl r k‖ ≤ St ρ * decayWt D D.wDec ρ k := by
    intro ρ cl r k
    rw [hWsum]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · refine (hsn ρ r k).congr fun m => ?_
      rw [norm_mul, norm_fsPhase3, mul_one]
    · calc ∑' m, ‖(Rw ρ).c m r k * fsPhase m cl‖ ≤ ∑' m, M.S ρ m * decayWt D D.wDec ρ k := by
            refine Summable.tsum_le_tsum (fun m => ?_) ?_ ((M.summable_S hθfs ρ).mul_right _)
            · rw [norm_mul, norm_fsPhase3, mul_one]
              exact M.norm_le hθfs ρ m r k
            · refine (hsn ρ r k).congr fun m => ?_
              rw [norm_mul, norm_fsPhase3, mul_one]
        _ = St ρ * decayWt D D.wDec ρ k := by rw [tsum_mul_right]
  set Bx : (D.S.VIdx → (Fin P.d → ℤ)) → ℝ := fun x => (∏ ρ, St ρ) * ∏ ρ, decayWt D D.wDec ρ (rowMom D P.L x E ρ) with hBx
  have hBxs : Summable Bx := (summable_decayWt D hL hreg E).mul_left _
  have hBx0 : ∀ x, 0 ≤ Bx x := fun x =>
    mul_nonneg (Finset.prod_nonneg fun ρ _ => hSt0 ρ) (Finset.prod_nonneg fun ρ _ => decayWt_nonneg D _ ρ _)
  refine continuousOn_clockedExprMul3 Mx (allCR Rw) hI P.L P.γ (2 * P.δ) P.η hη3 E hcont _ Cph hCph0
    (fun tt htt τ hτ => hCph tt (mem_outBox_of_timeDom hI htt hτ) τ hτ) Bx hBxs hBx0 (fun x tt htt τ hτ => ?_)
  calc ∏ ρ, ‖(allCR Rw).W ρ ((allCR Rw).clock τ tt ρ) (E 0 - E 1) (rowMom D P.L x E ρ)‖
      ≤ ∏ ρ, (St ρ * decayWt D D.wDec ρ (rowMom D P.L x E ρ)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ρ _ => hWb ρ _ _ _)
    _ = Bx x := Finset.prod_mul_distrib

end WaveTurbulence.VineEstS5C.P4.W2
