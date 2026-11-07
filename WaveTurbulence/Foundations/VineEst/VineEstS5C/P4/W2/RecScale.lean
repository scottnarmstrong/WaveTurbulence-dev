/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux

/-! # P4-W2 (session 14, step 2): scaling the rows of a `PieceRep` by a unit factor

`coefBound_unit_mul_le`: multiplying every mode coefficient by a unit complex number does not increase `coefBound`.
`PieceRep.sum_unit`: `PieceRep.sum` for the representation of `ν · X`, `‖ν‖ = 1` (the unit `ν = nuOf ..` of a record is absorbed into the `𝒦` row; the
Fourier sums, the modes, the slots and the sizes are those of `PieceRep.sum`, with the modes of `RK` multiplied by `ν`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

theorem coefBound_unit_mul_le {d : ℕ} (θ : ℝ) (A' B' : ℕ) (ν : ℂ) (hν : ‖ν‖ = 1)
    (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) :
    coefBound θ A' B' (fun m r k => ν * c m r k) ≤ coefBound θ A' B' c := by
  unfold coefBound
  refine ENNReal.tsum_le_tsum fun m => mul_le_mul_right ?_ _
  refine iSup_le fun r => ?_
  refine (WaveTurbulence.VineEstS3.Eng.SNorm_smul_le A' B' ν (c m r)).trans ?_
  have : ‖ν‖ₑ = 1 := by rw [← ofReal_norm, hν]; simp
  rw [this, one_mul]
  exact le_iSup (fun r => SNorm A' B' (c m r)) r

theorem PieceRep.sum_unit {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ}
    {fac : (D.S.TVar → ℝ) → Mom P.d → ℂ}
    {X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bK bL : ℝ≥0∞} {Bx : Set (Fin 3 → ℝ)}
    (h : PieceRep (P := P) hI vp vb ε fac X bK bL Bx) (hBx : Bx ⊆ outBox D) (ν s : ℂ) (hν : ‖ν‖ = 1) (hs : ‖s‖ = 1)
    (f0 : (D.S.TVar → ℝ) → Mom P.d → ℂ) (hfac : ∀ τ r, fac τ r = s * f0 τ r) :
    ∃ (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)),
      RK.Ae hI ∧ RL.Ae hI ∧
      (∀ cl r k, RK.W cl r k = ∑' m, RK.c m r k * fsPhase m cl) ∧
      (∀ cl r k, RL.W cl r k = ∑' m, RL.c m r k * fsPhase m cl) ∧ RK.b ≤ bK ∧ RL.b ≤ bL ∧
      ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        ν * X τ tt r k = f0 τ r * (RK.W (RK.clk τ tt) r k * RL.W (RL.clk τ tt) r (k + ε • r)) := by
  obtain ⟨RK, RL, hK, hL, hKW, hLW, hbK, hbL, hX⟩ := h.sum hBx
  have hθ : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hνs : ‖ν * s‖ = 1 := by rw [norm_mul, hν, hs, mul_one]
  let RK' : RowData D (6 * P.η ^ 6) (Sum.inl vp) := RowData.ofModes (Sum.inl vp) RK.slot (fun m r k => (ν * s) * RK.c m r k) RK.b
    RK.b_ne_top ((coefBound_unit_mul_le _ _ _ (ν * s) hνs RK.c).trans RK.fs) (fun v hv => by exact absurd hv (by simp))
  refine ⟨RK', RL, RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, hL, fun _ _ _ => rfl, hLW, hbK, hbL, fun tt htt => ?_⟩
  filter_upwards [hX tt htt] with τ h1 hd r k hr
  have hW : RK'.W (RK'.clk τ tt) r k = (ν * s) * RK.W (RK.clk τ tt) r k := by
    show ∑' m, (ν * s) * RK.c m r k * fsPhase m (RK'.clk τ tt) = _
    rw [hKW, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [mul_assoc]; rfl
  rw [hW, h1 hd r k hr, hfac]
  ring

end WaveTurbulence.VineEstS5C.P4.W2
