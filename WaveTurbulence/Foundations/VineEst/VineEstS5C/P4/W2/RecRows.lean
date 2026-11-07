/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRep

/-! # P4-W2 (session 13, step 2a): Fourier-sum normal form of a `PieceRep`

`PieceRep.sum`: the two rows of a `PieceRep` can be replaced by `RowData.ofModes` rows with the same modes, slots and sizes; their weights are the
Fourier SUMS of the modes (`hWsum` of `TermCertW`, valid at every clock), and the representation identity still holds a.e. on the engine time
domain for `tt ∈ Bx ⊆ outBox` (the original weights are the sums of their modes a.e. there, `RowData.Ae`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {A : ℝ} {P : WTParams}

/-- The a.e. identification of a row with the sum of its modes on the time domain. -/
theorem rowData_ae_W_eq_tsum {D : SumintPar.SumintDatum P.d} {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (hI : 0 < D.S.I) (hR : R.Ae hI)
    {tt : Fin 3 → ℝ} (htt : tt ∈ outBox D) :
    ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k,
      R.W (R.clk τ tt) r k = ∑' m, R.c m r k * fsPhase m (R.clk τ tt) := by
  have h := hR tt htt
  rw [ae_restrict_iff' (SumintPar.measurableSet_timeDom D hI _ _ _)] at h
  filter_upwards [h] with τ hτ hd r k
  exact (hτ hd r k).tsum_eq.symm

theorem PieceRep.sum {D : SumintPar.SumintDatum P.d} {hI : 0 < D.S.I} {vp vb : D.S.VIdx} {ε : ℝ} {fac : (D.S.TVar → ℝ) → Mom P.d → ℂ}
    {X : (D.S.TVar → ℝ) → (Fin 3 → ℝ) → Mom P.d → Mom P.d → ℂ} {bK bL : ℝ≥0∞} {Bx : Set (Fin 3 → ℝ)}
    (h : PieceRep (P := P) hI vp vb ε fac X bK bL Bx) (hBx : Bx ⊆ outBox D) :
    ∃ (RK : RowData D (6 * P.η ^ 6) (Sum.inl vp)) (RL : RowData D (6 * P.η ^ 6) (Sum.inr vb)),
      RK.Ae hI ∧ RL.Ae hI ∧
      (∀ cl r k, RK.W cl r k = ∑' m, RK.c m r k * fsPhase m cl) ∧
      (∀ cl r k, RL.W cl r k = ∑' m, RL.c m r k * fsPhase m cl) ∧ RK.b ≤ bK ∧ RL.b ≤ bL ∧
      ∀ tt ∈ Bx, ∀ᵐ τ : D.S.TVar → ℝ, τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) → ∀ r k : Mom P.d, ‖r‖ ≤ 1 →
        X τ tt r k = fac τ r * (RK.W (RK.clk τ tt) r k * RL.W (RL.clk τ tt) r (k + ε • r)) := by
  obtain ⟨RK, RL, hK, hL, hbK, hbL, hX⟩ := h
  let RK' : RowData D (6 * P.η ^ 6) (Sum.inl vp) := RowData.ofModes (Sum.inl vp) RK.slot RK.c RK.b RK.b_ne_top RK.fs
    (fun v hv => by exact absurd hv (by simp))
  let RL' : RowData D (6 * P.η ^ 6) (Sum.inr vb) := RowData.ofModes (Sum.inr vb) RL.slot RL.c RL.b RL.b_ne_top RL.fs RL.indepC
  have hθ : (0 : ℝ) ≤ 6 * P.η ^ 6 := by
    positivity
  refine ⟨RK', RL', RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, RowData.ofModes_ae hθ hI _ _ _ _ _ _ _, fun _ _ _ => rfl, fun _ _ _ => rfl,
    hbK, hbL, fun tt htt => ?_⟩
  filter_upwards [hX tt htt, rowData_ae_W_eq_tsum RK hI hK (hBx htt), rowData_ae_W_eq_tsum RL hI hL (hBx htt)] with τ h1 h2 h3 hd r k hr
  rw [h1 hd r k hr, h2 hd r k, h3 hd r (k + ε • r)]
  rfl

end WaveTurbulence.VineEstS5C.P4.W2
