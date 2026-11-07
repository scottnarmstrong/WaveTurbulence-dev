/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Merge
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Clock

/-! # P4-W2 (R82 step 2): rows whose weight is the Fourier SUM of their modes

`RowData.ofModes`: the row datum with mode coefficients `c`, weight `W cl r k = ∑' m, c m r k * fsPhase m cl`.  Since the modes are
absolutely summable (`summable_norm_modes`, from `coefBound ≤ b < ⊤`), `RowData.Ae` holds at EVERY clock, with no membership
hypothesis on the clocks (`ofModes_ae`); the identification of the weight with a given time factor (`ofModes_W`) is claimed only at the
clocks where the Fourier series of the time factor converges to it (the continuity set `Bc`).  This is the design of R82 (F-AUX-CONT). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem summable_norm_modes {θ : ℝ} (hθ : 0 ≤ θ) {A B : ℕ} (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (h : coefBound θ A B c ≤ b) (r k : Mom d) : Summable fun m => ‖c m r k‖ := by
  have h1 : ∀ m, ‖c m r k‖ₑ ≤ maxBracketPow θ (half m) * ⨆ r' : Mom d, SNorm A B (c m r') := by
    intro m
    refine le_trans ?_ (le_mul_of_one_le_left bot_le (one_le_maxBracketPow hθ _))
    refine le_trans ?_ (le_iSup (fun r' => SNorm A B (c m r')) r)
    refine le_trans ?_ (le_SNorm A B (c m r) k)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (WaveTurbulence.Induct.one_le_jbr k)))
  have h2 : ∑' m, ‖c m r k‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hb ((ENNReal.tsum_le_tsum h1).trans h)
  have := ENNReal.summable_toReal h2
  simpa using this

variable {D : SumintPar.SumintDatum d}

/-- The row datum with the given modes and the Fourier-sum weight. -/
noncomputable def RowData.ofModes {θ : ℝ} (ρ : Row D) (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) (b : ℝ≥0∞) (hb : b ≠ ⊤) (fs : coefBound θ D.wN (rowOrder D ρ) c ≤ b)
    (indepC : ∀ v, ρ = Sum.inr v → ∀ (m : Fin 3 → ℤ) (r r' k : Mom d), c m r k = c m r' k) : RowData D θ ρ where
  W := fun cl r k => ∑' m, c m r k * fsPhase m cl
  slot := slot
  c := c
  b := b
  b_ne_top := hb
  fs := fs
  indepW := fun v hv cl r r' k => tsum_congr fun m => by rw [indepC v hv m r r' k]
  indepC := indepC

theorem RowData.ofModes_ae {θ : ℝ} (hθ : 0 ≤ θ) (hI : 0 < D.S.I) (ρ : Row D) (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D)
    (c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ) (b : ℝ≥0∞) (hb : b ≠ ⊤) (fs : coefBound θ D.wN (rowOrder D ρ) c ≤ b)
    (indepC : ∀ v, ρ = Sum.inr v → ∀ (m : Fin 3 → ℤ) (r r' k : Mom d), c m r k = c m r' k) :
    (RowData.ofModes (θ := θ) ρ slot c b hb fs indepC).Ae hI := by
  intro tt _
  refine Filter.Eventually.of_forall fun τ r k => ?_
  refine Summable.hasSum ?_
  refine Summable.of_norm ?_
  refine (summable_norm_modes hθ c hb fs r k).congr fun m => ?_
  show ‖c m r k‖ = ‖c m r k * fsPhase m (RowData.clk (RowData.ofModes (θ := θ) ρ slot c b hb fs indepC) τ tt)‖
  rw [norm_mul, norm_fsPhase3, mul_one]

theorem RowData.ofModes_W {θ : ℝ} {ρ : Row D} {slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D}
    {c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ} {b : ℝ≥0∞} {hb : b ≠ ⊤} {fs : coefBound θ D.wN (rowOrder D ρ) c ≤ b}
    {indepC : ∀ v, ρ = Sum.inr v → ∀ (m : Fin 3 → ℤ) (r r' k : Mom d), c m r k = c m r' k}
    {cl : Fin 3 → ℝ} {r k : Mom d} {y : ℂ} (h : HasSum (fun m => c m r k * fsPhase m cl) y) :
    (RowData.ofModes (θ := θ) ρ slot c b hb fs indepC).W cl r k = y := h.tsum_eq

end WaveTurbulence.VineEstS5C.P4.W2
