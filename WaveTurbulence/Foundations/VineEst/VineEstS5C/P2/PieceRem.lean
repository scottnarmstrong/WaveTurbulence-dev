/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceSS
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.KCont
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.DefectRows

/-! # P2: piece bounds with a remainder row (the types of `remA`, `remB`)

`RemT`: a gate remainder (a kernel `f` which agrees a.e. in time on the box with a time-continuous `f'`, with finite `XNormRestr` bound).  `piece_SR`
(separated 𝒦, remainder ℒ), `piece_RS` (remainder 𝒦, separated ℒ), `piece_RR` (both remainders). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal ComplexConjugate

/-- A remainder kernel on the time box `B`: a.e. equal to a time-continuous `f'`, with `‖f‖_{𝔛^{6η^6, 30d, Λ₂}(B)} < CR`. -/
structure RemT (P : WTParams) (Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CR : ℝ) where
  f : (Fin 2 → ℝ) → Mom P.d → ℂ
  f' : (Fin 2 → ℝ) → Mom P.d → ℂ
  hcell : B ⊆ cell q
  hint : B ⊆ closure (interior B)
  hcont : ∀ k, Continuous fun t => f' t k
  hae : ∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k
  hCR : 0 ≤ CR
  hX : XNormRestr (6 * P.η ^ 6) (30 * P.d) Λ₂ B Set.univ f < ENNReal.ofReal CR

variable {A : ℝ} {P : WTParams}

end WaveTurbulence.VineEstS5C.P2
