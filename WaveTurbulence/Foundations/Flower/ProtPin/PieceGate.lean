/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.None
public import WaveTurbulence.Foundations.Flower.ProtPin.Restr

/-! # D3 PROT-PIN: the gates on the pieces of a cut, one output at a time

A regular paired tree (a cut piece: prefix or interior) in layers `≤ p` with lone leaf in layer `p`, and a regular
couple in layers `≤ p`, are bounded at every output `k'` in the scalar restricted norm `rn θ`, on `timeBoxGt p p`
resp. `timeBox p p`, by FILT-GATE (incoherent) or the flat coherent gate `CohFlatAt` (coherent pieces are flat in
layer `p`, the hypothesis `hflat`, supplied by `CutFlat.lean` from the canonical ambient); couples with the output
weight `⟨k'⟩^{30d}`. The loss is `L^{c'}`, `c' = 0` at `θ = η` and `c' = 4d` at `θ = 1/4`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- The per-piece loss exponent of the gates. -/
def PieceLoss (P : WTParams) (θ c' : ℝ) : Prop := (θ = P.η ∧ c' = 0) ∨ (θ = 1 / 4 ∧ c' = 4 * P.d)

theorem PieceLoss.nonneg {P : WTParams} {θ c' : ℝ} (h : PieceLoss P θ c') : 0 ≤ c' := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> subst h <;> positivity

theorem PieceLoss.theta {P : WTParams} {θ c' : ℝ} (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 4) (h : PieceLoss P θ c') :
    0 ≤ θ ∧ θ ≤ 1 / 4 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h
  · exact ⟨hη0, hη⟩
  · norm_num

end WaveTurbulence.Flower.ProtPin
