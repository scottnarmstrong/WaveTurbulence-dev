/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3TripleGe4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3TripleGe4`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the `≥ 4` case of `TripleDesig` (R37).**  A bond multiplicity `≥ 4` between two distinct atoms of `M_sub`
would make `{a, b}` a closed atom set (all `≤ 8` darts of `a` and `b` lie on those bonds), hence, by connectedness, all of
`M_sub`; the count `bonds + R = 2·atoms` with `R ≥ 1` then fails.  So S4's `= 3` form (`Subpro.triple_in_designated`) suffices:
`TripleDesig3 C → TripleDesig C`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- S4's form of `triple_in_designated` (`bondsBetween = 3`). -/
def TripleDesig3 {M₀ : Molecule V D₀} (C : CollData M₀) : Prop :=
  ∀ a b : V, a ∈ M₀.atoms → b ∈ M₀.atoms → a ≠ b → M₀.bondsBetween a b = 3 →
    ∃ v c x y, ((v = a ∧ c = b) ∨ (v = b ∧ c = a)) ∧ v ∈ C.hinges ∧ C.first v = some x ∧ C.second v = some y ∧
      TripleAtM M₀ v x y ∧ M₀.atom (M₀.mate x) = c ∧ M₀.atom (M₀.mate y) = c

/-- **`TripleDesig` from S4's `= 3` form**: the `≥ 4` case does not occur (`bondsBetween_lt_four`). -/
theorem tripleDesig_of_eq3 {R : ℕ} {M₀ : Molecule V D₀} (hS : SubHyp R M₀) {C : CollData M₀} (h3 : TripleDesig3 C) :
    TripleDesig C := by
  intro a b ha hb hab h
  exact h3 a b ha hb hab (le_antisymm (by have := bondsBetween_lt_four (b := b) hS ha; omega) h)

end WaveTurbulence.GammaLow.FinalCount.H
