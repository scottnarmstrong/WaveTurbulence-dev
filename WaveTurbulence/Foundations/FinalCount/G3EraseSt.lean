/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Erase
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.FinalCount.G3Flat
/-! **FINALCOUNT-G3: the erase-atom step** `Step5` (TARGET Remark `remtame` case (ii), L2152; remtame2 L2218).

A degree-`4` `ε`-atom `v` is *erasable* (case (ii)) if every component of `M - v` contains at least two atoms adjacent
to `v` (i.e. "no component contains exactly one atom adjacent to `v`").  Erasing removes `v` and its four bonds and
assigns no new `α`- or `β`-atoms; the neighbours of `v` lose darts and become imperfect (`contrib` increases by the
number of removed bonds).  The invariant `Good` is preserved with `R` replaced by `R + 2`
(`4V - 2E - 2(V_α + V_β)` increases by `4`, TARGET `finalmol` L2187 is false once erasures occur: E9). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

section inv
variable {s : St.{u} V D₀} {R : ℕ} {v : V}

theorem base_nonneg (c : Cls) : 0 ≤ c.base := by cases c <;> simp [Cls.base]

end inv
end WaveTurbulence.FinalCountG3
