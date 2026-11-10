/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3InvDel
/-! **FINALCOUNT-G3: erasing an atom** (TARGET Remark `remtame` case (ii), L2152: "we then remove `v` without
assigning any new `α`- or `β`-atoms").  `eraseAt M v` is the molecule on the atoms other than `v`, with the darts of
the bonds not touching `v`.  Degree formula, dart count, and the comparison of the connected components of `M` and of
`M - v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V)

section counts
variable {M v}

end counts

section comps
variable {M v}

theorem adj_symm_er {a b : V} (h : M.Adj a b) : M.Adj b a := by
  obtain ⟨z, h1, h2⟩ := h
  exact ⟨M.mate z, h2, by rw [M.mate_mate]; exact h1⟩

end comps

end WaveTurbulence.FinalCountG3
