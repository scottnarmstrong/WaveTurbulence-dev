/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.Layout` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.Layout


/-!
# CLASSCOUNT: the global layout of an atom set with units

Let `V` be a finite type, `F ⊆ V` the *fixed* atoms (unclassed atoms and unit representatives), labelled injectively by
`e : V → ℕ` with image `range n'`, and let `U 0, …, U (q-1)` be disjoint atom sets (the units) whose representatives
`rep i ∈ U i` are in `F`, with unit labellings `lab i` (injective on `U i` with image `range (W i + 1)`).  The *layout*
`pos` agrees with `e` on `F`, and sends `v ∈ U i` to `glob (lab i (rep i)) (e (rep i)) (n' + Σ_{j<i} W j) (lab i v)`.
`layout_inj`: `pos` is injective on `V` with image `range (n' + Σ W)`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.GammaLow.FinalCount
