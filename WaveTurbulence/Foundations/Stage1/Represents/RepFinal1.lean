/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal0
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the vine-free `RepresentsInt` at the `WTPrefix` level (finding F-CONST)

`NoVineRepresentsAt P`: for every vine-free piece `stage1PieceOf` at the parameter record `P`, `RepresentsInt`
holds (`represents_noVine` at the piece constant `C = P.C₁`).  `noVine_prefix`: it holds on the `WTPrefix` of the
two leafwise gates.  The piece constant is chosen AFTER the gate constant: the gates are used at `Pg` and the piece
at `{Pg with C₁ := C}` with `C ≥ CminF d η Pg.C₁`, a function of `d`, `η` and the gate constant only; the later
parameters `ν, δ, D, C₂, L` are unchanged.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set

theorem N_bumpC1 (P : WTParams) (C : ℝ) (p : ℕ) : ({P with C₁ := C} : WTParams).N p = P.N p := by
  simpa using N_largeConstants P C P.C₂ p

end WaveTurbulence.Represents
