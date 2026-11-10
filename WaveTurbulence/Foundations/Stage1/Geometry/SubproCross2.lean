/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSubst
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproBlockGeo
public import WaveTurbulence.Foundations.FinalCount.SubproItems2
import Mathlib.Tactic

/-!
# SUBPRO (S4): `crossing`, the far darts of a hinge (R28 session 2)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1 WaveTurbulence.Mole

variable {R : ℕ} {G : Garden (2 * R)}

theorem Object.upper_ne_lower' {w : ℕ} {G' : Garden w} (P : Object G'.molecule) : P.upper ≠ P.lower := by
  obtain ⟨A, a, b, sh⟩ := P
  cases sh with
  | vc h => exact h.1.2.2.2.1
  | hyper R => exact R.adjoint.1.2.2.2.1

end WaveTurbulence.Subpro
