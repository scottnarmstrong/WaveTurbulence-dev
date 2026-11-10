/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftCount
public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftCopiedLabel
public import WaveTurbulence.Foundations.FinalCount.AppBS33RightCount
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteFiberSum
import Mathlib.Tactic

/-! # Sequential left--pair--right counting for 3S3-3G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33SeparatedPostAdmissibility {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) :=
  appbSeparatedAdmissibility (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r)
    (appbS33LeftAdmissibility r Adm) (appbS33RightAdmissibility r Adm)

end WaveTurbulence.Mole
