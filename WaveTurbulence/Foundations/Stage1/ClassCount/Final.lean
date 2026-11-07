/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.SkeletonCode
public import WaveTurbulence.Foundations.Stage1.ClassCount.LayeringFinal
import Mathlib.Tactic

/-!
# CLASSCOUNT: the Stage 1 class count from the layering leg

`classCount_of_layeringLeg`: `ClassCountStmt` follows from `LayeringLeg` (TARGET L2248-L2252, the number of canonical
layered gardens over a fixed skeleton and replacement datum).  The other two legs are proved:
`decodeSizeLeg` (`G.order = S.order + D.size`) and `skeletonLeg_of_codeLeg skeletonCodeLeg` (TARGET L2241-L2247,
molecule counts: ladders, units, `propcplmol`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount

theorem classCount_of_layeringLeg (h2 : LayeringLeg) : ClassCountStmt :=
  classCount_of_legs decodeSizeLeg (skeletonLeg_of_codeLeg skeletonCodeLeg) h2

/-- **The Stage 1 class count (TARGET L2241-L2252), unconditional.** -/
theorem classCount : ClassCountStmt := classCount_of_layeringLeg layeringLeg

/-- B1b (R156): the Stage 1 class count with the truncation-free carrier `Stage1CarriesW`, unconditional. -/
theorem classCountW : ClassCountStmtW :=
  classCount_of_legsW decodeSizeLeg (skeletonLeg_of_codeLeg skeletonCodeLeg) layeringLegW

end WaveTurbulence.ClassCount
