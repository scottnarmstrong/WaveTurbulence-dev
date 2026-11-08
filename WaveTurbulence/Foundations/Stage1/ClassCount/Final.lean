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

/-- B2d: a class count valid for every marked set gives it for every admissibility predicate. -/
theorem classCountStmtMk_of_true {Adm : MarkAdm} (h : ClassCountStmtMk fun _ _ _ => True) :
    ClassCountStmtMk Adm := by
  obtain ⟨C₀, K, hC₀, hm⟩ := h
  refine ⟨C₀, K, hC₀, fun P hK p hp R hR N hN g r A hA => hm P hK p hp R hR N hN g r A fun LG hLG => ?_⟩
  obtain ⟨hc, S, D, hS, hd, σ, Mk, -, hg, hr⟩ := hA LG hLG
  exact ⟨hc, S, D, hS, hd, σ, Mk, trivial, hg, hr⟩

/-- B2d: **the Stage 1′ class count at any marking** (TARGET L2241-L2252 for the pieces `stage1PieceOf … σ Mk`, runs
of the marked groups spliced), unconditional. -/
theorem classCountMk : ClassCountStmtMk fun _ _ _ => True :=
  classCount_of_legsMk decodeSizeLeg (skeletonLegMk_of_codeLegMk skeletonCodeLegMk) layeringLegMk

/-- B2d: the Stage 1′ class count for every admissibility predicate (in particular the world's). -/
theorem classCountMk_adm (Adm : MarkAdm) : ClassCountStmtMk Adm := classCountStmtMk_of_true classCountMk

end WaveTurbulence.ClassCount
