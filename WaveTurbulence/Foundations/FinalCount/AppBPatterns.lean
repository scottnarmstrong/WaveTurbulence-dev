/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # DH23 Appendix B figure transcription

The seven figures are transcribed in TRANSCRIPTIONS.md. Here an edge list
records distinct bonds, including parallel entries; it does not constrain
the orientation of bonds without arrows. These are local incidence lists,
not induced subgraphs on surviving boundary vertices.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- Local bonds incident to the deleted atoms. Vertex labels are one-based
as in the paper. Distinct natural labels stand for distinct actual atoms. -/
structure AppbPattern where
  edges : List (ℕ × ℕ)
  removed : Finset ℕ
  deriving DecidableEq

def AppbPattern.localDegree (P : AppbPattern) (v : ℕ) : ℕ :=
  ∑ i : Fin P.edges.length, ((if P.edges[i].1 = v then 1 else 0) +
    (if P.edges[i].2 = v then 1 else 0))

def AppbPattern.boundaryCount (P : AppbPattern) : ℕ :=
  ∑ i : Fin P.edges.length, if
    (P.edges[i].1 ∈ P.removed ∧ P.edges[i].2 ∉ P.removed) ∨
    (P.edges[i].1 ∉ P.removed ∧ P.edges[i].2 ∈ P.removed) then 1 else 0

/-- All patterns in 3S3New, 3D4, and 3S2, plus the text-defined groups.
Their endpoint orientation is supplied by the actual realization. -/
inductive AppbPatternKind
  | tb1 | tb2 | s33 | s33new1 | s33new2 | s33new3 | s33new4 | s33new5 | s33new6
  | d33 | d33same | d33new | d34one | d34two | d34three | d34four
  | s32one | s32two | s32three | s32four | r3 | r21 | r22 | r23 | r23triangle | r24
  deriving DecidableEq

open AppbPatternKind in
def AppbPatternKind.pattern : AppbPatternKind → AppbPattern
  | tb1 => ⟨[(1,2),(1,2),(1,2)], {1,2}⟩
  | tb2 => ⟨[(1,2),(1,2),(1,2),(2,3)], {1,2}⟩
  | s33 => ⟨[(1,2),(1,3),(1,4),(2,5),(2,6)], {1,2}⟩
  | s33new1 => ⟨[(1,2),(1,3),(1,4),(2,3),(2,5)], {1,2}⟩
  | s33new2 => ⟨[(1,2),(1,3),(1,4),(2,3),(2,4)], {1,2}⟩
  | s33new3 => ⟨[(1,2),(1,3),(1,3),(2,4),(2,4)], {1,2}⟩
  | s33new4 => ⟨[(1,2),(1,3),(1,3),(2,3),(2,3)], {1,2}⟩
  | s33new5 => ⟨[(1,2),(1,3),(1,3),(2,4),(2,5)], {1,2}⟩
  | s33new6 => ⟨[(1,2),(1,3),(1,3),(2,3),(2,4)], {1,2}⟩
  | d33 => ⟨[(1,2),(1,2),(1,3),(2,4)], {1,2}⟩
  | d33same => ⟨[(1,2),(1,2),(1,3),(2,3)], {1,2}⟩
  | d33new => ⟨[(1,2),(1,2),(1,3),(2,4),(3,4),(3,5),(3,5),(4,6),(4,6)], {1,2,3,4}⟩
  | d34one => ⟨[(1,2),(1,2),(1,3),(2,4),(2,5)], {1,2}⟩
  | d34two => ⟨[(1,2),(1,2),(1,3),(2,3),(2,4)], {1,2}⟩
  | d34three => ⟨[(1,2),(1,2),(1,3),(2,4),(2,4)], {1,2}⟩
  | d34four => ⟨[(1,2),(1,2),(1,3),(2,3),(2,3)], {1,2}⟩
  | s32one => ⟨[(1,2),(2,4),(1,3),(1,3)], {1,2}⟩
  | s32two => ⟨[(1,2),(2,3),(1,3),(1,3)], {1,2}⟩
  | s32three => ⟨[(1,2),(2,5),(1,3),(1,4)], {1,2}⟩
  | s32four => ⟨[(1,2),(2,4),(1,3),(1,4)], {1,2}⟩
  | r3 => ⟨[(1,2),(1,3),(1,4)], {1}⟩
  | r21 => ⟨[(1,2),(1,2)], {1}⟩
  | r22 => ⟨[(1,2),(1,3)], {1}⟩
  | r23 => ⟨[(1,2),(1,3),(2,4),(3,5)], {1,2,3}⟩
  | r23triangle => ⟨[(1,2),(1,3),(2,3)], {1,2,3}⟩
  | r24 => ⟨[(1,2),(1,2)], {1,2}⟩

/-- The distinct-label version of 2R-3F may have a common outer neighbour;
this is a separate realization pattern, not a forced injective embedding
of the two outer labels. -/
def appbR23Common : AppbPattern :=
  ⟨[(1,2),(1,3),(2,4),(3,4)], {1,2,3}⟩

end WaveTurbulence.Mole
