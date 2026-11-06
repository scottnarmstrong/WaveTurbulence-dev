/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceRepresentatives
import Mathlib.Tactic

/-! # Endpoint cap support supplies the actual-label representative choices -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- A bond touching a cap side admits a representative on that side. This
includes either of the marked crossing occurrences, without exceptions. -/
theorem admissibleSide_of_endpoint (e : β) (side : Bool)
    (h : if side then (G.ends e).1 ∈ G.cap ∨ (G.ends e).2 ∈ G.cap
      else (G.ends e).1 ∉ G.cap ∨ (G.ends e).2 ∉ G.cap) : G.AdmissibleSide e side := by
  intro hi hj
  have hc := G.uncut e hi hj
  cases side
  · have hn : (G.ends e).1 ∉ G.cap := by
      rcases h with h | h
      · exact h
      · exact fun ht => h (hc.mp ht)
    simp [inside,hn]
  · have ht : (G.ends e).1 ∈ G.cap := by
      rcases h with h | h
      · exact h
      · exact hc.mpr h
    simp [inside,ht]

/-- The finite base chart's common-side support gives common admissible
physical representatives after insertion. -/
theorem exists_common_admissible (e f : β)
    (h : (((G.ends e).1 ∈ G.cap ∨ (G.ends e).2 ∈ G.cap) ∧
        ((G.ends f).1 ∈ G.cap ∨ (G.ends f).2 ∈ G.cap)) ∨
      (((G.ends e).1 ∉ G.cap ∨ (G.ends e).2 ∉ G.cap) ∧
        ((G.ends f).1 ∉ G.cap ∨ (G.ends f).2 ∉ G.cap))) :
    ∃ side : Bool,G.AdmissibleSide e side ∧ G.AdmissibleSide f side := by
  rcases h with h | h
  · exact ⟨true,G.admissibleSide_of_endpoint e true h.1,G.admissibleSide_of_endpoint f true h.2⟩
  · exact ⟨false,G.admissibleSide_of_endpoint e false h.1,G.admissibleSide_of_endpoint f false h.2⟩

end WaveTurbulence.Vine.Param.RungSpliceGeometry
