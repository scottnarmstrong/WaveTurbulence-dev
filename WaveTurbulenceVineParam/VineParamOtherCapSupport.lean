/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedSelectedSupport
import Mathlib.Tactic

/-! # Support at a different cap survives the selected insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Outside ports make both representatives of a selected crossing bond
external to every other cap. Uncut bonds preserve their literal side. -/
theorem representative_touches_other (C : Finset V)
    (hp : G.p ∉ C) (hq : G.q ∉ C) (hc : G.c ∉ C) (hd : G.d ∉ C)
    (hσ : ∀ v,G.σ v ∈ C ↔ v ∈ C) (e : β) (chosen side : Bool)
    (hs : touchesSide G.ends C e side) :
    touchesSide G.newEnds (liftedCap C) (G.representative e chosen) side := by
  by_cases hi : e=G.i
  · subst e
    rw [G.representative_first]
    cases side <;> cases chosen <;> cases hP : G.pattern
    all_goals simp_all [touchesSide,liftedCap,G.first,newEnds,rungSpliceEnds,
      RungPattern.signs,RungPattern.reversesPorts,orientPair]
  · by_cases hj : e=G.j
    · subst e
      rw [G.representative_second]
      cases side <;> cases chosen <;> cases hP : G.pattern
      all_goals simp_all [touchesSide,liftedCap,G.second,newEnds,rungSpliceEnds,
        RungPattern.signs,RungPattern.reversesPorts,orientPair]
    · rw [G.representative_rest e hi hj]
      simpa [touchesSide,liftedCap,newEnds,rungSpliceEnds,hσ] using hs

/-- Every inserted internal difference is supported outside any cap not
containing the outer lower rail endpoint. -/
theorem insertedOrigins_touches_other (C : Finset V) (hq : G.q ∉ C) (j : Fin 2) :
    touchesSide G.newEnds (liftedCap C) (.inr (insertedDifferenceOrigins G.pattern j).1) false ∧
      touchesSide G.newEnds (liftedCap C) (.inr (insertedDifferenceOrigins G.pattern j).2) false := by
  cases hP : G.pattern <;> fin_cases j
  all_goals simp [touchesSide,liftedCap,insertedDifferenceOrigins,newEnds,rungSpliceEnds,hP,
    RungPattern.signs,orientPair,hq]

/-- The strengthened source chart retains support simultaneously at every
other cap whose ports are outside and whose membership reflection preserves. -/
theorem insertedPhysicalChart_other_support [Fintype V] {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (hcap : P.CapSupported G.cap)
    (hpairs : ∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ G.cap ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ G.cap)
    (hbad : X.IsBad=true → G.gapSign a b ≠ 0)
    (C : Finset V) (hC : P.CapSupported C)
    (hp : G.p ∉ C) (hq : G.q ∉ C) (hc : G.c ∉ C) (hd : G.d ∉ C)
    (hσ : ∀ v,G.σ v ∈ C ↔ v ∈ C) :
    (G.insertedPhysicalChart P hX ha hb hcap hpairs hbad).CapSupported (liftedCap C) := by
  apply (physicalCapSupported_iff _ _).mpr
  intro i
  change ∃ side : Bool,
    touchesSide G.newEnds (liftedCap C) (G.insertedPhysicalPair P hcap hX i).1 side ∧
      touchesSide G.newEnds (liftedCap C) (G.insertedPhysicalPair P hcap hX i).2 side
  cases hi : nonreferenceInsertionEquiv P.full.indexing.shape hX i with
  | inl j =>
    simp only [insertedPhysicalPair,hi,Sum.elim_inl]
    obtain ⟨side,he,hf⟩ := (physicalCapSupported_iff P C).mp hC j
    exact ⟨side,G.representative_touches_other C hp hq hc hd hσ _ _ _ he,
      G.representative_touches_other C hp hq hc hd hσ _ _ _ hf⟩
  | inr j =>
    simp only [insertedPhysicalPair,hi,Sum.elim_inr]
    exact ⟨false,G.insertedOrigins_touches_other C hq j⟩

end WaveTurbulence.Vine.Param.RungSpliceGeometry
