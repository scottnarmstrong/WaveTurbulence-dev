/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedPhysicalChart
public import WaveTurbulenceVineParam.VineParamRepresentativeCapSupport
import Mathlib.Tactic

/-! # The strengthened physical chart retains support at the selected cap -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

omit [Fintype V] in
/-- Both actual local origins of each new difference touch the outside
of the original cap. Fresh atoms are outside, including a single II rung. -/
theorem insertedOrigins_touches_outside (j : Fin 2) :
    touchesSide G.newEnds (liftedCap G.cap) (.inr (insertedDifferenceOrigins G.pattern j).1) false ∧
      touchesSide G.newEnds (liftedCap G.cap) (.inr (insertedDifferenceOrigins G.pattern j).2) false := by
  cases hp : G.pattern <;> fin_cases j
  all_goals simp [touchesSide,liftedCap,insertedDifferenceOrigins,newEnds,rungSpliceEnds,hp,
    RungPattern.signs,orientPair,G.outer_q]

/-- The physical pair construction preserves common-side support at the
same cap, so further rungs can be inserted there. -/
theorem insertedPhysicalChart_selected_support {X : VineType} {a b : V}
    (P : PhysicalGraphChart G.ends X a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (hcap : P.CapSupported G.cap)
    (hpairs : ∀ j : Fin P.full.indexing.shape.m,
      (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ G.cap ↔
        (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ G.cap)
    (hbad : X.IsBad=true → G.gapSign a b ≠ 0) :
    (G.insertedPhysicalChart P hX ha hb hcap hpairs hbad).CapSupported (liftedCap G.cap) := by
  apply (physicalCapSupported_iff _ _).mpr
  intro i
  change ∃ side : Bool,
    touchesSide G.newEnds (liftedCap G.cap) (G.insertedPhysicalPair P hcap hX i).1 side ∧
      touchesSide G.newEnds (liftedCap G.cap) (G.insertedPhysicalPair P hcap hX i).2 side
  cases hi : nonreferenceInsertionEquiv P.full.indexing.shape hX i with
  | inl j =>
    simp only [insertedPhysicalPair,hi,Sum.elim_inl]
    have hs := G.retainedDifferenceSide_admissible P hcap j
    exact ⟨G.retainedDifferenceSide P hcap j,
      G.representative_touches_selected _ _ hs.1,G.representative_touches_selected _ _ hs.2⟩
  | inr j =>
    simp only [insertedPhysicalPair,hi,Sum.elim_inr]
    exact ⟨false,G.insertedOrigins_touches_outside j⟩

end WaveTurbulence.Vine.Param.RungSpliceGeometry
