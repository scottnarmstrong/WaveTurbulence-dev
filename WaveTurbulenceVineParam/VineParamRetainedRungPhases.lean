/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedOldPhases
import Mathlib.Tactic

/-! # Every retained rung keeps its exact contract phase -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Every retained s phase remains the required negative bilinear form. -/
theorem retained_s_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d)
    (j : Fin F.indexing.shape.m) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).ySlot j.castSucc)=
        -2*inner ℝ (x ((insertedShape F.indexing.shape hX).xSlot j.castSucc))
          (x ((insertedShape F.indexing.shape hX).ySlot j.castSucc)) := by
  rw [G.insertedContractChart_old_node F hab hX ha hb anchor d g r x _ _
    (slotInsertionEquiv_old_y F.indexing.shape hX j) (ySlot_ne_reference F.indexing.shape j)]
  rw [F.rung_s_phase]
  rw [G.reindexedOldCoordinate_eq F.indexing.shape hX a b r anchor x _ _
    (slotInsertionEquiv_old_x F.indexing.shape hX j) (xSlot_ne_reference F.indexing.shape j)]
  rw [G.reindexedOldCoordinate_eq F.indexing.shape hX a b r anchor x _ _
    (slotInsertionEquiv_old_y F.indexing.shape hX j) (ySlot_ne_reference F.indexing.shape j)]

/-- Every retained t phase keeps its original ternary gap coefficients. -/
theorem retained_t_phase {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d)
    (j : Fin F.indexing.shape.m) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r
      ((insertedShape F.indexing.shape hX).xSlot j.castSucc)=
        2*inner ℝ (x ((insertedShape F.indexing.shape hX).xSlot j.castSucc))
          (x ((insertedShape F.indexing.shape hX).ySlot j.castSucc))+
        2*inner ℝ r ((F.ζc j 0 : ℝ) • x ((insertedShape F.indexing.shape hX).xSlot j.castSucc)+
          (F.ζc j 1 : ℝ) • x ((insertedShape F.indexing.shape hX).ySlot j.castSucc)+
          (F.ζc j 2 : ℝ) • r) := by
  rw [G.insertedContractChart_old_node F hab hX ha hb anchor d g r x _ _
    (slotInsertionEquiv_old_x F.indexing.shape hX j) (xSlot_ne_reference F.indexing.shape j)]
  rw [F.rung_t_phase]
  rw [G.reindexedOldCoordinate_eq F.indexing.shape hX a b r anchor x _ _
    (slotInsertionEquiv_old_x F.indexing.shape hX j) (xSlot_ne_reference F.indexing.shape j)]
  rw [G.reindexedOldCoordinate_eq F.indexing.shape hX a b r anchor x _ _
    (slotInsertionEquiv_old_y F.indexing.shape hX j) (ySlot_ne_reference F.indexing.shape j)]

end WaveTurbulence.Vine.Param.RungSpliceGeometry
