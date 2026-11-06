/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedPhysicalChart
public import WaveTurbulenceVineParam.VineParamLiftedCap
import Mathlib.Tactic

/-! # Uniform cap membership of paired atoms survives insertion -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Old paired atoms are reflected together on every invariant cap;
both newly appended atoms lie outside every lifted old cap. -/
theorem insertedIndexing_pair_uniform {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (C : Finset V) (hσ : ∀ v,G.σ v ∈ C ↔ v ∈ C)
    (hI : ∀ j : Fin I.shape.m,(I.atom (I.shape.xSlot j)).1 ∈ C ↔
      (I.atom (I.shape.ySlot j)).1 ∈ C) :
    ∀ j : Fin (insertedShape I.shape hX).m,
      ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).xSlot j)).1 ∈ liftedCap C ↔
        ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).ySlot j)).1 ∈ liftedCap C := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · erw [G.insertedIndexing_new_x,G.insertedIndexing_new_y]
    simp [liftedCap]
  · erw [G.insertedIndexing_old I hX ha hb _ _ (slotInsertionEquiv_old_x I.shape hX j),
      G.insertedIndexing_old I hX ha hb _ _ (slotInsertionEquiv_old_y I.shape hX j)]
    simpa [liftedCap,hσ] using hI j

end WaveTurbulence.Vine.Param.RungSpliceGeometry
