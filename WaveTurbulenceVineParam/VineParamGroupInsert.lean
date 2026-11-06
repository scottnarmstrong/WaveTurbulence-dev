/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGroupSet
import Mathlib.Tactic

/-! # Chart groups after one rung insertion and along graph isomorphisms -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

namespace RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- The groups of the inserted chart are the old groups (atoms moved by `σ`, as in
`insertedIndexing`) plus the fresh doubled pair. -/
theorem insertedIndexing_groupSet {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a = a) (hb : G.σ b = b) (ℓ : V ⊕ Fin 2 → ℕ) :
    indexingGroupSet (G.insertedIndexing I hX ha hb) ℓ =
      insert ({ℓ (.inr 0), ℓ (.inr 1)} : Finset ℕ)
        (shapeGroupSet I.shape (fun i => ℓ (.inl (G.σ (I.atom i).1)))) := by
  classical
  have hx : ∀ j : Fin I.shape.m,
      ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).xSlot j.castSucc)).1 =
        ℓ (.inl (G.σ (I.atom (I.shape.xSlot j)).1)) := fun j => by
    rw [G.insertedIndexing_old I hX ha hb _ _ (slotInsertionEquiv_old_x I.shape hX j)]
  have hy : ∀ j : Fin I.shape.m,
      ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).ySlot j.castSucc)).1 =
        ℓ (.inl (G.σ (I.atom (I.shape.ySlot j)).1)) := fun j => by
    rw [G.insertedIndexing_old I hX ha hb _ _ (slotInsertionEquiv_old_y I.shape hX j)]
  have hu : ∀ (hn : X.IsBad = false) (c : Fin 3),
      ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn c)).1 =
        ℓ (.inl (G.σ (I.atom (I.shape.uSlot hn c)).1)) := fun hn c => by
    rw [G.insertedIndexing_old I hX ha hb _ _ (slotInsertionEquiv_core I.shape hX hn c)]
  have hnx : ℓ ((G.insertedIndexing I hX ha hb).atom
      ((insertedShape I.shape hX).xSlot (Fin.last I.shape.m))).1 = ℓ (.inr 0) := by
    rw [G.insertedIndexing_new_x]
  have hny : ℓ ((G.insertedIndexing I hX ha hb).atom
      ((insertedShape I.shape hX).ySlot (Fin.last I.shape.m))).1 = ℓ (.inr 1) := by
    rw [G.insertedIndexing_new_y]
  unfold indexingGroupSet shapeGroupSet
  change (univ.image fun j : Fin (I.shape.m + 1) =>
      ({ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).xSlot j)).1,
        ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).ySlot j)).1} :
        Finset ℕ)) ∪
      (if hn : X.IsBad = false then
        {({ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 0)).1,
           ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 1)).1,
           ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 2)).1} :
           Finset ℕ)} else (∅ : Finset (Finset ℕ))) = _
  have hcore : (if hn : X.IsBad = false then
        {({ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 0)).1,
           ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 1)).1,
           ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).uSlot hn 2)).1} :
           Finset ℕ)} else (∅ : Finset (Finset ℕ))) =
      (if hn : X.IsBad = false then
        {({ℓ (.inl (G.σ (I.atom (I.shape.uSlot hn 0)).1)),
           ℓ (.inl (G.σ (I.atom (I.shape.uSlot hn 1)).1)),
           ℓ (.inl (G.σ (I.atom (I.shape.uSlot hn 2)).1))} : Finset ℕ)} else (∅ : Finset (Finset ℕ))) := by
    by_cases hn : X.IsBad = false
    · simp only [hn, dite_true, hu]
    · have hn' : X.IsBad = true := by simpa using hn
      simp [hn']
  rw [hcore]
  have hpairs : (univ.image fun j : Fin (I.shape.m + 1) =>
      ({ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).xSlot j)).1,
        ℓ ((G.insertedIndexing I hX ha hb).atom ((insertedShape I.shape hX).ySlot j)).1} :
        Finset ℕ)) =
      insert ({ℓ (.inr 0), ℓ (.inr 1)} : Finset ℕ)
        (univ.image fun j : Fin I.shape.m =>
          ({ℓ (.inl (G.σ (I.atom (I.shape.xSlot j)).1)),
            ℓ (.inl (G.σ (I.atom (I.shape.ySlot j)).1))} : Finset ℕ)) := by
    ext s
    simp only [mem_image, mem_univ, true_and, mem_insert]
    rw [Fin.exists_fin_succ']
    rw [hnx, hny]
    simp only [hx, hy]
    tauto
  rw [hpairs, Finset.insert_union]

end RungSpliceGeometry

namespace DirectedGraphIso
variable {V W β δ : Type*} [DecidableEq V] [DecidableEq W]
  [Fintype V] [Fintype W] [Fintype β] [Fintype δ]
  {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other)

/-- Relabeling a chart along a directed graph isomorphism moves its group labels. -/
theorem physicalChart_groupSet {X : VineType} {a b : V}
    (P : PhysicalGraphChart ends X a b) (ℓ : W → ℕ) :
    indexingGroupSet (I.physicalChart P).full.indexing ℓ =
      indexingGroupSet P.full.indexing (fun v => ℓ (I.atom v)) := rfl

end DirectedGraphIso
end WaveTurbulence.Vine.Param
