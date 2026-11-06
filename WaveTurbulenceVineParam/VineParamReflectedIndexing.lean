/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedSlots
public import WaveTurbulenceVineParam.VineParamSpliceGeometry
public import WaveTurbulenceVineParam.VineParamGraphMolecule
import Mathlib.Tactic

/-! # Actual included atoms after the cap reflection and rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]

/-- A cap permutation fixing the deleted joint induces the literal
permutation of included source atoms. -/
@[expose] def reflectedErasedEquiv (σ : V ≃ V) (a : V) (ha : σ a=a) :
    ↥((univ : Finset V).erase a) ≃ ↥((univ : Finset V).erase a) where
  toFun v := ⟨σ v.1,mem_erase.mpr ⟨by
    intro h
    have hh : σ v.1=σ a := h.trans ha.symm
    exact (mem_erase.mp v.2).1 (σ.injective hh),mem_univ _⟩⟩
  invFun v := ⟨σ.symm v.1,mem_erase.mpr ⟨by
    intro h
    have hh := congrArg σ h
    rw [σ.apply_symm_apply,ha] at hh
    exact (mem_erase.mp v.2).1 hh,mem_univ _⟩⟩
  left_inv v := Subtype.ext (σ.symm_apply_apply v.1)
  right_inv v := Subtype.ext (σ.apply_symm_apply v.1)

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- The old physical atom at v becomes the actual atom inl(σ v).
Both fresh rung atoms occupy their prescribed new x/y slots. -/
@[expose, reducible] def insertedIndexing {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) :
    Indexing (graphMolecule G.newEnds) X univ (.inl a) (.inl b) where
  shape := insertedShape I.shape hX
  atom := insertedAtomEquiv I.shape hX a
    (I.atom.trans (reflectedErasedEquiv G.σ a ha))
  lower := by
    change ((erasedUnivSumEquiv a).symm
      (Sum.map (I.atom.trans (reflectedErasedEquiv G.σ a ha)) id
        (slotInsertionEquiv I.shape hX (insertedShape I.shape hX).x0))).1=Sum.inl b
    rw [slotInsertionEquiv_reference]
    change Sum.inl (G.σ (I.atom I.shape.x0).1)=Sum.inl b
    rw [I.lower,hb]

/-- Exact old-atom value at every retained coordinate. -/
theorem insertedIndexing_old {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b)
    (i : Fin (insertedShape I.shape hX).n) (j : Fin I.shape.n)
    (hi : slotInsertionEquiv I.shape hX i=Sum.inl j) :
    ((G.insertedIndexing I hX ha hb).atom i).1=Sum.inl (G.σ (I.atom j).1) := by
  change ((erasedUnivSumEquiv a).symm
    (Sum.map (I.atom.trans (reflectedErasedEquiv G.σ a ha)) id
      (slotInsertionEquiv I.shape hX i))).1=_
  rw [hi]
  rfl

/-- The appended x atom is the actual first fresh vertex. -/
theorem insertedIndexing_new_x {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) :
    ((G.insertedIndexing I hX ha hb).atom
      ((insertedShape I.shape hX).xSlot (Fin.last I.shape.m))).1=Sum.inr 0 := by
  change ((erasedUnivSumEquiv a).symm
    (Sum.map (I.atom.trans (reflectedErasedEquiv G.σ a ha)) id
      (slotInsertionEquiv I.shape hX ((insertedShape I.shape hX).xSlot (Fin.last I.shape.m))))).1=_
  rw [slotInsertionEquiv_new_x]
  rfl

/-- The appended y atom is the actual second fresh vertex. -/
theorem insertedIndexing_new_y {X : VineType} {a b : V}
    (I : Indexing (graphMolecule G.ends) X univ a b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) :
    ((G.insertedIndexing I hX ha hb).atom
      ((insertedShape I.shape hX).ySlot (Fin.last I.shape.m))).1=Sum.inr 1 := by
  change ((erasedUnivSumEquiv a).symm
    (Sum.map (I.atom.trans (reflectedErasedEquiv G.σ a ha)) id
      (slotInsertionEquiv I.shape hX ((insertedShape I.shape hX).ySlot (Fin.last I.shape.m))))).1=_
  rw [slotInsertionEquiv_new_y]
  rfl

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
