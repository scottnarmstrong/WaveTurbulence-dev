/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedContractPhases
import Mathlib.Tactic

/-! # Exact old interior node phases after reanchored rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

/-- Every nonreference included coordinate is a source interior atom. -/
theorem indexing_atom_interior {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (I : Indexing M X S a b) (j : Fin I.shape.n) (hj : j ≠ I.shape.x0) :
    (I.atom j).1 ≠ a ∧ (I.atom j).1 ≠ b := by
  refine ⟨(mem_erase.mp (I.atom j).2).1,?_⟩
  intro h
  apply hj
  apply I.atom.injective
  exact Subtype.ext (h.trans I.lower.symm)

namespace RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

omit [Fintype V] in
/-- The old-coordinate shear changes only the physical reference. -/
theorem insertionOldCoordinates_nonreference {ι E : Type*} [DecidableEq ι] [AddCommGroup E]
    (a b : V) (r : E) (ref : ι) (anchor : Bool) (x : ι ⊕ Fin 2 → E)
    (j : ι) (hj : j ≠ ref) :
    G.insertionOldCoordinates a b r ref anchor x j=x (.inl j) := by
  simp only [insertionOldCoordinates,hj,false_and,ite_false,sub_zero]

omit [Fintype V] in
/-- Reindexing a retained nonreference slot removes the old reference shear
and gives exactly its public contract coordinate. -/
theorem reindexedOldCoordinate_eq {X : VineType} (A : Shape X) (hX : X ≠ .I)
    {E : Type} [AddCommGroup E] (a b : V) (r : E) (anchor : Bool)
    (x : Fin (insertedShape A hX).n → E)
    (i : Fin (insertedShape A hX).n) (j : Fin A.n)
    (hij : slotInsertionEquiv A hX i=Sum.inl j) (hj : j ≠ A.x0) :
    G.insertionOldCoordinates a b r A.x0 anchor
      (fun q => x ((slotInsertionEquiv A hX).symm q)) j=x i := by
  rw [G.insertionOldCoordinates_nonreference a b r A.x0 anchor _ j hj]
  have h := congrArg (slotInsertionEquiv A hX).symm hij
  rw [Equiv.symm_apply_apply] at h
  rw [← h]

/-- At a retained interior atom, the exact new node resonance is the old
one evaluated at the explicit reference shear. No phase formula is assumed. -/
theorem insertedContractChart_old_node {X : VineType} {a b : V}
    (F : FullVineChart (graphMolecule G.ends) X univ a b) (hab : a ≠ b)
    (hX : X ≠ .I) (ha : G.σ a=a) (hb : G.σ b=b) (anchor : Bool)
    (d : ℕ) (g r : Mom d) (x : Fin (insertedShape F.indexing.shape hX).n → Mom d)
    (i : Fin (insertedShape F.indexing.shape hX).n) (j : Fin F.indexing.shape.n)
    (hij : slotInsertionEquiv F.indexing.shape hX i=Sum.inl j)
    (hj : j ≠ F.indexing.shape.x0) :
    nodeResonance (G.insertedIndexing F.indexing hX ha hb)
      ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1 g r i=
    nodeResonance F.indexing
      ((F.chart g r).symm
        (G.insertionOldCoordinates a b r F.indexing.shape.x0 anchor
          (fun q => x ((slotInsertionEquiv F.indexing.shape hX).symm q)))).1 g r j := by
  have hi : i ≠ (insertedShape F.indexing.shape hX).x0 := by
    intro h
    rw [h,slotInsertionEquiv_reference] at hij
    exact hj (Sum.inl.inj hij).symm
  have hv := indexing_atom_interior F.indexing j hj
  simp only [nodeResonance]
  change energy (graphMolecule G.newEnds) univ
    ((G.insertedContractChart F hab hX ha hb anchor g r).symm x).1
      ((G.insertedIndexing F.indexing hX ha hb).atom i).1+
      (if i=(insertedShape F.indexing.shape hX).x0 then _ else 0)=_
  rw [ite_eq_right hi,ite_eq_right hj,add_zero,add_zero,G.insertedIndexing_old F.indexing hX ha hb i j hij,
    G.insertedContractChart_energy,G.anchoredInsertionChart_decode_labels,G.globalSourceChart_energy]
  have hf : directedFlow G.ends (F.indexing.atom j).1
      ((G.oldDirectedChart F hab g r).symm
        (G.insertionOldCoordinates a b r F.indexing.shape.x0 anchor
          (fun q => x ((slotInsertionEquiv F.indexing.shape hX).symm q)))).1=0 := by
    have h := ((G.oldDirectedChart F hab g r).symm
      (G.insertionOldCoordinates a b r F.indexing.shape.x0 anchor
        (fun q => x ((slotInsertionEquiv F.indexing.shape hX).symm q)))).2 (F.indexing.atom j).1
    simpa only [rootForcing,hv.1,hv.2,ite_false] using h
  rw [hf,inner_zero_left,mul_zero,add_zero,G.oldDirectedChart_energy]

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
