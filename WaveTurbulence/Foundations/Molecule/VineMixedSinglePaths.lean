/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoubleRemovalRails
import Mathlib.Tactic

/-! # Single-bond paths outside one removed block survive all double removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A single edge whose endpoints survive a designated ordinary removal
and which is not an internal bond of that removal. -/
@[expose] def ProtectedSingleAdj (M : Molecule V D) (S : Finset V)
    (A : Finset V) (a b u v : V) : Prop :=
  SingleGroupAdj M S u v ∧ u ∉ A \ {a,b} ∧ v ∉ A \ {a,b} ∧ ¬(u ∈ A ∧ v ∈ A)

/-- Type-I removals add no deleted atom to one ordinary block removal. -/
theorem remainingAtoms_block_typeI (M : Molecule V D) (S A : Finset V) (a b : V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right) :
    remainingAtoms S (blockRemoval M A a b::ps)=S \ (A \ {a,b}) := by
  ext v
  constructor
  · intro hv
    have hh := mem_filter.mp hv
    exact mem_sdiff.mpr ⟨hh.1,hh.2 _ List.mem_cons_self⟩
  · intro hv
    refine mem_filter.mpr ⟨(mem_sdiff.mp hv).1,?_⟩
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · exact (mem_sdiff.mp hv).2
    · change v ∉ P.atoms \ {P.left,P.right}
      rw [typeI_atoms (hI P hP),sdiff_self]
      simp

/-- A protected single edge survives one ordinary block and any family
of complete type-I removals. The helper assumes actual source removal
pieces, not replacement paths. -/
theorem protected_single_adj_survives (M : Molecule V D) (S A : Finset V) (a b : V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V} (h : ProtectedSingleAdj M S A a b u v) :
    (removeBlocks M S (blockRemoval M A a b::ps)).Adj u v := by
  classical
  obtain ⟨⟨hu,hv,hne,⟨d,hdu,hdv⟩,hd⟩,huA,hvA,hn⟩ := h
  have hr := remainingAtoms_block_typeI M S A a b ps hI
  have hk : KeepDart M S (blockRemoval M A a b::ps) d := by
    refine ⟨hr.symm ▸ mem_sdiff.mpr ⟨hdu.symm ▸ hu,by simpa only [hdu] using huA⟩,
      hr.symm ▸ mem_sdiff.mpr ⟨hdv.symm ▸ hv,by simpa only [hdv] using hvA⟩,?_⟩
    intro P hP
    have hnot : ¬M.InGroup P.atoms d := by
      intro hin
      rcases List.mem_cons.mp hP with rfl | hP
      · exact hn ⟨hdu ▸ hin.1,hdv ▸ hin.2⟩
      · exact single_pair_not_in_typeI M (hI P hP) (hdu ▸ hin.1) (hdv ▸ hin.2) hne hd
    have hPd : P.darts=univ.filter (M.InGroup P.atoms) := by
      rcases List.mem_cons.mp hP with rfl | hP
      · rfl
      · exact hD P hP
    rw [hPd]
    constructor
    · simpa only [mem_filter,mem_univ,true_and] using hnot
    · intro hm
      have hh := (mem_filter.mp hm).2
      exact hnot ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩
  exact ⟨⟨d,hk⟩,hdu,hdv⟩

/-- Every protected single-bond path survives the mixed ordinary family. -/
theorem protected_single_path_survives (M : Molecule V D) (S A : Finset V) (a b : V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V} (hp : Relation.EqvGen (ProtectedSingleAdj M S A a b) u v) :
    (removeBlocks M S (blockRemoval M A a b::ps)).SameComponent u v := by
  induction hp with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (protected_single_adj_survives M S A a b ps hI hD huv)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.Vine
