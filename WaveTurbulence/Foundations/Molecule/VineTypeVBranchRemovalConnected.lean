/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeVExpandedProtected
public import WaveTurbulence.Foundations.Molecule.VineProtectedPathMono
public import WaveTurbulence.Foundations.Molecule.VineBlockTypeIExternalEdge
public import WaveTurbulence.Foundations.Molecule.VineBackboneCenter
import Mathlib.Tactic

/-! # Removing one branch leaves a connected type V despite double removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, DV branch-removal geometry: if one branch shares
only the joints with a retained type-V branch, deleting it (including the
shared joint bond) together with any disjoint family of type-I pieces
leaves a connected graph. The removed branch need not itself be a vine
for this geometric statement; all retained paths are proved in type V. -/
theorem typeV_other_branch_typeI_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (A : Finset V) (hAB : A ∩ B={a,b}) (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms (A ∪ B) (blockRemoval M A a b::ps),
      ∀ v ∈ remainingAtoms (A ∪ B) (blockRemoval M A a b::ps),
      (removeBlocks M (A ∪ B) (blockRemoval M A a b::ps)).SameComponent u v := by
  let U := A ∪ B
  let N := removeBlocks M U (blockRemoval M A a b::ps)
  have hlen : R.k.length=1 := R.length_eq
  obtain ⟨k,hk⟩ := List.length_eq_one_iff.mp hlen
  have hRemain : remainingAtoms U (blockRemoval M A a b::ps)=B := by
    rw [remainingAtoms_block_typeI M U A a b ps hI]
    ext v
    constructor
    · intro hv
      have hh := mem_sdiff.mp hv
      rcases mem_union.mp hh.1 with hvA | hvB
      · by_cases hj : v ∈ ({a,b} : Finset V)
        · rcases mem_insert.mp hj with he | he
          · exact he.symm ▸ hB.2.1
          · exact (mem_singleton.mp he).symm ▸ hB.2.2.1
        · exact False.elim (hh.2 (mem_sdiff.mpr ⟨hvA,hj⟩))
      · exact hvB
    · intro hv
      exact mem_sdiff.mpr ⟨mem_union_right A hv,other_branch_atoms_survive hAB hv⟩
  have goodReach (v : V) (hv : v ∈ B) (hc : R.f v ≠ 8) :
      N.SameComponent (R.coreAtom (0 : Fin 9)).1 v := by
    have hp := R.typeV_other_branch_protected_to_atom hB hM A hAB k hk v hv hc
    exact protected_single_path_survives M U A a b ps hI hD
      (protected_single_path_mono M (show B ⊆ U from subset_union_right) hp)
  have centerAdj (j : Fin 9) (hj : j=(6 : Fin 9) ∨ j=(7 : Fin 9)) :
      M.Adj (R.coreAtom (8 : Fin 9)).1 (R.coreAtom j).1 := by
    apply R.center_core_adj (8 : Fin 9) j (by decide) (by decide)
    rcases hj with rfl | rfl <;> decide
  have h86 : (R.coreAtom (8 : Fin 9)).1 ≠ (R.coreAtom (6 : Fin 9)).1 :=
    fun h => (by decide : (8 : Fin 9) ≠ 6) (R.coreAtom_injective h)
  have h87 : (R.coreAtom (8 : Fin 9)).1 ≠ (R.coreAtom (7 : Fin 9)).1 :=
    fun h => (by decide : (8 : Fin 9) ≠ 7) (R.coreAtom_injective h)
  have h67 : (R.coreAtom (6 : Fin 9)).1 ≠ (R.coreAtom (7 : Fin 9)).1 :=
    fun h => (by decide : (6 : Fin 9) ≠ 7) (R.coreAtom_injective h)
  have hcOutside : (R.coreAtom (8 : Fin 9)).1 ∉ A :=
    R.nonjoint_outside_other_branch hB A hAB (R.coreAtom (8 : Fin 9)).2
      (by rw [R.label_coreAtom (8 : Fin 9)]; decide)
  have centerKeep (j : Fin 9) (hj : j=(6 : Fin 9) ∨ j=(7 : Fin 9))
      (hNo : ∀ P ∈ ps,¬((R.coreAtom (8 : Fin 9)).1 ∈ P.atoms ∧ (R.coreAtom j).1 ∈ P.atoms)) :
      N.Adj (R.coreAtom (8 : Fin 9)).1 (R.coreAtom j).1 := by
    exact block_typeI_external_adj M U A a b ps hI hD
      (mem_union_right A (R.coreAtom (8 : Fin 9)).2) (mem_union_right A (R.coreAtom j).2)
      (other_branch_atoms_survive hAB (R.coreAtom (8 : Fin 9)).2)
      (other_branch_atoms_survive hAB (R.coreAtom j).2)
      (fun h => hcOutside h.1) hNo (centerAdj j hj)
  have centerReach : N.SameComponent (R.coreAtom (0 : Fin 9)).1 (R.coreAtom (8 : Fin 9)).1 := by
    rcases typeI_family_keeps_one_neighbor M ps hI hdis h86 h87 h67 with h | h
    · have hp := goodReach (R.coreAtom (6 : Fin 9)).1 (R.coreAtom (6 : Fin 9)).2
        (by rw [R.label_coreAtom (6 : Fin 9)]; decide)
      exact Relation.EqvGen.trans _ _ _ hp
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (centerKeep (6 : Fin 9) (Or.inl rfl) h)))
    · have hp := goodReach (R.coreAtom (7 : Fin 9)).1 (R.coreAtom (7 : Fin 9)).2
        (by rw [R.label_coreAtom (7 : Fin 9)]; decide)
      exact Relation.EqvGen.trans _ _ _ hp
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (centerKeep (7 : Fin 9) (Or.inr rfl) h)))
  have reach (v : V) (hv : v ∈ B) : N.SameComponent (R.coreAtom (0 : Fin 9)).1 v := by
    by_cases hc : R.f v=8
    · have he : (R.coreAtom (8 : Fin 9)).1=v :=
        R.injOn (R.coreAtom (8 : Fin 9)).2 hv ((R.label_coreAtom (8 : Fin 9)).trans hc.symm)
      simpa only [he] using centerReach
    · exact goodReach v hv hc
  intro u hu v hv
  rw [hRemain] at hu hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

end WaveTurbulence.Vine
