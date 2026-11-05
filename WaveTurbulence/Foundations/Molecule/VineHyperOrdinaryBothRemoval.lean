/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperJointPairShape
public import WaveTurbulence.Foundations.Molecule.VineHyperOrdinaryMissingRemoval
public import WaveTurbulence.Foundations.Molecule.VineTypeVBranchRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineLargeVCInTypeV
public import WaveTurbulence.Foundations.Molecule.VineRemovalAmbientEq
public import WaveTurbulence.Foundations.Molecule.VineRemovalCongruence
import Mathlib.Tactic

/-! # Ordinary removals selecting both hyper-object joints preserve connectivity -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc's both-joints hyper-outer case. The selected ordinary
piece is their double bond and the designated adjoint is type V. All
other disjoint ordinary vines are double bonds; the checked type-V branch
geometry then applies after deleting the outer designated bond. -/
theorem ordinary_removal_in_hyperLike_of_both_joints_piece (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (R : HyperLikeRealization M U a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (P0 : RemovalPiece V D) (hP0 : P0 ∈ ps) (ha : a ∈ P0.atoms) (hb : b ∈ P0.atoms) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  classical
  obtain ⟨hAtoms,hI0,hAdjV⟩ := ordinary_vine_in_hyperLike_both_joint_shape M hM R
    (hvine P0 hP0) (hsub P0 hP0) ha hb
  let N := Mole.eraseBond M R.added
  have hne := ends_distinct_of_pair M R.added R.ends_eq R.adjoint.1.2.2.2.1
  have hN := eraseBond_isMolecule M hM R.added hne
  let qs := ps.filter (fun P => P ≠ P0)
  have hqs (P : RemovalPiece V D) (hP : P ∈ qs) : P ∈ ps := (List.mem_filter.mp hP).1
  have hOutside (P : RemovalPiece V D) (hP : P ∈ qs) : a ∉ P.atoms ∧ b ∉ P.atoms := by
    have hPne : P ≠ P0 := of_decide_eq_true (List.mem_filter.mp hP).2
    have hd := disjoint_left.mp (hdis P0 hP0 P (hqs P hP) (Ne.symm hPne))
    exact ⟨fun hh => hd ha hh,fun hh => hd hb hh⟩
  have hExternal (P : RemovalPiece V D) (hP : P ∈ qs) : ¬M.InGroup P.atoms R.added :=
    bond_external_of_missing_joint M R.added R.ends_eq (fun h => (hOutside P hP).1 h.1)
  have hIqs : ∀ P ∈ qs,M.IsVine .I P.atoms P.left P.right := by
    intro P hP
    obtain ⟨X,hX⟩ := hvine P (hqs P hP)
    let F := eraseBond_local_embedding M R.added P.atoms (hExternal P hP)
    have hXN : N.IsVine X P.atoms P.left P.right :=
      (F.isVine_iff X P.atoms (Subset.refl _) P.left P.right).mpr hX
    have hc : P.atoms.card<4 := by
      by_contra hh
      have he := large_VC_in_typeV_eq N hN hAdjV (isVine_isVC hXN) (hsub P (hqs P hP)) (by omega)
      exact (hOutside P hP).1 (he.symm ▸ R.adjoint.1.2.1)
    have htype := isVine_typeI_of_card_lt_four hX hc
    subst X
    exact hX
  let ns := qs.map (eraseOrdinaryPiece M R.added)
  have hIns : ∀ P ∈ ns,N.IsVine .I P.atoms P.left P.right := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    let F := eraseBond_local_embedding M R.added P.atoms (hExternal P hP)
    exact (F.isVine_iff .I P.atoms (Subset.refl _) P.left P.right).mpr (hIqs P hP)
  have hDns : ∀ P ∈ ns,P.darts=univ.filter (N.InGroup P.atoms) := by
    intro Q hQ
    obtain ⟨P,_hP,rfl⟩ := List.mem_map.mp hQ
    rfl
  have hDisns : ∀ P ∈ ns,∀ Q ∈ ns,P ≠ Q → Disjoint P.atoms Q.atoms := by
    intro P hP Q hQ hPQ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hQ
    exact hdis p (hqs p hp) q (hqs q hq)
      (fun he => hPQ (congrArg (eraseOrdinaryPiece M R.added) he))
  have hPairSub : ({a,b} : Finset V) ⊆ U := by
    intro v hv
    rcases mem_insert.mp hv with h | h
    · exact h.symm ▸ R.adjoint.1.2.1
    · exact (mem_singleton.mp h).symm ▸ R.adjoint.1.2.2.1
  obtain ⟨hUB,⟨RV⟩⟩ := isVine_iff_realization.mp hAdjV
  have hgeom := typeV_other_branch_typeI_removal_connected N hN RV hUB ({a,b} : Finset V)
    (inter_eq_left.mpr hPairSub) ns hIns hDns hDisns
  have hGeomU := removal_connected_change_ambient N (blockRemoval N {a,b} a b::ns)
    (union_eq_right.mpr hPairSub) hgeom
  let C := blockRemoval M {a,b} a b
  have hPair : ({P0.left,P0.right} : Finset V)={a,b} := (typeI_atoms hI0).symm.trans hAtoms
  have heq0 : P0.Equivalent C := by
    refine ⟨hAtoms,hPair,?_⟩
    rw [hD P0 hP0,hAtoms]
    rfl
  have hEq : RemovalFamilyEquivalent ps (C::qs) := by
    constructor
    · intro P hP
      by_cases hp : P=P0
      · subst P
        exact ⟨C,List.mem_cons_self,heq0⟩
      · exact ⟨P,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hP,by simpa using hp⟩),rfl,rfl,rfl⟩
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨P0,hP0,heq0⟩
      · exact ⟨Q,hqs Q hQ,rfl,rfl,rfl⟩
  have hDC : ∀ P ∈ C::qs,P.darts=univ.filter (M.InGroup P.atoms) := by
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · rfl
    · exact hD P (hqs P hP)
  have hCanon := remainingAtoms_congr_of_equivalent U hEq
  have hErased := remainingAtoms_eraseOrdinary M R.added U (C::qs)
  intro u hu v hv
  have hpN := hGeomU u (hErased.symm ▸ (hCanon ▸ hu)) v (hErased.symm ▸ (hCanon ▸ hv))
  have hpM := eraseBond_ordinary_removal_path_to M R.added U (C::qs) hDC hpN
  exact removal_path_congr_of_equivalent M U hEq.symm hpM

end WaveTurbulence.Vine
