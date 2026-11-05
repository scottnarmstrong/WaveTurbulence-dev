/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVTypeIRemoval
public import WaveTurbulence.Foundations.Molecule.VineTypeVBranchRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineRemovalCongruence
import Mathlib.Tactic

/-! # Arbitrary disjoint ordinary vine removals preserve a DV -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, complete ordinary-removal clause for a DV. In fact
no decoration or SG premise is needed: each removed ordinary vine is a
double bond or an entire type-V branch, and disjointness permits at most
one branch removal. All paths are constructed from the actual templates. -/
theorem ordinary_vines_removal_in_DV_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : IsDV M U a b) (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  classical
  by_cases hAll : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right
  · exact DV_typeI_removal_connected M hM hU ps hAll hsub hD hdis
  · push Not at hAll
    obtain ⟨P0,hP0,hP0not⟩ := hAll
    have hP0V : M.IsVine .V P0.atoms P0.left P0.right :=
      (ordinary_vine_in_DV_shape M hM hU (hvine P0 hP0) (hsub P0 hP0)).resolve_left hP0not
    obtain ⟨S,T,hS,hT,hi,hUnion⟩ := hU
    have hChoice := typeV_in_DV_eq_branch M hM hS hT hi hP0V (hUnion ▸ hsub P0 hP0)
    obtain ⟨A,B,hA,hB,hAB,hUeq,hAtom⟩ :
        ∃ A B,M.IsVine .V A a b ∧ M.IsVine .V B a b ∧ A ∩ B={a,b} ∧ U=A ∪ B ∧ P0.atoms=A := by
      rcases hChoice with h | h
      · exact ⟨S,T,hS,hT,hi,hUnion,h⟩
      · exact ⟨T,S,hT,hS,by rw [inter_comm]; exact hi,hUnion.trans (union_comm S T),h⟩
    have hP0B : M.IsBlock P0.atoms a b := hAtom.symm ▸ hA.1
    have hPair := block_joints_unique M hP0V.1 hP0B
    let qs := ps.filter (fun P => P ≠ P0)
    have hIqs : ∀ P ∈ qs,M.IsVine .I P.atoms P.left P.right := by
      intro Q hQ
      have hQmem := (List.mem_filter.mp hQ).1
      have hQne : Q ≠ P0 := of_decide_eq_true (List.mem_filter.mp hQ).2
      by_contra hQnot
      have hDV : IsDV M U a b := ⟨S,T,hS,hT,hi,hUnion⟩
      have hQV := (ordinary_vine_in_DV_shape M hM hDV (hvine Q hQmem) (hsub Q hQmem)).resolve_left hQnot
      have hCQ := typeV_in_DV_eq_branch M hM hS hT hi hQV (hUnion ▸ hsub Q hQmem)
      have haQ : a ∈ Q.atoms := hCQ.elim (fun h => h.symm ▸ hS.1.2.1) (fun h => h.symm ▸ hT.1.2.1)
      exact (disjoint_left.mp (hdis P0 hP0 Q hQmem (Ne.symm hQne))) hP0B.2.1 haQ
    let C := blockRemoval M A a b
    have heq0 : P0.Equivalent C := by
      refine ⟨hAtom,hPair,?_⟩
      rw [hD P0 hP0,hAtom]
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
        · exact ⟨Q,(List.mem_filter.mp hQ).1,rfl,rfl,rfl⟩
    have hDqs : ∀ P ∈ qs,P.darts=univ.filter (M.InGroup P.atoms) :=
      fun P hP => hD P (List.mem_filter.mp hP).1
    have hDisqs : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms :=
      fun P hP Q hQ hne => hdis P (List.mem_filter.mp hP).1 Q (List.mem_filter.mp hQ).1 hne
    clear hUnion
    subst U
    obtain ⟨hBB,⟨R⟩⟩ := isVine_iff_realization.mp hB
    have hconn := typeV_other_branch_typeI_removal_connected M hM R hBB A hAB qs hIqs hDqs hDisqs
    have hrAtoms := remainingAtoms_congr_of_equivalent (A ∪ B) hEq
    intro u hu v hv
    exact removal_path_congr_of_equivalent M (A ∪ B) hEq.symm (hconn u (hrAtoms ▸ hu) v (hrAtoms ▸ hv))

end WaveTurbulence.Vine
