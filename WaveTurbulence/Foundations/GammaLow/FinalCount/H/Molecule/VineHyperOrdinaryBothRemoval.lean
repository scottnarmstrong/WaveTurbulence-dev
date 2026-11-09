/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperOrdinaryBothRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperJointPairShape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperOrdinaryMissingRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.RemovalDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperOrdinaryBothRemoval`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Ordinary removals selecting both hyper-object joints preserve connectivity 

**Low-range change (L6-HDS).** The designated adjoint is a T-vine with `σ = 1` (N3 Cor 1.16′ (L-b); main: a vine (V));
the other removed ordinary vines are members of it avoiding the joints (any type of the low family; main: double
bonds), and the connectivity is N3 Lemma P (`DS.DV_branch_removal_connected` with the pair piece `{a, b}`; proved by
L3-LP). The statement is main's.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc's both-joints hyper-outer case. The selected ordinary
piece is their double bond and the designated adjoint is type V. All
other disjoint ordinary vines are double bonds; the checked type-V branch
geometry then applies after deleting the outer designated bond. -/
theorem ordinary_removal_in_hyperLike_of_both_joints_piece (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (R : Src.HyperLikeRealization Src.γL M U a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,Src.IsSomeVine Src.γL M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (P0 : RemovalPiece V D) (hP0 : P0 ∈ ps) (ha : a ∈ P0.atoms) (hb : b ∈ P0.atoms) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  classical
  obtain ⟨hAtoms,hI0,hAdjT,hσN⟩ := ordinary_vine_in_hyperLike_both_joint_shape M hM R
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
  let ns := qs.map (eraseOrdinaryPiece M R.added)
  have hvineN : ∀ P ∈ ns, Src.IsSomeVine Src.γL N P.atoms P.left P.right := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    let F := eraseBond_local_embedding M R.added P.atoms (hExternal P hP)
    exact (F.isVine_iffS P.atoms (Subset.refl _) P.left P.right).mpr (hvine P (hqs P hP))
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
  have hnsOut : ∀ P ∈ ns, P.atoms ⊆ U ∧ a ∉ P.atoms ∧ b ∉ P.atoms := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    exact ⟨hsub P (hqs P hP), (hOutside P hP).1, (hOutside P hP).2⟩
  have hns (P : RemovalPiece V {d : D // d ≠ R.added ∧ d ≠ M.mate R.added})
      (hP : P ∈ blockRemoval N {a,b} a b :: ns) (hne : P ≠ blockRemoval N {a,b} a b) : P ∈ ns :=
    (List.mem_cons.mp hP).resolve_left hne
  have hdisC : ∀ Q ∈ ns, Disjoint (blockRemoval N {a,b} a b).atoms Q.atoms := by
    intro Q hQ
    refine disjoint_left.mpr fun v hv hvQ => ?_
    change v ∈ ({a,b} : Finset V) at hv
    rcases mem_insert.mp hv with h | h
    · exact (hnsOut Q hQ).2.1 (h ▸ hvQ)
    · exact (hnsOut Q hQ).2.2 (mem_singleton.mp h ▸ hvQ)
  have hgeom := DS.DV_branch_removal_connected hN hσN hAdjT (inter_eq_left.mpr hPairSub)
    (blockRemoval N {a,b} a b::ns) (blockRemoval N {a,b} a b) List.mem_cons_self rfl (Or.inl ⟨rfl, rfl⟩) rfl
    (fun P hP hne => ⟨Src.Object.ofVine (hvineN P (hns P hP hne)), rfl, rfl, rfl, fun x => by
      rw [hDns P (hns P hP hne)]
      exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩⟩)
    (fun P hP hne => hnsOut P (hns P hP hne))
    (fun P hP Q hQ hPQ => by
      by_cases hP0 : P = blockRemoval N {a,b} a b
      · subst hP0
        exact hdisC Q (hns Q hQ (Ne.symm hPQ))
      · by_cases hQ0 : Q = blockRemoval N {a,b} a b
        · subst hQ0
          exact (hdisC P (hns P hP hP0)).symm
        · exact hDisns P (hns P hP hP0) Q (hns Q hQ hQ0) hPQ)
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

end WaveTurbulence.GammaLow.FinalCount.H
