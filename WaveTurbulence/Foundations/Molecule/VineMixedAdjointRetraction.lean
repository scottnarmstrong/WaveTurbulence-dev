/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMixedAdjointJoints
import Mathlib.Tactic

/-! # Retract surviving ordinary-removal paths through disjoint adjoint pieces -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A path surviving ordinary removals retracts to a path after all
additional disjoint adjoint removals. Only the original molecule axioms
are used. The intermediate ordinary-removal graph need not be a molecule. -/
theorem ordinary_path_retract_adjoints (M : Molecule V D) (hM : M.IsMolecule)
    (S : Finset V) (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hsub : ∀ Q ∈ qs,Q.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d)
    {u v : V} (hu : u ∈ remainingAtoms S (ps++qs.map AdjointPiece.toRemoval))
    (hv : v ∈ remainingAtoms S (ps++qs.map AdjointPiece.toRemoval))
    (hp : (removeBlocks M S ps).SameComponent u v) :
    (removeBlocks M S (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  let rs := qs.map AdjointPiece.toRemoval
  let r := removalRetraction rs
  let N := removeBlocks M S (ps++rs)
  have hdisR := adjoint_removal_family_disjoint M qs hdis
  have hinsideR := adjoint_removal_family_inside M qs
  have hclosedR := adjoint_removal_family_closed M hM qs
  have hjoints := mixed_adjoint_joint_paths M S ps qs hsub hdis hcross hinside
  have edge (x y : V) (hxy : (removeBlocks M S ps).Adj x y) : N.SameComponent (r x) (r y) := by
    obtain ⟨d,hdx,hdy⟩ := hxy
    have hadj : M.Adj x y := ⟨d.1,hdx,hdy⟩
    by_cases hpiece : ∃ P,P ∈ rs ∧ x ∈ P.atoms ∧ y ∈ P.atoms
    · obtain ⟨P,hP,hxP,hyP⟩ := hpiece
      exact hjoints P hP _ (removalRetraction_joint rs hdisR hP hxP)
        _ (removalRetraction_joint rs hdisR hP hyP)
    · have hxI : ∀ P ∈ rs,x ∉ P.interior := by
        intro P hP hx
        exact hpiece ⟨P,hP,(mem_sdiff.mp hx).1,hclosedR P hP x hx y hadj⟩
      have hyI : ∀ P ∈ rs,y ∉ P.interior := by
        intro P hP hy
        exact hpiece ⟨P,hP,hclosedR P hP y hy x (Mole.adj_symmetric M hadj),(mem_sdiff.mp hy).1⟩
      have hxS : x ∈ S := hdx ▸ (mem_filter.mp d.2.1).1
      have hyS : y ∈ S := hdy ▸ (mem_filter.mp d.2.2.1).1
      have hxR : x ∈ remainingAtoms S rs := mem_filter.mpr ⟨hxS,hxI⟩
      have hyR : y ∈ remainingAtoms S rs := mem_filter.mpr ⟨hyS,hyI⟩
      have hrx : r x=x := removalRetraction_fixed S rs hxR
      have hry : r y=y := removalRetraction_fixed S rs hyR
      rw [hrx,hry]
      have hkR : KeepDart M S rs d.1 := by
        refine ⟨hdx.symm ▸ hxR,hdy.symm ▸ hyR,?_⟩
        intro P hP
        constructor
        · intro hdP
          have hh := hinsideR P hP d.1 hdP
          exact hpiece ⟨P,hP,hdx ▸ hh.1,hdy ▸ hh.2⟩
        · intro hdP
          have hh := hinsideR P hP (M.mate d.1) hdP
          have hlast : M.atom d.1 ∈ P.atoms := by simpa only [M.mate_mate] using hh.2
          exact hpiece ⟨P,hP,hdx ▸ hlast,hdy ▸ hh.1⟩
      have hk := (keepDart_append_iff M S ps rs d.1).mpr ⟨d.2,hkR⟩
      exact Relation.EqvGen.rel _ _ ⟨⟨d.1,hk⟩,hdx,hdy⟩
  have lift {x y : V} (h : (removeBlocks M S ps).SameComponent x y) :
      N.SameComponent (r x) (r y) := by
    induction h with
    | rel x y hxy => exact edge x y hxy
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hru : r u=u := removalRetraction_fixed S rs ((mem_remainingAtoms_append S ps rs u).mp hu).2
  have hrv : r v=v := removalRetraction_fixed S rs ((mem_remainingAtoms_append S ps rs v).mp hv).2
  simpa only [hru,hrv] using lift hp

/-- Conditional assembly helper: once ordinary-removal connectivity has
been established from source geometry, adding a disjoint actual adjoint
family preserves it. This helper does not replace any outer-object case. -/
theorem mixed_removal_connected_of_ordinary (M : Molecule V D) (hM : M.IsMolecule)
    (S : Finset V) (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hsub : ∀ Q ∈ qs,Q.atoms ⊆ S)
    (hdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d)
    (hconn : ∀ u ∈ remainingAtoms S ps,∀ v ∈ remainingAtoms S ps,
      (removeBlocks M S ps).SameComponent u v) :
    ∀ u ∈ remainingAtoms S (ps++qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms S (ps++qs.map AdjointPiece.toRemoval),
      (removeBlocks M S (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  intro u hu v hv
  exact ordinary_path_retract_adjoints M hM S ps qs hsub hdis hcross hinside hu hv
    (hconn u ((mem_remainingAtoms_append S ps _ u).mp hu).1
      v ((mem_remainingAtoms_append S ps _ v).mp hv).1)

end WaveTurbulence.Vine
