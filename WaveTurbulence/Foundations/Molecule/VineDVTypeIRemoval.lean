/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVOrdinaryShapes
public import WaveTurbulence.Foundations.Molecule.VineTypeIRemovalConnected
public import WaveTurbulence.Foundations.Molecule.VineRemovalLocalPaths
import Mathlib.Tactic

/-! # Simultaneous double-bond removals preserve a DV -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A disjoint family of type-I removals in a DV preserves connectivity.
Each double bond lies in one actual type-V branch and avoids the shared
joints, so the two retained branch backbones glue at either joint. -/
theorem DV_typeI_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : IsDV M U a b) (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  obtain ⟨S,T,hS,hT,hi,rfl⟩ := hU
  have hparts : ∀ P ∈ ps,(P.atoms ⊆ S ∧ Disjoint P.atoms T) ∨
      (P.atoms ⊆ T ∧ Disjoint P.atoms S) := by
    intro P hP
    exact typeI_in_DV_split_disjoint M hM hS hT hi (hI P hP) (hsub P hP)
  classical
  let qs := ps.filter (fun P => P.atoms ⊆ S)
  let ts := ps.filter (fun P => P.atoms ⊆ T)
  have hqs (P : RemovalPiece V D) (hP : P ∈ qs) : P ∈ ps := (List.mem_filter.mp hP).1
  have hts (P : RemovalPiece V D) (hP : P ∈ ts) : P ∈ ps := (List.mem_filter.mp hP).1
  have hqsParts : ∀ P ∈ ps,P ∈ qs ∨ Disjoint P.atoms S := by
    intro P hP
    rcases hparts P hP with ⟨hPS,_hPT⟩ | ⟨_hPT,hPS⟩
    · exact Or.inl (List.mem_filter.mpr ⟨hP,by simpa using hPS⟩)
    · exact Or.inr hPS
  have htsParts : ∀ P ∈ ps,P ∈ ts ∨ Disjoint P.atoms T := by
    intro P hP
    rcases hparts P hP with ⟨_hPS,hPT⟩ | ⟨hPT,_hPS⟩
    · exact Or.inr hPT
    · exact Or.inl (List.mem_filter.mpr ⟨hP,by simpa using hPT⟩)
  have hconnS := nontrivial_vine_typeI_removal_connected M hM (by decide : VineType.V ≠ .I) hS qs
    (fun P hP => hI P (hqs P hP)) (fun P hP => hD P (hqs P hP))
    (fun P hP Q hQ hne => hdis P (hqs P hP) Q (hqs Q hQ) hne)
  have hconnT := nontrivial_vine_typeI_removal_connected M hM (by decide : VineType.V ≠ .I) hT ts
    (fun P hP => hI P (hts P hP)) (fun P hP => hD P (hts P hP))
    (fun P hP Q hQ hne => hdis P (hts P hP) Q (hts Q hQ) hne)
  have hinside : ∀ P ∈ ps,∀ d ∈ P.darts,M.InGroup P.atoms d := by
    intro P hP d hd
    rw [hD P hP] at hd
    exact (mem_filter.mp hd).2
  have reach (u : V) (hu : u ∈ remainingAtoms (S ∪ T) ps) :
      (removeBlocks M (S ∪ T) ps).SameComponent u a := by
    rcases mem_union.mp (mem_filter.mp hu).1 with huS | huT
    · exact removal_local_path_lift M (show S ⊆ S ∪ T from subset_union_left) qs ps
        hqsParts hinside (hconnS u huS a hS.1.2.1)
    · exact removal_local_path_lift M (show T ⊆ S ∪ T from subset_union_right) ts ps
        htsParts hinside (hconnT u huT a hT.1.2.1)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (reach u hu) (Relation.EqvGen.symm _ _ (reach v hv))

end WaveTurbulence.Vine
