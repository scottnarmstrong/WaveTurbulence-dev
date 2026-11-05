/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSGOrdinaryRemovalVC
public import WaveTurbulence.Foundations.Molecule.VineEraseOrdinaryRemovals
public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
import Mathlib.Tactic

/-! # Ordinary removals avoiding an outer hyper-object's closing bond -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, hyper-outer case when every removed ordinary vine
misses at least one outer joint. Deleting the designated outer bond
transports the entire actual family to its LG/ZG adjoint VC. The checked
ordinary-VC removal theorem then lifts back through the same darts. -/
theorem SG_ordinary_removal_in_hyperLike_of_missing_joint (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (R : HyperLikeRealization M U a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hmiss : ∀ P ∈ ps,¬(a ∈ P.atoms ∧ b ∈ P.atoms))
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    {r : Mom d} (hr : R.IsGap L w κ r)
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hSG : ∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  let N := Mole.eraseBond M R.added
  let qs := ps.map (eraseOrdinaryPiece M R.added)
  have hne := ends_distinct_of_pair M R.added R.ends_eq R.adjoint.1.2.2.2.1
  have hN := eraseBond_isMolecule M hM R.added hne
  obtain ⟨zN,hκN,hzN⟩ := eraseBond_decoration_exists M hM R.added hne L w z κ hκ hz
  have hVinesN : ∀ P ∈ qs,IsSomeVine N P.atoms P.left P.right := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    obtain ⟨X,hX⟩ := hvine P hP
    let F := eraseBond_local_embedding M R.added P.atoms
      (bond_external_of_missing_joint M R.added R.ends_eq (hmiss P hP))
    exact ⟨X,(F.isVine_iff X P.atoms (Subset.refl _) P.left P.right).mpr hX⟩
  have hSubN : ∀ P ∈ qs,P.atoms ⊆ U := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    exact hsub P hP
  have hDN : ∀ P ∈ qs,P.darts=univ.filter (N.InGroup P.atoms) := by
    intro Q hQ
    obtain ⟨P,_hP,rfl⟩ := List.mem_map.mp hQ
    rfl
  have hDisN : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms := by
    intro P hP Q hQ hPQ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hP
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hQ
    exact hdis p hp q hq (fun he => hPQ (congrArg (eraseOrdinaryPiece M R.added) he))
  have hSGN : ∀ P ∈ qs,∃ r' : Mom d,N.IsBlockGap L w (fun d => κ d.1) P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hQ
    obtain ⟨rP,hrP,hsgP⟩ := hSG P hP
    let F := eraseBond_local_embedding M R.added P.atoms
      (bond_external_of_missing_joint M R.added R.ends_eq (hmiss P hP))
    exact ⟨rP,(F.blockGap_iff P.atoms (Subset.refl _) L w κ P.left rP).mpr hrP,hsgP⟩
  have hconn := SG_ordinary_vines_removal_in_VC_connected N hN R.adjoint qs hVinesN hSubN hDN hDisN
    L γ η w zN (fun d => κ d.1) hκN hzN hr houter hSGN
  have hAtoms := remainingAtoms_eraseOrdinary M R.added U ps
  intro u hu v hv
  exact eraseBond_ordinary_removal_path_to M R.added U ps hD
    (hconn u (hAtoms.symm ▸ hu) v (hAtoms.symm ▸ hv))

end WaveTurbulence.Vine
