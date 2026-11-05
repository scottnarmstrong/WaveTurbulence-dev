/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperOrdinaryBothRemoval
import Mathlib.Tactic

/-! # Ordinary SG-vine removals preserve an LG/ZG hyper-vine-like object -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, complete ordinary-removal clause for a designated
LG/ZG HV/HVC. The both-joints double-bond case uses type-V geometry;
otherwise every piece transports to the designated adjoint VC. -/
theorem SG_ordinary_vines_removal_in_hyperLike_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (R : HyperLikeRealization M U a b)
    (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    {r : Mom d} (hr : R.IsGap L w κ r)
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hSG : ∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  classical
  by_cases hboth : ∃ P ∈ ps,a ∈ P.atoms ∧ b ∈ P.atoms
  · obtain ⟨P,hP,ha,hb⟩ := hboth
    exact ordinary_removal_in_hyperLike_of_both_joints_piece M hM R ps hvine hsub hD hdis P hP ha hb
  · have hmiss : ∀ P ∈ ps,¬(a ∈ P.atoms ∧ b ∈ P.atoms) :=
      fun P hP hp => hboth ⟨P,hP,hp⟩
    exact SG_ordinary_removal_in_hyperLike_of_missing_joint M hM R ps hvine hsub hD hdis hmiss
      L γ η w z κ hκ hz hr houter hSG

end WaveTurbulence.Vine
