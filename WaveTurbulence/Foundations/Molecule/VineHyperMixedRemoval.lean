/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperOrdinaryRemoval
public import WaveTurbulence.Foundations.Molecule.VineMixedAdjointRetraction
import Mathlib.Tactic

/-! # Simultaneous ordinary and adjoint removals preserve an LG/ZG HV/HVC -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, simultaneous mixed-removal clause for a designated
LG/ZG HV/HVC. The ordinary part is derived from source gaps, while the
additional disjoint actual adjoints retract through their retained bonds. -/
theorem SG_mixed_removal_in_hyperLike_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (R : HyperLikeRealization M U a b)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hQsub : ∀ Q ∈ qs,Q.atoms ⊆ U)
    (hQdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    {r : Mom d} (hr : R.IsGap L w κ r)
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hSG : ∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG) :
    ∀ u ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      (removeBlocks M U (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  apply mixed_removal_connected_of_ordinary M hM U ps qs hQsub hQdis hcross
  · intro P hP d hd
    rw [hD P hP] at hd
    exact (mem_filter.mp hd).2
  · exact SG_ordinary_vines_removal_in_hyperLike_connected M hM R ps hvine hsub hD hdis
      L γ η w z κ hκ hz hr houter hSG

end WaveTurbulence.Vine
