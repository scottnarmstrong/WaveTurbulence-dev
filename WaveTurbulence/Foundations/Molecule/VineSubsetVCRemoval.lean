/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSGMixedRemovalVC
public import WaveTurbulence.Foundations.Molecule.VineHyperMixedRemoval
public import WaveTurbulence.Foundations.Molecule.VineDVMixedRemoval
public import WaveTurbulence.Foundations.Molecule.VineLikeGapObjects
import Mathlib.Tactic

/-! # Complete simultaneous-removal clause of TARGET Lemma subsetvc -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, all outer objects and simultaneous ordinary/adjoint
removals. Ordinary removed pieces are actual SG vines. Adjoint pieces
retain their designated bond and may be arbitrary actual hyper-block
adjoints for this connectivity claim; hence the source's selected vine
adjoints are included. The classification clause is proved separately in
`subsetvc_classification`, with compatible-designation containment. -/
theorem subsetvc_simultaneous_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hQsub : ∀ Q ∈ qs,Q.atoms ⊆ U)
    (hQdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    (hSG : ∀ P ∈ ps,∃ r' : Mom d,M.IsBlockGap L w κ P.atoms P.left r' ∧
      Molecule.gapKind L γ η r'=.SG)
    (houter : IsDV M U a b ∨ ∃ C : VineLikeObject M U a b,∃ r : Mom d,
      C.IsGap L w κ r ∧ (Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)) :
    ∀ u ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      (removeBlocks M U (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  rcases houter with hDV | ⟨C,r,hr,hkind⟩
  · exact mixed_vines_removal_in_DV_connected M hM hDV ps qs hvine hsub hD hdis hQsub hQdis hcross
  · cases C with
    | vc hVC =>
      exact SG_mixed_removal_in_VC_connected M hM hVC ps qs hvine hsub hD hdis hQsub hQdis hcross
        L γ η w z κ hκ hz hr hkind hSG
    | hyper R =>
      exact SG_mixed_removal_in_hyperLike_connected M hM R ps qs hvine hsub hD hdis hQsub hQdis hcross
        L γ η w z κ hκ hz hr hkind hSG

end WaveTurbulence.Vine
