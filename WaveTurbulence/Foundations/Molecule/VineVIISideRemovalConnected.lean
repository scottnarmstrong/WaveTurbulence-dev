/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVIIExpandedProtectedBackbone
import Mathlib.Tactic

/-! # Removing the full VII side and arbitrary double bonds preserves connectivity -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc's ordinary V-removal geometry inside type VII:
removing the complete side (retaining its joints 7/8) together with any
family of complete double-bond removals leaves a connected main body.
All red/cyan/green rung counts are arbitrary; no gap or path premise is
assumed. Source SG containment supplies this actual side via the earlier
structural classification. -/
theorem typeVII_side_typeI_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms)) :
    let A := R.selectedAtoms (sideLabels (11+2*kr) kc)
    let x := (R.coreAtom (7 : Fin 11)).1
    let y := (R.coreAtom (8 : Fin 11)).1
    ∀ u ∈ remainingAtoms S (blockRemoval M A x y::ps),
      ∀ v ∈ remainingAtoms S (blockRemoval M A x y::ps),
      (removeBlocks M S (blockRemoval M A x y::ps)).SameComponent u v := by
  dsimp only
  let A := R.selectedAtoms (sideLabels (11+2*kr) kc)
  let x := (R.coreAtom (7 : Fin 11)).1
  let y := (R.coreAtom (8 : Fin 11)).1
  let N := removeBlocks M S (blockRemoval M A x y::ps)
  have hr : remainingAtoms S (blockRemoval M A x y::ps)=
      S \ R.selectedAtoms (capLabels (11+2*kr) kc) := by
    rw [remainingAtoms_block_typeI M S A x y ps hI]
    rw [show A \ {x,y}=R.selectedAtoms (capLabels (11+2*kr) kc) from
      R.side_interior_eq (11+2*kr) kc (by omega)]
  have reach (z : V) (hz : z ∈ remainingAtoms S (blockRemoval M A x y::ps)) :
      N.SameComponent (R.coreAtom (0 : Fin 11)).1 z := by
    rw [hr] at hz
    have hp := R.typeVII_protected_to_atom hM kr kc kg hks z (mem_sdiff.mp hz).1 (mem_sdiff.mp hz).2
    exact protected_single_path_survives M S A x y ps hI hD hp
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

end WaveTurbulence.Vine
