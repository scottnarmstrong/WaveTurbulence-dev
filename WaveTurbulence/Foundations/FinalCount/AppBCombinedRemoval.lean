/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBUnionBondEnumeration
public import WaveTurbulence.Foundations.FinalCount.AppBEncodedRemovalProperties
import Mathlib.Tactic

/-! # A single actual realization of two successive deletion steps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P Q : AppbPattern} (r : AppbRealization M P) (s : AppbRealization r.post Q)

def combinedRemovedAtoms : Finset V := r.removedAtoms ∪ s.removedAtoms

theorem combinedRemovedAtoms_subset : r.combinedRemovedAtoms s ⊆ M.atoms := by
  apply union_subset r.removedAtoms_subset
  intro v hv
  exact (mem_sdiff.mp (s.removedAtoms_subset hv)).1

noncomputable def combinedPattern : AppbPattern :=
  appbEncodedRemovalPattern M (r.combinedRemovedAtoms s) (r.combinedRemovedAtoms_subset s) (r.combinedEdgeEnumeration s)

noncomputable def combinedRemoval (v0 : M.atoms) : AppbRealization M (r.combinedPattern s) :=
  appbEncodedRemoval M (r.combinedRemovedAtoms s) (r.combinedRemovedAtoms_subset s) v0 (r.combinedEdgeEnumeration s)

theorem combinedRemoval_removed (v0 : M.atoms) :
    (r.combinedRemoval s v0).removedAtoms = r.combinedRemovedAtoms s :=
  appb_encoded_removed_eq M _ _ v0 _

theorem combinedPattern_length : (r.combinedPattern s).edges.length = P.edges.length+Q.edges.length :=
  appb_encoded_edges_length M _ _ _

theorem combinedEdgeEnumeration_left (j : Fin P.edges.length) :
    (r.combinedEdgeEnumeration s (Fin.castAdd Q.edges.length j)).val = (r.edge j).val := by
  change (appbUnionBondEquiv M r.removedAtoms s.removedAtoms
    ((r.edge.sumCongr s.edge) (finSumFinEquiv.symm (Fin.castAdd Q.edges.length j)))).val = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem combinedEdgeEnumeration_right (j : Fin Q.edges.length) :
    (r.combinedEdgeEnumeration s (Fin.natAdd P.edges.length j)).val = (s.edge j).val.val := by
  change (appbUnionBondEquiv M r.removedAtoms s.removedAtoms
    ((r.edge.sumCongr s.edge) (finSumFinEquiv.symm (Fin.natAdd P.edges.length j)))).val = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

end AppbRealization
end WaveTurbulence.Mole
