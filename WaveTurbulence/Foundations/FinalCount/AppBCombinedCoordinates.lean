/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCombinedRemoval
public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabels
import Mathlib.Tactic

/-! # Original physical coordinates inside a combined removal table -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P Q : AppbPattern} (r : AppbRealization M P) (s : AppbRealization r.post Q)

noncomputable def combinedIndexEquiv : Fin (P.edges.length+Q.edges.length) ≃ Fin (r.combinedPattern s).edges.length :=
  (finCongr (r.combinedPattern_length s)).symm

noncomputable def combinedLeftIndex (j : Fin P.edges.length) : Fin (r.combinedPattern s).edges.length :=
  r.combinedIndexEquiv s (Fin.castAdd Q.edges.length j)

noncomputable def combinedRightIndex (j : Fin Q.edges.length) : Fin (r.combinedPattern s).edges.length :=
  r.combinedIndexEquiv s (Fin.natAdd P.edges.length j)

theorem combinedLeftIndex_injective : Function.Injective (r.combinedLeftIndex s) := by
  intro i j h
  have hh := (r.combinedIndexEquiv s).injective h
  exact Fin.ext (congrArg (fun x : Fin (P.edges.length+Q.edges.length) => x.val) hh)

theorem combinedRightIndex_injective : Function.Injective (r.combinedRightIndex s) := by
  intro i j h
  have hh := congrArg Fin.val ((r.combinedIndexEquiv s).injective h)
  change P.edges.length+i.val = P.edges.length+j.val at hh
  exact Fin.ext (Nat.add_left_cancel hh)

theorem combinedLeftRight_ne (i : Fin P.edges.length) (j : Fin Q.edges.length) :
    r.combinedLeftIndex s i ≠ r.combinedRightIndex s j := by
  intro h
  have hh := congrArg Fin.val ((r.combinedIndexEquiv s).injective h)
  change i.val = P.edges.length+j.val at hh
  have hi := i.isLt
  omega

theorem combined_edge_left (v0 : M.atoms) (j : Fin P.edges.length) :
    ((r.combinedRemoval s v0).edge (r.combinedLeftIndex s j)).val = (r.edge j).val :=
  (appb_encoded_edge_val M _ _ v0 _ (Fin.castAdd Q.edges.length j)).trans (r.combinedEdgeEnumeration_left s j)

theorem combined_edge_right (v0 : M.atoms) (j : Fin Q.edges.length) :
    ((r.combinedRemoval s v0).edge (r.combinedRightIndex s j)).val = (s.edge j).val.val :=
  (appb_encoded_edge_val M _ _ v0 _ (Fin.natAdd P.edges.length j)).trans (r.combinedEdgeEnumeration_right s j)

theorem combined_labels_left (v0 : M.atoms) (κ : D → K) (j : Fin P.edges.length) :
    (r.combinedRemoval s v0).localLabels κ (r.combinedLeftIndex s j) = r.localLabels κ j := by
  change κ ((r.combinedRemoval s v0).edge (r.combinedLeftIndex s j)).val = κ (r.edge j).val
  rw [r.combined_edge_left]

theorem combined_labels_right (v0 : M.atoms) (κ : D → K) (j : Fin Q.edges.length) :
    (r.combinedRemoval s v0).localLabels κ (r.combinedRightIndex s j) = s.localLabels (r.retainedLabels κ) j := by
  change κ ((r.combinedRemoval s v0).edge (r.combinedRightIndex s j)).val = κ (s.edge j).val.val
  rw [r.combined_edge_right]

theorem combined_index_cases (i : Fin (r.combinedPattern s).edges.length) :
    (∃ j,r.combinedLeftIndex s j = i) ∨ (∃ j,r.combinedRightIndex s j = i) := by
  let E : (Fin P.edges.length ⊕ Fin Q.edges.length) ≃ Fin (r.combinedPattern s).edges.length :=
    finSumFinEquiv.trans (r.combinedIndexEquiv s)
  obtain ⟨j,hj⟩ := E.surjective i
  rcases j with j | j
  · exact Or.inl ⟨j,hj⟩
  · exact Or.inr ⟨j,hj⟩

end AppbRealization
end WaveTurbulence.Mole
