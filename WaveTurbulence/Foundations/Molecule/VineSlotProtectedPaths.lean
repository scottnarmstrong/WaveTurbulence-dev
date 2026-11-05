/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotSinglePaths
public import WaveTurbulence.Foundations.Molecule.VineProtectedRailPaths
public import WaveTurbulence.Foundations.Molecule.VineOldSingleAdj
import Mathlib.Tactic

/-! # Source slots protected from one ordinary block removal -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact source slot data and primitive avoidance data give two protected
port-to-port paths. At zero rungs the old bonds must not belong to the
removed piece; positive rungs are protected by their fresh vertices. -/
theorem VineRealization.slot_protected_paths {M : Molecule V D} {X : VineType}
    {S A : Finset V} {a b x y : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (Q : FullRungSequence M k) (hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1))
    (H : RailAvoidsPiece Q A x y)
    (hzero : k=0 → ¬(Q.u 0 ∈ A ∧ Q.u (k+1) ∈ A) ∧
      ¬(Q.v 0 ∈ A ∧ Q.v (k+1) ∈ A)) :
    Relation.EqvGen (ProtectedSingleAdj M S A x y) (Q.u 0) (Q.u (k+1)) ∧
      Relation.EqvGen (ProtectedSingleAdj M S A x y) (Q.v 0) (Q.v (k+1)) := by
  by_cases hk : k=0
  · subst k
    have hsk : (s,0) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    have hs := (List.of_mem_zip hsk).1
    have hb := template_slot_endpoints X s hs
    have hc := template_slot_unordered_single X s hs
    have hn := template_slot_edges_nonloop X s hs
    have hu := R.old_single_of_adj (hmem 0).1 (hmem 1).1
      (by rw [hports.1]; exact hb.1) (by rw [hports.2.2.1]; exact hb.2.1)
      (by rw [hports.1,hports.2.2.1]; exact hn.1)
      (by rw [hports.1,hports.2.2.1]; exact hc.1)
      (R.zero_slot_adj s hsk s.1 (Or.inl rfl) (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1)
    have hv := R.old_single_of_adj (hmem 0).2 (hmem 1).2
      (by rw [hports.2.1]; exact hb.2.2.1) (by rw [hports.2.2.2]; exact hb.2.2.2)
      (by rw [hports.2.1,hports.2.2.2]; exact hn.2)
      (by rw [hports.2.1,hports.2.2.2]; exact hc.2)
      (R.zero_slot_adj s hsk s.2 (Or.inr rfl) (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2)
    exact ⟨Relation.EqvGen.rel _ _ ⟨hu,(H.survive 0 (by omega)).1,
      (H.survive 1 le_rfl).1,(hzero rfl).1⟩,
      Relation.EqvGen.rel _ _ ⟨hv,(H.survive 0 (by omega)).2,
      (H.survive 1 le_rfl).2,(hzero rfl).2⟩⟩
  · let F := R.slot_rail_frame pre post s k hloc Q hports hlabels
    exact ⟨F.upper_protected_complete hM S A x y hmem H (by omega),
      F.lower_protected_complete hM S A x y hmem H (by omega)⟩

end WaveTurbulence.Vine
