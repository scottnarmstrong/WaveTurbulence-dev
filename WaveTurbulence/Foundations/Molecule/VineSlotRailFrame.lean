/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotRailLabels
public import WaveTurbulence.Foundations.Molecule.VineActualRailFrame
import Mathlib.Tactic

/-! # Actual source slots supply complete rail coordinate frames -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The exact source slot and allocation data construct a rail frame.
No cross-distinctness of the two final ports is required (F72). -/
@[expose] def VineRealization.slot_rail_frame {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (Q : FullRungSequence M k)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1)) :
    RailLabelFrame Q := by
  let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
  have hslot : s ∈ X.template.slots := by
    have hh : (s,k) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    exact (List.of_mem_zip hh).1
  have hs := template_slot_endpoints X s hslot
  have hn : X.template.n ≤ N := by
    dsimp [N]
    rw [fold_insertRungs_atoms]
    omega
  have hnon := template_slot_edges_nonloop X s hslot
  have hl := R.slot_rail_labels pre post s k hloc Q hports hlabels
  exact ⟨R.f,N,s.1.1,s.1.2,s.2.1,s.2.2,
    lt_of_lt_of_le hs.1 hn,lt_of_lt_of_le hs.2.1 hn,
    lt_of_lt_of_le hs.2.2.1 hn,lt_of_lt_of_le hs.2.2.2 hn,
    hnon.1,hnon.2,hl.1,hl.2⟩

end WaveTurbulence.Vine
