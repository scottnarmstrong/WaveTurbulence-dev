/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotFullDistinct
import Mathlib.Tactic

/-! # Exact complete rail labels, permitting coincident final ports (F72) -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Slot endpoints and allocations determine both rail label functions,
including endpoints, even when the two final ports coincide. -/
theorem VineRealization.slot_rail_labels {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (_hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (Q : FullRungSequence M k)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1)) :
    let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
    (∀ i : Fin (k+2),R.f (Q.u i.1)=railAtom N s.1.1 s.1.2 k i.1) ∧
    (∀ i : Fin (k+2),R.f (Q.v i.1)=railAtom (N+k) s.2.1 s.2.2 k i.1) := by
  let N := (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n
  have hfu (i : Fin (k+2)) : R.f (Q.u i.1)=railAtom N s.1.1 s.1.2 k i.1 := by
    by_cases hz : i.1=0
    · simpa only [hz,railAtom,ite_true] using hports.1
    · by_cases hi : i.1 ≤ k
      · rw [railAtom_interior N s.1.1 s.1.2 k i.1 (by omega) hi]
        exact (hlabels i.1 (by omega) hi).1
      · have he : i.1=k+1 := by omega
        simpa only [he,railAtom,show k+1 ≠ 0 by omega,
          show ¬k+1 ≤ k by omega,ite_false] using hports.2.2.1
  have hfv (i : Fin (k+2)) : R.f (Q.v i.1)=railAtom (N+k) s.2.1 s.2.2 k i.1 := by
    by_cases hz : i.1=0
    · simpa only [hz,railAtom,ite_true] using hports.2.1
    · by_cases hi : i.1 ≤ k
      · rw [railAtom_interior (N+k) s.2.1 s.2.2 k i.1 (by omega) hi]
        exact (hlabels i.1 (by omega) hi).2
      · have he : i.1=k+1 := by omega
        simpa only [he,railAtom,show k+1 ≠ 0 by omega,
          show ¬k+1 ≤ k by omega,ite_false] using hports.2.2.2
  exact ⟨hfu,hfv⟩

end WaveTurbulence.Vine
