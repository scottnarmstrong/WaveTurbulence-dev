/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineRailEndpointInjectivity
import Mathlib.Tactic

/-! # Actual slot sequences remain distinct when both old endpoint pairs are included -/

public section
namespace WaveTurbulence.Vine

/-- The four endpoints are distinct when the two final ports differ. -/
theorem template_slot_pair_distinct (X : VineType) : ∀ s ∈ X.template.slots, s.1.2 ≠ s.2.2 →
    s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2 ∧ s.1.1 ≠ s.2.1 ∧
      s.1.1 ≠ s.2.2 ∧ s.1.2 ≠ s.2.1 ∧ s.1.2 ≠ s.2.2 := by
  cases X <;> decide

/-- Each slot rail has different initial and final endpoints. Type II's
rails may share their final joint (F72). -/
theorem template_slot_edges_nonloop (X : VineType) : ∀ s ∈ X.template.slots,
    s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2 := by
  cases X <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The exact port and allocation formulas prove distinctness of every
old endpoint and inserted rung in a source slot, with no positivity restriction. -/
theorem VineRealization.slot_full_distinct {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hend : s.1.2 ≠ s.2.2)
    (Q : FullRungSequence M k)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1)) :
    Function.Injective (Sum.elim (fun i : Fin (k+2) => Q.u i.1)
      (fun i : Fin (k+2) => Q.v i.1)) := by
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
  obtain ⟨hab,hcd,hac,had,hbc,hbd⟩ := template_slot_pair_distinct X s hslot hend
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
  have hd := railAtom_full_pair_injective N s.1.1 s.1.2 s.2.1 s.2.2 k
    (by omega) (by omega) (by omega) (by omega) hab hcd hac had hbc hbd
  intro i j he
  apply hd
  have hh := congrArg R.f he
  cases i <;> cases j <;> simpa only [Sum.elim_inl,Sum.elim_inr,hfu,hfv] using hh

end WaveTurbulence.Vine
