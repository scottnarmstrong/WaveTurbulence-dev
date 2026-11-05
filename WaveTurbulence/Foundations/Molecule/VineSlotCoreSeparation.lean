/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotFullDistinct
public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
import Mathlib.Tactic

/-! # Old atoms outside a slot differ from every actual rail atom -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Literal labels separate an old core atom from both complete slot rails,
including their old endpoints. This uses only the allocation convention. -/
theorem VineRealization.core_outside_slot_rails {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (Q : FullRungSequence M k)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1))
    (j : Fin X.template.n)
    (hj : j.1 ≠ s.1.1 ∧ j.1 ≠ s.1.2 ∧ j.1 ≠ s.2.1 ∧ j.1 ≠ s.2.2) :
    ∀ i,i ≤ k+1 → (R.coreAtom j).1 ≠ Q.u i ∧ (R.coreAtom j).1 ≠ Q.v i := by
  have hn : X.template.n ≤ (pre.foldl
      (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]
    omega
  intro i hi
  have hne : j.1 ≠ R.f (Q.u i) ∧ j.1 ≠ R.f (Q.v i) := by
    by_cases hz : i=0
    · subst i
      rw [hports.1,hports.2.1]
      exact ⟨hj.1,hj.2.2.1⟩
    · by_cases he : i=k+1
      · subst i
        rw [hports.2.2.1,hports.2.2.2]
        exact ⟨hj.2.1,hj.2.2.2⟩
      · obtain ⟨hu,hv⟩ := hlabels i (by omega) (by omega)
        rw [hu,hv]
        constructor <;> omega
  constructor
  · intro he
    apply hne.1
    exact (R.label_coreAtom j).symm.trans (congrArg R.f he)
  · intro he
    apply hne.2
    exact (R.label_coreAtom j).symm.trans (congrArg R.f he)

end WaveTurbulence.Vine
