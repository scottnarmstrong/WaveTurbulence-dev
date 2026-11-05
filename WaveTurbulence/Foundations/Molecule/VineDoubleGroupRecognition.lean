/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizedSlot
public import WaveTurbulence.Foundations.Molecule.VineActualCorePairCounts
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # Actual doubled pairs are contained in one source coherence group -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two actual atoms occur in a common literal group of this realization. -/
@[expose] def SameRealizedGroup {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (u v : V) : Prop :=
  ∃ g ∈ (X.expand R.k).groups,R.f u ∈ g ∧ R.f v ∈ g

/-- Every doubled pair incident to a fresh atom is its allocated rung. -/
theorem VineRealization.fresh_double_same_group (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hu : u ∈ S) (hf : X.template.n ≤ R.f u) (T : TwoIncidences M u v) :
    SameRealizedGroup R u v := by
  obtain ⟨A,i,hi,hin,he⟩ := R.fresh_slot hu hf
  rcases he with rfl | rfl
  · have hv := A.Q.upper_double_neighbor M hM A.frame.upper_injective i hi hin T
    subst v
    exact ⟨_,A.rung_group i hi hin,by simp⟩
  · have hv := A.Q.lower_double_neighbor M hM A.frame.lower_injective i hi hin T
    subst v
    exact ⟨_,A.rung_group i hi hin,by simp⟩

/-- Intrinsic nonjoint doubled pairs belong to one group for every possible
realization of the same actual vine. -/
theorem VineRealization.double_same_group (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b u v : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (hu : u ∈ S) (hv : v ∈ S)
    (hua : u ≠ a) (hub : u ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (huv : u ≠ v) (T : TwoIncidences M u v) : SameRealizedGroup R u v := by
  by_cases huo : R.f u<X.template.n
  · by_cases hvo : R.f v<X.template.n
    · have hu2 : 2 ≤ R.f u := by
        have hh := realization_index_lt_two_iff R hB hu
        have : ¬R.f u<2 := fun h => (hh.mp h).elim hua hub
        omega
      have hv2 : 2 ≤ R.f v := by
        have hh := realization_index_lt_two_iff R hB hv
        have : ¬R.f v<2 := fun h => (hh.mp h).elim hva hvb
        omega
      obtain ⟨q,hq⟩ := R.old_double_same_group M hu hv huv hu2 hv2 huo hvo T
      exact ⟨_,template_group_mem_expand X R.k (List.getElem_mem q.2),hq⟩
    · obtain ⟨g,hg,hv,hu⟩ := R.fresh_double_same_group M hM hv (by omega) T.mates
      exact ⟨g,hg,hu,hv⟩
  · exact R.fresh_double_same_group M hM hu (by omega) T

end WaveTurbulence.Vine
