/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeDecorations
import Mathlib.Tactic

/-! # Conservation on atomic subsets (TARGET defdecmol, subsetvc)

All internal bonds cancel as pairs of actual darts, including loops.
-/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [AddCommGroup E] [Module ℝ E] (M : Molecule V D)

/-- The darts leaving an atomic set, retaining both directions via dartSign. -/
@[expose] def boundary (S : Finset V) : Finset D :=
  univ.filter fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S

/-- Internal bonds cancel even when the surrounding molecule is larger. -/
theorem sum_internal_eq_zero (S : Finset V) (k : D → E)
    (hk : ∀ x, k (M.mate x)=k x) :
    ∑ x ∈ univ.filter (M.InGroup S), M.dartSign x • k x = 0 := by
  apply Finset.sum_involution (fun x _ => M.mate x)
  · intro x _hx
    rw [hk x,Mole.dartSign_mate,neg_smul,add_neg_cancel]
  · intro x _hx _hne
    exact M.mate_ne x
  · intro x hx
    simp only [mem_filter,mem_univ,true_and,Molecule.InGroup] at hx
    simp only [mem_filter,mem_univ,true_and,Molecule.InGroup,M.mate_mate]
    exact hx.symm
  · intro x _hx
    exact M.mate_mate x

/-- Summed local conservation is exactly the signed boundary flow. -/
theorem sum_conservation_boundary (S : Finset V) (k : D → E) (c : V → E)
    (hk : ∀ x, k (M.mate x)=k x)
    (hc : ∀ v ∈ S, ∑ x ∈ M.dartsAt v, M.dartSign x • k x = c v) :
    ∑ v ∈ S, c v = ∑ x ∈ boundary M S, M.dartSign x • k x := by
  have hsplit :
      ∑ x ∈ univ.filter (fun x => M.atom x ∈ S), M.dartSign x • k x =
        ∑ x ∈ univ.filter (M.InGroup S), M.dartSign x • k x +
          ∑ x ∈ boundary M S, M.dartSign x • k x := by
    have hh := Finset.sum_filter_add_sum_filter_not
      (univ.filter fun x => M.atom x ∈ S) (fun x => M.atom (M.mate x) ∈ S)
      (fun x => M.dartSign x • k x)
    change _ = (∑ x ∈ univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S), _) + _
    simpa only [filter_filter,and_assoc,boundary] using hh.symm
  rw [sum_internal_eq_zero M S k hk,zero_add] at hsplit
  rw [← hsplit]
  calc
    _ = ∑ v ∈ S, ∑ x ∈ M.dartsAt v, M.dartSign x • k x :=
      Finset.sum_congr rfl (fun v hv => (hc v hv).symm)
    _ = _ := by
      simp only [Molecule.dartsAt]
      exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _

/-- An atomic set with zero local sources has zero total boundary flow under conservation. -/
theorem boundary_eq_zero (S : Finset V) (k : D → E)
    (hk : ∀ x, k (M.mate x)=k x)
    (hc : ∀ v ∈ S, ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0) :
    ∑ x ∈ boundary M S, M.dartSign x • k x = 0 := by
  rw [← sum_conservation_boundary M S k (fun _ => 0) hk hc]
  exact Finset.sum_const_zero

end WaveTurbulence.Vine
