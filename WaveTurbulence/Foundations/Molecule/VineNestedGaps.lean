/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGapKinds
public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
import Mathlib.Tactic

/-! # Nested blocks sharing a joint have the same actual gap -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [AddCommGroup E] [Module ℝ E]

/-- Equal restricted degrees and nested atom sets give identical actual
internal dart sets at the specified atom. -/
theorem internal_darts_eq_of_nested_degree (M : Molecule V D) {A S : Finset V}
    (hAS : A ⊆ S) (v : V) (hd : M.degIn A v=M.degIn S v) :
    (M.dartsAt v).filter (M.InGroup A)=(M.dartsAt v).filter (M.InGroup S) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨hv,h1,h2⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hv,hAS h1,hAS h2⟩
  · exact hd.symm.le

/-- Nested blocks with the same joint carry exactly the same flow there.
This does not require an ambient conservation law. -/
theorem nested_block_gap_eq (M : Molecule V D) {A S : Finset V} {a b c : V}
    (hAS : A ⊆ S) (hA : M.IsBlock A a b) (hS : M.IsBlock S a c)
    (k : D → E) {r r' : E} (hr : IsGroupGap M A k a r)
    (hr' : IsGroupGap M S k a r') : r=r' := by
  classical
  have ha := (Mole.block_joint_degrees M hA).1
  have hs := (Mole.block_joint_degrees M hS).1
  rw [groupGap_eq_flow M ha hr,groupGap_eq_flow M hs hr']
  unfold groupFlow
  rw [internal_darts_eq_of_nested_degree M hAS a (ha.trans hs.symm)]

end WaveTurbulence.Vine
