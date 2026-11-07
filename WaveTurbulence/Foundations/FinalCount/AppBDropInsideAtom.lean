/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFrameIncidentBonds
public import WaveTurbulence.Foundations.FinalCount.AppBBoundaryCounts
import Mathlib.Tactic

/-! # The three-bond cut obtained by removing the inside special atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_drop_inside_atom_crossing (M : Molecule V D) (S : Finset V) (a c o : V)
    (x bridge d1 d2 : D) (ha : a ∈ S) (hc : c ∈ S) (ho : o ∉ S) (hca : c ≠ a)
    (hcross : appbCrossingBonds M S = {x,bridge})
    (hincident : appbRemovedBonds M {a} = {bridge,d1,d2})
    (hbridge : M.ends bridge = s(a,o)) (hd1 : M.ends d1 = s(a,c)) (hd2 : M.ends d2 = s(a,c))
    (hx : appbIncidence M a x = 0) :
    appbCrossingBonds M (S \ {a}) = {x,d1,d2} := by
  classical
  let T := S \ {a}
  have haN : a ∉ T := fun h => (mem_sdiff.mp h).2 (mem_singleton_self a)
  have hoN : o ∉ T := fun h => ho (mem_sdiff.mp h).1
  have hcN : c ∈ T := mem_sdiff.mpr ⟨hc,by simpa only [mem_singleton] using hca⟩
  have hBnot : bridge ∉ appbCrossingBonds M T := by
    intro h
    have ht := (mem_filter.mp h).2
    rcases Sym2.eq_iff.mp hbridge with he | he
    all_goals simp only [he.1,he.2,haN,hoN,false_and,and_false,or_self] at ht
  have hD1 : d1 ∈ appbCrossingBonds M T := by
    have hm : d1 ∈ appbRemovedBonds M {a} := hincident.symm ▸ mem_insert_of_mem (mem_insert_self _ _)
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hm).1,?_⟩
    rcases Sym2.eq_iff.mp hd1 with he | he
    all_goals simp only [he.1,he.2,haN,hcN,not_false_eq_true,not_true_eq_false,true_and,false_and,and_true,and_false,true_or,or_true,false_or,or_false]
  have hD2 : d2 ∈ appbCrossingBonds M T := by
    have hm : d2 ∈ appbRemovedBonds M {a} := hincident.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hm).1,?_⟩
    rcases Sym2.eq_iff.mp hd2 with he | he
    all_goals simp only [he.1,he.2,haN,hcN,not_false_eq_true,not_true_eq_false,true_and,false_and,and_true,and_false,true_or,or_true,false_or,or_false]
  have hX : x ∈ appbCrossingBonds M T := by
    have hm : x ∈ appbCrossingBonds M S := hcross.symm ▸ mem_insert_self _ _
    have hn := (appb_incidence_zero_iff M a x).mp hx
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hm).1,?_⟩
    simpa only [T,mem_sdiff,mem_singleton,hn.1,hn.2,not_false_eq_true,and_true] using (mem_filter.mp hm).2
  ext y
  constructor
  · intro hy
    obtain ⟨hb,ht⟩ := mem_filter.mp hy
    have hcases :
        ((M.atom y ∈ S ∧ M.atom (M.mate y) ∉ S) ∨ (M.atom y ∉ S ∧ M.atom (M.mate y) ∈ S)) ∨
        (M.atom y = a ∨ M.atom (M.mate y) = a) := by
      simp only [mem_sdiff,mem_singleton] at ht
      tauto
    rcases hcases with h | h
    · have hm : y ∈ appbCrossingBonds M S := mem_filter.mpr ⟨hb,h⟩
      rw [hcross] at hm
      rcases mem_insert.mp hm with rfl | h
      · exact mem_insert_self _ _
      · have he := mem_singleton.mp h
        exact False.elim (hBnot (he ▸ hy))
    · have hm : y ∈ appbRemovedBonds M {a} := mem_filter.mpr ⟨hb,by simpa only [mem_singleton] using h⟩
      rw [hincident] at hm
      rcases mem_insert.mp hm with rfl | h
      · exact False.elim (hBnot hy)
      · rcases mem_insert.mp h with rfl | h
        · exact mem_insert_of_mem (mem_insert_self _ _)
        · have he := mem_singleton.mp h
          exact he.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  · intro hy
    rcases mem_insert.mp hy with rfl | h
    · exact hX
    · rcases mem_insert.mp h with rfl | h
      · exact hD1
      · exact (mem_singleton.mp h).symm ▸ hD2

end WaveTurbulence.Mole
