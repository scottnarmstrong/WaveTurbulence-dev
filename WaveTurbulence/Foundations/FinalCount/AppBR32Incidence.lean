/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32CutPair
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceCounts
import Mathlib.Tactic

/-! # Exact direct/indirect incidence alternatives at the chosen special atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_r3_edge_ends {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (j : Fin 3) :
    M.ends (r.edge j).val = s(r.vertex 1,r.vertex (2+j.val)) := by
  fin_cases j
  all_goals exact r.endpoints _

theorem appb_r3_incidence_le_one {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (a : V) (ha : a ∈ r.post.atoms) (j : Fin 3) :
    appbIncidence M a (r.edge j).val ≤ 1 := by
  have hn : r.vertex 1 ≠ a := by
    intro he
    exact (mem_sdiff.mp ha).2 (he ▸ mem_image_of_mem _ (show 1 ∈ AppbPatternKind.r3.pattern.removed by decide))
  rcases Sym2.eq_iff.mp (appb_r3_edge_ends r j) with h | h
  all_goals simp only [appbIncidence,h.1,h.2,hn,ite_false,zero_add,add_zero]
  all_goals split_ifs <;> decide

theorem appb_r32_other_star_not_crossing {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (S : Finset V) (j i : Fin 3)
    (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val}) (hne : i ≠ j) :
    (r.edge i).val ∉ appbCrossingBonds M S := by
  intro hx
  rw [hcross] at hx
  rcases mem_insert.mp hx with he | he
  · exact hne (r.edge.injective (Subtype.ext he))
  · have hdel := (mem_filter.mp (r.edge i).property).2
    rw [mem_singleton.mp he] at hdel
    exact hdel.elim (s.edge ⟨0,by decide⟩).val.property.1 (s.edge ⟨0,by decide⟩).val.property.2

theorem appb_r3_incidence_zero_of_not_crossing {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern) (S : Finset V) (hS : S ⊆ r.post.atoms)
    (a : V) (ha : a ∈ S) (i : Fin 3) (hn : (r.edge i).val ∉ appbCrossingBonds M S) :
    appbIncidence M a (r.edge i).val = 0 := by
  have hv : r.vertex 1 ∉ S := by
    intro h
    exact (mem_sdiff.mp (hS h)).2 (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.r3.pattern.removed by decide))
  have hsame : M.atom (r.edge i).val ∈ S ↔ M.atom (M.mate (r.edge i).val) ∈ S := by
    by_contra h
    apply hn
    exact mem_filter.mpr ⟨(mem_filter.mp (r.edge i).property).1,by tauto⟩
  have hvne : r.vertex 1 ≠ a := fun he => hv (he.symm ▸ ha)
  rcases Sym2.eq_iff.mp (appb_r3_edge_ends r i) with h | h
  · rw [h.1,h.2] at hsame
    have hnother : r.vertex (2+i.val) ∉ S := fun h => hv (hsame.mpr h)
    have hneother : r.vertex (2+i.val) ≠ a := fun he => hnother (he.symm ▸ ha)
    simp only [appbIncidence,h.1,h.2,hvne,hneother,ite_false,zero_add]
  · rw [h.1,h.2] at hsame
    have hnother : r.vertex (2+i.val) ∉ S := fun h => hv (hsame.mp h)
    have hneother : r.vertex (2+i.val) ≠ a := fun he => hnother (he.symm ▸ ha)
    simp only [appbIncidence,h.1,h.2,hvne,hneother,ite_false,zero_add]

theorem appb_r32_all_star_incidence_zero {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (S : Finset V) (hS : S ⊆ r.post.atoms)
    (j : Fin 3) (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val})
    (a : V) (ha : a ∈ S) (hj : appbIncidence M a (r.edge j).val = 0) :
    ∀ i : Fin 3,appbIncidence M a (r.edge i).val = 0 := by
  intro i
  by_cases hi : i = j
  · exact hi.symm ▸ hj
  · exact appb_r3_incidence_zero_of_not_crossing r S hS a ha i
      (appb_r32_other_star_not_crossing r s S j i hcross hi)

end WaveTurbulence.Mole
