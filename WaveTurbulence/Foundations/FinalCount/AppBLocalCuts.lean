/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBoundaryCounts
import Mathlib.Tactic

/-! # Actual cuts computed from the Appendix B incidence tables -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Number of figure bonds crossing a concrete old vertex cut S. -/
def cutCount (S : Finset V) : ℕ :=
  ∑ i : Fin P.edges.length, if
    (r.vertex P.edges[i].1 ∈ S ∧ r.vertex P.edges[i].2 ∉ S) ∨
    (r.vertex P.edges[i].1 ∉ S ∧ r.vertex P.edges[i].2 ∈ S) then 1 else 0

/-- If the cut crosses only listed bonds, its full ambient boundary is
computed by the actual incidence table. -/
theorem cutCount_eq_boundary (S : Finset V)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms) :
    (Degen.boundaryDarts M S).card = r.cutCount S := by
  classical
  rw [appb_boundary_card]
  let cross : D → Prop := fun x =>
    (M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) ∨ (M.atom x ∉ S ∧ M.atom (M.mate x) ∈ S)
  have hf : appbCrossingBonds M S = (appbRemovedBonds M r.removedAtoms).filter cross := by
    ext x
    constructor
    · intro hx
      exact mem_filter.mpr ⟨hcross hx,(mem_filter.mp hx).2⟩
    · intro hx
      obtain ⟨hx,hp⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp hx).1,hp⟩
  have hs : (filter cross (appbRemovedBonds M r.removedAtoms)).card =
      ∑ x ∈ appbRemovedBonds M r.removedAtoms, if cross x then (1 : ℕ) else 0 :=
    (sum_boole (R := ℕ) cross _).symm
  rw [hf,hs,← r.removedBond_sum]
  unfold cutCount
  apply sum_congr rfl
  intro i _
  have he := r.endpoints i
  unfold Molecule.ends at he
  rcases Sym2.eq_iff.mp he with h | h
  · simp only [cross,h.1,h.2]
  · apply if_congr
    · simp only [cross,h.1,h.2]
      tauto
    · rfl
    · rfl

/-- Every boundary of an actual residual component crosses a removed bond. -/
theorem residual_cut_crossing (v : V) :
    appbCrossingBonds M (Degen.residualComponent M r.removedAtoms v) ⊆
      appbRemovedBonds M r.removedAtoms := by
  intro x hx
  obtain ⟨hxout,hcross⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨hxout,?_⟩
  rcases hcross with h | h
  · have hd : x ∈ Degen.boundaryDarts M (Degen.residualComponent M r.removedAtoms v) :=
      mem_filter.mpr ⟨mem_univ _,h⟩
    exact Or.inr (Degen.residual_boundary_ends_in_removed M r.removedAtoms v hd)
  · have hd : M.mate x ∈ Degen.boundaryDarts M (Degen.residualComponent M r.removedAtoms v) :=
      mem_filter.mpr ⟨mem_univ _,by simpa only [M.mate_mate] using And.intro h.2 h.1⟩
    have he := Degen.residual_boundary_ends_in_removed M r.removedAtoms v hd
    exact Or.inl (by simpa only [M.mate_mate] using he)

/-- Adding deleted vertices to such a side still crosses only listed bonds. -/
theorem union_removed_cut_crossing (S T : Finset V) (hT : T ⊆ r.removedAtoms)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms) :
    appbCrossingBonds M (S ∪ T) ⊆ appbRemovedBonds M r.removedAtoms := by
  intro x hx
  obtain ⟨hxout,hcut⟩ := mem_filter.mp hx
  by_cases hdel : M.atom x ∈ r.removedAtoms ∨ M.atom (M.mate x) ∈ r.removedAtoms
  · exact mem_filter.mpr ⟨hxout,hdel⟩
  · have ha : M.atom x ∉ T := fun h => hdel (Or.inl (hT h))
    have hb : M.atom (M.mate x) ∉ T := fun h => hdel (Or.inr (hT h))
    apply hcross
    apply mem_filter.mpr
    refine ⟨hxout,?_⟩
    simpa only [mem_union,ha,hb,or_false] using hcut

/-- A source bridgeless graph rules out every locally computed cut of size
one, including a residual component with a deleted atom reattached. -/
theorem cutCount_ne_one (S : Finset V)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) : r.cutCount S ≠ 1 := by
  intro h
  have hc : (Degen.boundaryDarts M S).card = 1 := (r.cutCount_eq_boundary S hcross).trans h
  obtain ⟨e,he⟩ := card_eq_one.mp hc
  exact hbridge e (Degen.isBridge_of_single_boundary M S he)

end AppbRealization
end WaveTurbulence.Mole
