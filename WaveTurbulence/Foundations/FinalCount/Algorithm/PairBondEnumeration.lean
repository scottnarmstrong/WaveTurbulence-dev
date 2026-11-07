/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.StarMultiplicity
import Mathlib.Tactic

/-! # Enumerating parallel bonds and the remaining single boundary at an atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def parallelBonds (M : Molecule V D) (a b : V) : Finset D :=
  M.bonds.filter fun x => M.ends x = s(a,b)

theorem parallelBonds_subset_incident (M : Molecule V D) (a b : V) :
    parallelBonds M a b ⊆ appbRemovedBonds M {a} := by
  classical
  intro x hx
  obtain ⟨hx,he⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨hx,?_⟩
  simp only [mem_singleton]
  rcases Sym2.eq_iff.mp he with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

noncomputable def parallelBondEnumeration (M : Molecule V D) {a b : V} {n : ℕ}
    (h : M.bondsBetween a b = n) : Fin n ≃ {x // x ∈ parallelBonds M a b} :=
  (equivFinOfCardEq h).symm

/-- A degree n+1 atom with n bonds to b has exactly one remaining bond. -/
theorem unique_boundary_bond (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} {n : ℕ} (hd : M.deg a = n+1) (hm : M.bondsBetween a b = n) :
    ∃ x, appbRemovedBonds M {a} \ parallelBonds M a b = {x} := by
  classical
  apply card_eq_one.mp
  rw [card_sdiff_of_subset (parallelBonds_subset_incident M a b),
    incident_card_eq_degree M hno,hd]
  change n+1-M.bondsBetween a b = 1
  rw [hm]
  omega

/-- The actual remaining edge ends at a third atom, not a or b. -/
theorem exists_boundary_neighbor (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} {n : ℕ} (hd : M.deg a = n+1) (hm : M.bondsBetween a b = n) :
    ∃ x ∈ M.bonds, ∃ c ∈ M.atoms,
      c ≠ a ∧ c ≠ b ∧ M.ends x = s(a,c) := by
  classical
  obtain ⟨x,hx⟩ := unique_boundary_bond M hno hd hm
  have hxm : x ∈ appbRemovedBonds M {a} \ parallelBonds M a b := by
    rw [hx]; exact mem_singleton_self _
  obtain ⟨hi,hnot⟩ := mem_sdiff.mp hxm
  let st := starOfDegree M hno a (n+1) hd
  let i := st.edge.symm ⟨x,hi⟩
  have he : (st.edge i).val = x := congrArg Subtype.val (st.edge.apply_symm_apply ⟨x,hi⟩)
  have hend : M.ends x = s(a,st.neighbor i) := by rw [← he]; exact st.endpoints i
  refine ⟨x,(mem_filter.mp hi).1,st.neighbor i,st.neighbor_mem i,st.neighbor_ne i,?_,hend⟩
  intro hb
  apply hnot
  exact mem_filter.mpr ⟨(mem_filter.mp hi).1,by simpa only [hb] using hend⟩

end WaveTurbulence.Mole.AppbAlgorithm
