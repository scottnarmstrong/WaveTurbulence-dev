/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33Topology
public import WaveTurbulence.Foundations.FinalCount.AppBS33SwapBoundary
import Mathlib.Tactic

/-! # Interchanging the two residual components before the source label test -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset

def s33ComponentPermutation : Equiv.Perm ℕ :=
  (Equiv.swap 1 2).trans ((Equiv.swap 3 6).trans (Equiv.swap 4 5))

theorem s33ComponentPermutation_mem : ∀ a ∈ AppbPatternKind.s33.pattern.vertices,
    s33ComponentPermutation a ∈ AppbPatternKind.s33.pattern.vertices := by decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def swapS33Components {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : AppbRealization M AppbPatternKind.s33.pattern := by
  let σ := s33ComponentPermutation
  let v' := fun j => r.vertex (σ j)
  have hY : AppbPatternKind.s33.pattern.removed.image v' = r.removedAtoms := by
    change ({1,2} : Finset ℕ).image v' = ({1,2} : Finset ℕ).image r.vertex
    simp only [image_insert,image_singleton]
    change ({r.vertex 2,r.vertex 1} : Finset V) = {r.vertex 1,r.vertex 2}
    exact pair_comm _ _
  let τ : Equiv.Perm (Fin 5) := (Equiv.swap 1 4).trans (Equiv.swap 2 3)
  let e : Fin 5 ≃ {x // x ∈ appbRemovedBonds M (AppbPatternKind.s33.pattern.removed.image v')} := τ.trans (r.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]; rfl)))
  exact {
    vertex := v'
    vertex_injective := by
      intro a ha b hb he
      exact σ.injective (r.vertex_injective (s33ComponentPermutation_mem a ha) (s33ComponentPermutation_mem b hb) he)
    vertex_mem := fun a ha => r.vertex_mem _ (s33ComponentPermutation_mem a ha)
    edge := e
    endpoints := by
      intro i
      change M.ends (r.edge (τ i)).val =
        s(r.vertex (σ (AppbPatternKind.s33.pattern.edges[i].1)),r.vertex (σ (AppbPatternKind.s33.pattern.edges[i].2)))
      have he := r.endpoints (τ i)
      rw [he]
      fin_cases i <;> first | rfl | exact Sym2.eq_swap }

theorem swapS33Components_removed {M : Molecule V D} (r : AppbRealization M AppbPatternKind.s33.pattern) :
    (swapS33Components r).removedAtoms = r.removedAtoms := by
  change ({1,2} : Finset ℕ).image (fun j => r.vertex (s33ComponentPermutation j)) =
    ({1,2} : Finset ℕ).image r.vertex
  simp only [image_insert,image_singleton]
  exact pair_comm _ _

theorem swapS33Components_vertex {M : Molecule V D} (r : AppbRealization M AppbPatternKind.s33.pattern)
    (a : ℕ) : (swapS33Components r).vertex a = r.vertex (s33ComponentPermutation a) := rfl

theorem swapS33Components_sameComponent {M : Molecule V D} (r : AppbRealization M AppbPatternKind.s33.pattern)
    (a b : V) : (swapS33Components r).post.SameComponent a b ↔ r.post.SameComponent a b := by
  change (Degen.eraseAtoms M (swapS33Components r).removedAtoms).SameComponent a b ↔
    (Degen.eraseAtoms M r.removedAtoms).SameComponent a b
  rw [swapS33Components_removed]

theorem oppositeFrom_swap_iff (M : Molecule V D) (a b : V) (x y : D) :
    AppbOppositeFrom M a b x y ↔ AppbOppositeFrom M b a y x := by
  by_cases hx : M.atom x = a <;> by_cases hy : M.atom y = b
  all_goals simp [AppbOppositeFrom,hx,hy]

theorem twoComponents_swap (M : Molecule V D) {a b : V} (h : TwoComponents M M.atoms a b) :
    TwoComponents M M.atoms b a := by
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  refine ⟨W,U,(union_comm _ _).trans hcover,hdis.symm,hW,hU,hb,ha,?_⟩
  intro w hw u hu hp
  exact hno u hu w hw (adj_symmetric M hp)



/-- A component partition is independent of its chosen representatives. -/
theorem twoComponents_representatives (M : Molecule V D) {a b c d : V}
    (h : TwoComponents M M.atoms a b) (hac : M.SameComponent a c)
    (hbd : M.SameComponent b d) : TwoComponents M M.atoms c d := by
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  have hc : c ∈ U := (partition_path_side M hcover hno (appb_induced_atoms_path M hac)).mp ha
  have hdU : d ∉ U := by
    intro hd
    have hbU := (partition_path_side M hcover hno (appb_induced_atoms_path M hbd)).mpr hd
    exact disjoint_left.mp hdis hbU hb
  have hdM : d ∈ M.atoms := (sameComponent_mem_iff M hbd).mp (hcover ▸ mem_union_right _ hb)
  exact ⟨U,W,hcover,hdis,hU,hW,hc,((mem_union.mp (hcover.symm ▸ hdM)).resolve_left hdU),hno⟩

/-- The source's choice of the defective residual pair is a literal figure
permutation, before partitioning decoration label tests. -/
theorem swapS33Components_geometry {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (h : AppbS33SplitGeometry M r) :
    AppbS33SplitGeometry M (swapS33Components r) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change TwoComponents (Degen.eraseAtoms M (swapS33Components r).removedAtoms)
      (Degen.eraseAtoms M (swapS33Components r).removedAtoms).atoms (r.vertex 6) (r.vertex 5)
    rw [swapS33Components_removed]
    exact twoComponents_representatives r.post (twoComponents_swap r.post h.1) h.2.2.1 h.2.1
  · change (swapS33Components r).post.SameComponent (r.vertex 6) (r.vertex 4)
    exact (swapS33Components_sameComponent r _ _).mpr h.2.2.1.symm
  · change (swapS33Components r).post.SameComponent (r.vertex 5) (r.vertex 3)
    exact (swapS33Components_sameComponent r _ _).mpr h.2.1.symm
  · change AppbOppositeFrom M (r.vertex 2) (r.vertex 1) (r.edge (4 : Fin 5)).val (r.edge (2 : Fin 5)).val
    exact (oppositeFrom_swap_iff M _ _ _ _).mp h.2.2.2.2
  · change AppbOppositeFrom M (r.vertex 2) (r.vertex 1) (r.edge (3 : Fin 5)).val (r.edge (1 : Fin 5)).val
    exact (oppositeFrom_swap_iff M _ _ _ _).mp h.2.2.2.1

/-- Source rule two can choose the defective residual pair without an
unproved symmetry convention. The resulting realization deletes exactly
the same atoms; subsequent label tests are made on this chosen figure. -/
theorem exists_s33_left_defective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    (hd : ¬∀ a ∈ AppbPatternKind.s33.pattern.vertices,
      a ∉ AppbPatternKind.s33.pattern.removed → M.deg (r.vertex a) = 4) :
    ∃ t : AppbRealization M AppbPatternKind.s33.pattern,
      t.removedAtoms = r.removedAtoms ∧ AppbS33SplitGeometry M t ∧
      ¬(M.deg (t.vertex 3) = 4 ∧ M.deg (t.vertex 5) = 4) := by
  classical
  by_cases h35 : M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4
  · refine ⟨swapS33Components r,swapS33Components_removed r,swapS33Components_geometry r hg,?_⟩
    change ¬(M.deg (r.vertex 6) = 4 ∧ M.deg (r.vertex 4) = 4)
    intro h64
    apply hd
    intro a ha hka
    have hh : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
      have hV : AppbPatternKind.s33.pattern.vertices = ({1,2,3,4,5,6} : Finset ℕ) := by decide
      rw [hV] at ha
      change a ∉ ({1,2} : Finset ℕ) at hka
      simp only [mem_insert,mem_singleton] at ha hka
      rcases ha with h | h | h | h | h | h
      · exact False.elim (hka (Or.inl h))
      · exact False.elim (hka (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    rcases hh with rfl | rfl | rfl | rfl
    · exact h35.1
    · exact h64.2
    · exact h35.2
    · exact h64.1
  · exact ⟨r,rfl,hg,h35⟩

end WaveTurbulence.Mole.AppbAlgorithm
