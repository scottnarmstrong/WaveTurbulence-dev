/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel
import Mathlib.Tactic

/-!
# VINE-B: the geometry of one (CL) unit in the skeleton

For a (CL) block `u` of a garden (TARGET `block_clcn` (1)(a), L1349) with upper joint `a = u1` and lower joint `b = u2`,
the realization `G[B]` (`clRealizationNodes`, Remark `rem_realiz` L1377) is the set of descendants of `a` that are not
descendants of the three boundary nodes `u11 = a.child excluded`, `u21 = b.child positive`, `u22 = b.child negative`
(`CLRegionData.geometry`).  This file proves the order facts used by the splitting of decorations, times and slots:
* the boundary nodes are exactly the children of atoms of the unit that lie outside the realization (`ext_child`);
* a node of the realization other than `a` has its parent in the unit (`real_parent`), `a` has no parent in the unit;
* realizations of disjoint units meet only trivially (`real_disjoint`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

/-! ## Descendant order -/

theorem isDesc_child_iff {x : GNode S.tree} (v : GBranch S.tree) (i : Fin 3) :
    x.IsDesc (v.child i) ↔ x = v.child i ∨ x.IsDesc v.toNode := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases List.prefix_concat_iff.mp h2 with h | h
    · left; exact Subtype.ext (Prod.ext h1 h)
    · right; exact ⟨h1, h⟩
  · rintro (rfl | h)
    · exact GNode.isDesc_refl _
    · exact h.trans (GBranch.isDesc_child v i)

theorem child_inj {v v' : GBranch S.tree} {i i' : Fin 3} (h : v.child i = v'.child i') : v = v' ∧ i = i' := by
  have h1 := congrArg (fun x : GNode S.tree => x.1.1) h
  have h2 := congrArg (fun x : GNode S.tree => x.1.2) h
  simp only [GBranch.child] at h1 h2
  obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
  simp only [List.cons.injEq, and_true] at h4
  exact ⟨Subtype.ext (Prod.ext h1 h3), h4⟩

theorem child_ne_toNode (v : GBranch S.tree) (i : Fin 3) : ¬ (v.child i).IsDesc v.toNode := by
  rintro ⟨-, h⟩
  have := h.length_le
  simp [GBranch.child, GBranch.toNode] at this

theorem isDesc_antisymm' {x y : GNode S.tree} (h₁ : x.IsDesc y) (h₂ : y.IsDesc x) : x = y :=
  Subtype.ext (Prod.ext h₁.1 (h₁.2.eq_of_length (le_antisymm h₁.2.length_le h₂.2.length_le)))

theorem child_parent (x : GNode S.tree) (hn : x.1.2 ≠ []) :
    ∃ i, (x.parent hn).child i = x := by
  have hb : x.1.2 ∈ (S.tree x.1.1).nodes := x.2
  have e : x.1.2.dropLast ++ [x.1.2.getLast hn] = x.1.2 := List.dropLast_append_getLast hn
  exact ⟨x.1.2.getLast hn, Subtype.ext (Prod.ext rfl e)⟩

theorem parent_child (v : GBranch S.tree) (i : Fin 3) (hn : (v.child i).1.2 ≠ []) :
    (v.child i).parent hn = v := by
  apply Subtype.ext
  exact Prod.ext rfl (by simp [GBranch.child, GNode.parent])

theorem child_nonroot (v : GBranch S.tree) (i : Fin 3) : (v.child i).1.2 ≠ [] := by
  simp [GBranch.child]

/-! ## One unit -/

/-- The CL region data of a unit (TARGET `block_clcn` (1)(a)). -/
noncomputable def regionOf (u : CLBlock S) : CLRegionData S u.atoms u.upper u.lower :=
  clRegionData S u.isBlock u.cl

/-- The three boundary nodes `u11, u21, u22` of a unit. -/
def crownSet (u : CLBlock S) : Set (GNode S.tree) :=
  {x | x = u.upper.child (regionOf u).excluded ∨ x = u.lower.child (regionOf u).positive ∨
    x = u.lower.child (regionOf u).negative}

theorem real_iff (u : CLBlock S) (x : GNode S.tree) :
    x ∈ clRealizationNodes S u.atoms ↔
      u.upper.toNode.IsDesc x ∧ ¬ (u.upper.child (regionOf u).excluded).IsDesc x ∧
        ¬ (u.lower.child (regionOf u).positive).IsDesc x ∧ ¬ (u.lower.child (regionOf u).negative).IsDesc x :=
  (mem_clRealizationNodes x).trans ((((regionOf u).geometry u.isBlock).realization x))

theorem branch_real_iff (u : CLBlock S) (v : GBranch S.tree) :
    v.toNode ∈ clRealizationNodes S u.atoms ↔ v ∈ u.atoms :=
  branch_mem_clRealizationNodes v

theorem upper_mem (u : CLBlock S) : u.upper ∈ u.atoms := u.isBlock.2.1

theorem lower_mem (u : CLBlock S) : u.lower ∈ u.atoms := u.isBlock.2.2.1

theorem upper_real (u : CLBlock S) : u.upper.toNode ∈ clRealizationNodes S u.atoms :=
  (branch_real_iff u _).mpr (upper_mem u)

theorem lower_desc (u : CLBlock S) : u.upper.toNode.IsDesc u.lower.toNode :=
  ((real_iff u _).mp ((branch_real_iff u _).mpr (lower_mem u))).1

theorem real_desc (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ clRealizationNodes S u.atoms) :
    u.upper.toNode.IsDesc x := ((real_iff u x).mp hx).1

theorem real_tree (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ clRealizationNodes S u.atoms) :
    x.1.1 = u.upper.1.1 := (real_desc u hx).1.symm

theorem crown_not_real (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ crownSet u) :
    x ∉ clRealizationNodes S u.atoms := by
  intro h
  have h' := (real_iff u x).mp h
  rcases hx with rfl | rfl | rfl
  · exact h'.2.1 (GNode.isDesc_refl _)
  · exact h'.2.2.1 (GNode.isDesc_refl _)
  · exact h'.2.2.2 (GNode.isDesc_refl _)

/-- The parent of a realization node other than `a` lies in the unit. -/
theorem real_parent (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ clRealizationNodes S u.atoms)
    (hne : x ≠ u.upper.toNode) : ∃ hn : x.1.2 ≠ [], x.parent hn ∈ u.atoms :=
  cl_realization_parent u.isBlock (regionOf u) x hx hne

/-- **The external children of the unit's atoms are exactly the boundary nodes.** -/
theorem ext_child (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (i : Fin 3)
    (hx : v.child i ∉ clRealizationNodes S u.atoms) :
    (v = u.upper ∧ i = (regionOf u).excluded) ∨
      (v = u.lower ∧ (i = (regionOf u).positive ∨ i = (regionOf u).negative)) := by
  have hvr := (real_iff u v.toNode).mp ((branch_real_iff u v).mpr hv)
  rw [real_iff] at hx
  have ha : u.upper.toNode.IsDesc (v.child i) := hvr.1.trans (GBranch.isDesc_child v i)
  have key : ∀ (c : GBranch S.tree) (k : Fin 3), ¬ (c.child k).IsDesc v.toNode →
      (c.child k).IsDesc (v.child i) → c = v ∧ k = i := by
    intro c k hn hd
    rcases (isDesc_child_iff v i).mp hd with h | h
    · obtain ⟨h1, h2⟩ := child_inj h
      exact ⟨h1, h2⟩
    · exact (hn h).elim
  by_cases h1 : (u.upper.child (regionOf u).excluded).IsDesc (v.child i)
  · obtain ⟨rfl, rfl⟩ := key _ _ hvr.2.1 h1
    exact Or.inl ⟨rfl, rfl⟩
  by_cases h2 : (u.lower.child (regionOf u).positive).IsDesc (v.child i)
  · obtain ⟨rfl, rfl⟩ := key _ _ hvr.2.2.1 h2
    exact Or.inr ⟨rfl, Or.inl rfl⟩
  by_cases h3 : (u.lower.child (regionOf u).negative).IsDesc (v.child i)
  · obtain ⟨rfl, rfl⟩ := key _ _ hvr.2.2.2 h3
    exact Or.inr ⟨rfl, Or.inr rfl⟩
  exact (hx ⟨ha, h1, h2, h3⟩).elim

theorem ext_child_crown (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (i : Fin 3)
    (hx : v.child i ∉ clRealizationNodes S u.atoms) : v.child i ∈ crownSet u := by
  rcases ext_child u hv i hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The children of an atom other than the two joints are in the realization. -/
theorem interior_child (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (ha : v ≠ u.upper)
    (hb : v ≠ u.lower) (i : Fin 3) : v.child i ∈ clRealizationNodes S u.atoms := by
  by_contra hx
  rcases ext_child u hv i hx with ⟨h, -⟩ | ⟨h, -⟩
  · exact ha h
  · exact hb h

/-- An external child of an atom other than the upper joint is a child of the lower joint. -/
theorem ext_child_lower (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (ha : v ≠ u.upper) (i : Fin 3)
    (hx : v.child i ∉ clRealizationNodes S u.atoms) :
    v = u.lower ∧ (i = (regionOf u).positive ∨ i = (regionOf u).negative) := by
  rcases ext_child u hv i hx with ⟨h, -⟩ | h
  · exact (ha h).elim
  · exact h

/-- The parent of a boundary node is a joint of the unit. -/
theorem crown_parent (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ crownSet u) :
    ∃ v ∈ u.atoms, ∃ i, v.child i = x := by
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, upper_mem u, _, rfl⟩
  · exact ⟨_, lower_mem u, _, rfl⟩
  · exact ⟨_, lower_mem u, _, rfl⟩

theorem crown_desc (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ crownSet u) : u.upper.toNode.IsDesc x := by
  obtain ⟨v, hv, i, rfl⟩ := crown_parent u hx
  exact (real_desc u ((branch_real_iff u v).mpr hv)).trans (GBranch.isDesc_child v i)

theorem crown_ne_upper (u : CLBlock S) {x : GNode S.tree} (hx : x ∈ crownSet u) : x ≠ u.upper.toNode := by
  rintro rfl
  exact crown_not_real u hx (upper_real u)

theorem parent_isDesc (x : GNode S.tree) (hn : x.1.2 ≠ []) : (x.parent hn).toNode.IsDesc x :=
  ⟨rfl, List.dropLast_prefix _⟩

theorem not_isDesc_parent (x : GNode S.tree) (hn : x.1.2 ≠ []) : ¬ x.IsDesc (x.parent hn).toNode := by
  rintro ⟨-, h⟩
  have h1 := h.length_le
  have h2 : (x.parent hn).toNode.1.2 = x.1.2.dropLast := rfl
  rw [h2, List.length_dropLast] at h1
  have : x.1.2.length ≠ 0 := by simpa using hn
  omega

/-- The upper joint has no parent in the unit. -/
theorem upper_parent_not_mem (u : CLBlock S) (hn : u.upper.toNode.1.2 ≠ []) :
    u.upper.toNode.parent hn ∉ u.atoms := fun h =>
  not_isDesc_parent _ hn (real_desc u ((branch_real_iff u _).mpr h))

/-! ## Disjoint units -/

theorem real_disjoint {u u' : CLBlock S} (hd : Disjoint u.atoms u'.atoms) {x : GNode S.tree}
    (hx : x ∈ clRealizationNodes S u.atoms) (hx' : x ∈ clRealizationNodes S u'.atoms)
    (hne : x ≠ u.upper.toNode) : False := by
  obtain ⟨hn, hp⟩ := real_parent u hx hne
  by_cases he : x = u'.upper.toNode
  · subst he
    have hb : u'.upper ∈ u.atoms := by
      have := (real_iff u _).mp hx
      have hc : ∀ v : GBranch S.tree, v.toNode ∈ clRealizationNodes S u.atoms → v ∈ u.atoms :=
        fun v h => (branch_real_iff u v).mp h
      exact hc _ hx
    exact Finset.disjoint_left.mp hd hb (upper_mem u')
  · obtain ⟨hn', hp'⟩ := real_parent u' hx' he
    exact Finset.disjoint_left.mp hd hp hp'

/-- The upper joint of a unit is not in the realization of a disjoint unit. -/
theorem upper_not_real {u u' : CLBlock S} (hd : Disjoint u.atoms u'.atoms) :
    u.upper.toNode ∉ clRealizationNodes S u'.atoms := fun h =>
  Finset.disjoint_left.mp hd (upper_mem u) ((branch_real_iff u' _).mp h)

/-- A boundary node of a unit lies in the realization of a disjoint unit only as its upper joint. -/
theorem crown_real_other {u u' : CLBlock S} (hd : Disjoint u.atoms u'.atoms) {x : GNode S.tree}
    (hx : x ∈ crownSet u) (hx' : x ∈ clRealizationNodes S u'.atoms) : x = u'.upper.toNode := by
  by_contra hne
  obtain ⟨hn, hp⟩ := real_parent u' hx' hne
  obtain ⟨v, hv, i, rfl⟩ := crown_parent u hx
  rw [parent_child] at hp
  exact Finset.disjoint_left.mp hd hv hp

end WaveTurbulence.VineB
