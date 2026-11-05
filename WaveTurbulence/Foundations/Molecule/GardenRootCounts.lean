/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PortShim
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
import Mathlib.Tactic

/-!
# Root incidence counts and trivial-tree partners

TARGET `propcplmol` L1304–L1306: every tree has either a branching root
or a leaf root. In a positive-order irreducible plain garden, two trivial
tree roots cannot be paired to each other.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (tree : Fin w → TTree)

theorem card_root_branches :
    (Finset.univ.filter (fun c : GBranch tree => c.1.2 = [])).card =
      (Finset.univ.filter (fun i : Fin w => ([] : Path) ∈ (tree i).branching)).card := by
  apply Finset.card_bij (fun c _hc => c.1.1)
  · intro c hc
    have hp := (Finset.mem_filter.mp hc).2
    have hm := c.2
    rw [hp] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
  · intro c hc d hd he
    exact Subtype.ext (Prod.ext he ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm))
  · intro i hi
    refine ⟨⟨(i,[]),(Finset.mem_filter.mp hi).2⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩

theorem card_root_leaves :
    (Finset.univ.filter (fun l : GLeaf tree => l.1.2 = [])).card =
      (Finset.univ.filter (fun i : Fin w => ([] : Path) ∈ (tree i).leaves)).card := by
  apply Finset.card_bij (fun l _hl => l.1.1)
  · intro l hl
    have hp := (Finset.mem_filter.mp hl).2
    have hm := l.2
    rw [hp] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩
  · intro l hl m hm he
    exact Subtype.ext (Prod.ext he ((Finset.mem_filter.mp hl).2.trans (Finset.mem_filter.mp hm).2.symm))
  · intro i hi
    refine ⟨⟨(i,[]),(Finset.mem_filter.mp hi).2⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩

/-- Every tree contributes exactly one of the two kinds of root. -/
theorem card_root_branches_add_leaves :
    (Finset.univ.filter (fun c : GBranch tree => c.1.2 = [])).card+
      (Finset.univ.filter (fun l : GLeaf tree => l.1.2 = [])).card = w := by
  rw [card_root_branches,card_root_leaves]
  have hiff (i : Fin w) : ([] : Path) ∈ (tree i).leaves ↔ ¬ ([] : Path) ∈ (tree i).branching := by
    cases tree i <;> simp [TTree.leaves,TTree.branching,TTree.nil_notMem_pre]
  have he : (Finset.univ.filter (fun i : Fin w => ([] : Path) ∈ (tree i).leaves)) =
      Finset.univ.filter (fun i : Fin w => ¬ ([] : Path) ∈ (tree i).branching) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hiff]
  rw [he,Finset.card_filter_add_card_filter_not,Finset.card_univ,Fintype.card_fin]

/-- A pair of trivial roots would form an isolated two-tree subgarden;
irreducibility and a positive-order atom exclude it. -/
theorem irreducible_root_partner_nonroot (G : Garden w) (hP : G.IsPlain)
    (hI : G.Irreducible) (hn : 1 ≤ G.order) (l : GLeaf G.tree) (hl : l.1.2 = []) :
    (G.pair l).1.2 ≠ [] := by
  classical
  intro hp
  let A : Finset (Fin w) := {l.1.1,(G.pair l).1.1}
  have hclosed : G.CompletelyPaired (G.leavesOf A) := by
    intro m hm
    refine ⟨Garden.pair_ne_of_unmarked (hP m),?_⟩
    have hmA : m.1.1 = l.1.1 ∨ m.1.1 = (G.pair l).1.1 := by
      simpa only [Garden.leavesOf,A,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_insert,Finset.mem_singleton] using hm
    rcases hmA with hm0 | hm1
    · have he : m = l := leaf_eq_of_same_tree_root l m hm0 hl
      subst m
      simp [Garden.leavesOf,A]
    · have he : m = G.pair l := leaf_eq_of_same_tree_root (G.pair l) m hm1 hp
      subst m
      simp [Garden.leavesOf,A,G.pair_pair]
  have hAU : A = Finset.univ := by
    by_contra hproper
    exact hI A (by exact ⟨l.1.1,Finset.mem_insert_self _ _⟩) hproper hclosed
  obtain ⟨a,_ha⟩ := garden_atoms_nonempty G hn
  have haA : a.1.1 = l.1.1 ∨ a.1.1 = (G.pair l).1.1 := by
    have hh : a.1.1 ∈ A := hAU.symm ▸ Finset.mem_univ a.1.1
    simpa only [A,Finset.mem_insert,Finset.mem_singleton] using hh
  rcases haA with ha0 | ha1
  · exact leaf_nonroot_of_branch_same_tree a l ha0.symm hl
  · exact leaf_nonroot_of_branch_same_tree a (G.pair l) ha1.symm hp

end WaveTurbulence.Mole
