/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
import Mathlib.Tactic

/-!
# Connectivity of molecules of irreducible gardens

TARGET `propcplmol` L1304–L1306. A molecular component determines a set
of whole nontrivial trees together with their trivial-tree partners. This
set is closed under leaf pairing, so irreducibility forces all atoms into
the component. Trivial trees are handled explicitly.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} {tree : Fin w → TTree}

theorem branches_same_tree_connected (G : Garden w) (a b : GBranch G.tree)
    (hi : a.1.1 = b.1.1) : G.molecule.SameComponent a b := by
  have hr : branchRoot a = branchRoot b := Subtype.ext (Prod.ext hi rfl)
  have ha := branch_connected_root G a
  rw [hr] at ha
  exact sameComponent_trans G.molecule ha (sameComponent_symm G.molecule (branch_connected_root G b))

theorem leaf_nonroot_of_branch_same_tree (c : GBranch tree) (l : GLeaf tree)
    (hi : l.1.1 = c.1.1) : l.1.2 ≠ [] := by
  intro hl
  have hr : ([] : Path) ∈ (tree c.1.1).branching := (branchRoot c).2
  have hleaf : ([] : Path) ∈ (tree c.1.1).leaves := by simpa only [hi,hl] using l.2
  exact TTree.not_mem_branching_of_mem_leaves _ hleaf hr

theorem leaf_eq_of_same_tree_root (l0 l : GLeaf tree) (hi : l.1.1 = l0.1.1)
    (h0 : l0.1.2 = []) : l = l0 := by
  have hr : ([] : Path) ∈ (tree l0.1.1).leaves := by simpa only [h0] using l0.2
  have ht : tree l0.1.1 = TTree.leaf := by
    cases he : tree l0.1.1 with
    | leaf => rfl
    | node x y z => simp only [he,TTree.leaves,Finset.mem_union,TTree.nil_notMem_pre,or_self] at hr
  have hl : l.1.2 = [] := by
    have hh : l.1.2 ∈ TTree.leaf.leaves := by simpa only [hi,ht] using l.2
    simpa only [TTree.leaves,Finset.mem_singleton] using hh
  exact Subtype.ext (Prod.ext hi (hl.trans h0.symm))

theorem paired_parents_adj (G : Garden w) (l : GLeaf G.tree) (hm : G.mark l = none)
    (hl : l.1.2 ≠ []) (hp : (G.pair l).1.2 ≠ []) :
    G.molecule.Adj (GNode.parent l.toNode hl) (GNode.parent (G.pair l).toNode hp) := by
  refine ⟨Sum.inr ⟨l,hm,hl,hp⟩,rfl,?_⟩
  rfl

/-- The actual molecule of a plain irreducible garden is connected,
including gardens with trivial trees. -/
theorem irreducible_garden_molecule_connected (G : Garden w) (hP : G.IsPlain)
    (hI : G.Irreducible) (a b : GBranch G.tree) : G.molecule.SameComponent a b := by
  classical
  by_contra hab
  let P (i : Fin w) : Prop :=
    (∃ c : GBranch G.tree, c.1.1 = i ∧ G.molecule.SameComponent a c) ∨
      ∃ l : GLeaf G.tree, l.1.1 = i ∧ l.1.2 = [] ∧
        ∃ hp : (G.pair l).1.2 ≠ [], G.molecule.SameComponent a (GNode.parent (G.pair l).toNode hp)
  let A := Finset.univ.filter P
  have haA : A.Nonempty := by
    refine ⟨a.1.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact Or.inl ⟨a,rfl,sameComponent_refl G.molecule a⟩
  have hbnot : ¬ P b.1.1 := by
    rintro (⟨c,hci,hac⟩ | ⟨l,hli,hl,_hp,_hc⟩)
    · exact hab (sameComponent_trans G.molecule hac (branches_same_tree_connected G c b hci))
    · exact leaf_nonroot_of_branch_same_tree b l hli hl
  have hproper : A ≠ Finset.univ := by
    intro he
    have hb : b.1.1 ∈ A := he.symm ▸ Finset.mem_univ b.1.1
    exact hbnot (Finset.mem_filter.mp hb).2
  have hclosedP (l : GLeaf G.tree) (hi : P l.1.1) : P (G.pair l).1.1 := by
    rcases hi with ⟨c,hci,hac⟩ | ⟨l0,hl0i,hroot,hp0,hcomp⟩
    · have hl : l.1.2 ≠ [] := leaf_nonroot_of_branch_same_tree c l hci.symm
      have hpar : G.molecule.SameComponent a (GNode.parent l.toNode hl) :=
        sameComponent_trans G.molecule hac (branches_same_tree_connected G c _ hci)
      by_cases hp : (G.pair l).1.2 = []
      · have hpp : (G.pair (G.pair l)).1.2 ≠ [] := by simpa only [G.pair_pair] using hl
        refine Or.inr ⟨G.pair l,rfl,hp,hpp,?_⟩
        simpa only [G.pair_pair] using hpar
      · exact Or.inl ⟨GNode.parent (G.pair l).toNode hp,rfl,
          sameComponent_trans G.molecule hpar (sameComponent_of_adj G.molecule (paired_parents_adj G l (hP l) hl hp))⟩
    · have he : l = l0 := leaf_eq_of_same_tree_root l0 l hl0i.symm hroot
      subst l
      exact Or.inl ⟨GNode.parent (G.pair l0).toNode hp0,rfl,hcomp⟩
  have hclosed : G.CompletelyPaired (G.leavesOf A) := by
    intro l hl
    have hi : P l.1.1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).2).2
    refine ⟨(fun he => ((G.pair_eq_iff l).1 he) (hP l)),?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hclosedP l hi⟩⟩
  exact hI A haA hproper hclosed

end WaveTurbulence.Mole
