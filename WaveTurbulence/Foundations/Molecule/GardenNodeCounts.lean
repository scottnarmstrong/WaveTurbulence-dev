/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeConnectivity
import Mathlib.Tactic

/-!
# Exact garden node and molecule atom counts

TARGET `propcplmol` L1304–L1306 and tree definition L630. Structural
counting lemmas are adapted from the checked COMB-CORE source API, against
the pinned B1 snapshot-5 carrier.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

private theorem card_pre (i : Fin 3) (S : Finset Path) : (pre i S).card = S.card :=
  Finset.card_image_of_injective _ List.cons_injective

private theorem pre_disjoint {i j : Fin 3} (hij : i ≠ j) (S T : Finset Path) :
    Disjoint (pre i S) (pre j T) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨q,_hq,rfl⟩ := TTree.mem_pre.mp hp
  exact hij (TTree.cons_mem_pre.mp hq).1.symm

/-- A ternary tree of order n has 2n+1 leaves. -/
theorem tree_card_leaves : ∀ t : TTree, t.leaves.card = 2*t.order+1
  | .leaf => rfl
  | .node l m r => by
    rw [leaves,Finset.card_union_of_disjoint,Finset.card_union_of_disjoint,
      card_pre,card_pre,card_pre,tree_card_leaves l,tree_card_leaves m,tree_card_leaves r,order]
    · ring
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.mpr ⟨pre_disjoint (by decide) _ _,pre_disjoint (by decide) _ _⟩

theorem mem_forestSet {w : ℕ} (tree : Fin w → TTree) (f : TTree → Finset Path) (a : Fin w × Path) :
    a ∈ forestSet tree f ↔ a.2 ∈ f (tree a.1) := by
  simp only [forestSet,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and]
  constructor
  · rintro ⟨i,p,hp,rfl⟩
    exact hp
  · intro ha
    exact ⟨a.1,a.2,ha,rfl⟩

theorem card_forestSet {w : ℕ} (tree : Fin w → TTree) (f : TTree → Finset Path) :
    (forestSet tree f).card = ∑ j, (f (tree j)).card := by
  rw [forestSet,Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun j _ => Finset.card_image_of_injective _ (Prod.mk_right_injective j))
  · intro i _hi j _hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q,_hq,h⟩ := Finset.mem_image.mp hb
    exact hij (congrArg Prod.fst h).symm

/-- The branching-node count is the actual garden order. -/
theorem card_gbranch {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GBranch tree) = ∑ j, (tree j).order := by
  have hc : Fintype.card (GBranch tree) = (forestSet tree TTree.branching).card :=
    @Fintype.card_of_subtype (Fin w × Path) (fun a => a.2 ∈ (tree a.1).branching)
    (forestSet tree TTree.branching) (fun a => mem_forestSet tree TTree.branching a)
    (inferInstanceAs (Fintype (GBranch tree)))
  rw [hc,card_forestSet]
  exact Finset.sum_congr rfl (fun j _ => TTree.card_branching_eq _)

/-- The leaf count in a width-w garden is 2n+w. -/
theorem card_gleaf {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GLeaf tree) = 2*(∑ j, (tree j).order)+w := by
  have hc : Fintype.card (GLeaf tree) = (forestSet tree TTree.leaves).card :=
    @Fintype.card_of_subtype (Fin w × Path) (fun a => a.2 ∈ (tree a.1).leaves)
    (forestSet tree TTree.leaves) (fun a => mem_forestSet tree TTree.leaves a)
    (inferInstanceAs (Fintype (GLeaf tree)))
  rw [hc,card_forestSet]
  simp only [tree_card_leaves,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

/-- TARGET `propcplmol`: the actual garden molecule has n atoms. -/
theorem garden_card_atoms {w : ℕ} (G : Garden w) : G.molecule.atoms.card = G.order := by
  rw [show G.molecule.atoms = Finset.univ by rfl,Finset.card_univ,card_gbranch]
  rfl

/-- Positive garden order supplies an actual molecule atom. -/
theorem garden_atoms_nonempty {w : ℕ} (G : Garden w) (hn : 1 ≤ G.order) : G.molecule.atoms.Nonempty := by
  apply Finset.card_pos.mp
  rw [garden_card_atoms]
  omega

/-- The component count in the irreducible source case is exactly one. -/
theorem irreducible_garden_numComponents {w : ℕ} (G : Garden w) (hP : G.IsPlain)
    (hI : G.Irreducible) (hn : 1 ≤ G.order) : G.molecule.numComponents = 1 := by
  exact numComponents_eq_one G.molecule (garden_atoms_nonempty G hn)
    (fun a _ha b _hb => irreducible_garden_molecule_connected G hP hI a b)

end WaveTurbulence.Mole
