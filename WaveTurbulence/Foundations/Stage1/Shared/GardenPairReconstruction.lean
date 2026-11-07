/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenRootEncoding
import Mathlib.Tactic

/-! # Reconstructing actual leaf pairs, including roots of trivial trees -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {V D : Type*} {G H : Garden w} {M : Molecule V D}

/-- Root records for a trivial tree explicitly record its unique partner. -/
theorem encodeRoot_of_leaf (f : GardenMoleculeIso G M) (l : GLeaf G.tree) (hr : l.1.2 = []) :
    encodeRoot G M f l.1.1 =
      if hp : (G.pair l).1.2 = [] then .inr (.inr (G.pair l).1.1)
      else .inr (.inl (f.branches (GNode.parent (G.pair l).toNode hp),(G.pair l).1.2.getLast hp)) := by
  rcases l with ⟨⟨i,p⟩,hl⟩
  change p = [] at hr
  subst p
  have hb : [] ∉ (G.tree i).branching := TTree.not_mem_branching_of_mem_leaves _ hl
  simp only [encodeRoot,hb,↓reduceDIte]

/-- A nonbranching root record can only come from a trivial tree. -/
theorem encodeRoot_inr_implies_leaf (f : GardenMoleculeIso G M) (i : Fin w)
    (r : (M.atoms × Fin 3) ⊕ Fin w) (hr : encodeRoot G M f i = .inr r) :
    [] ∈ (G.tree i).leaves := by
  have hb : [] ∉ (G.tree i).branching := by
    intro hb
    have he := (encodeRoot_inl_iff G M f i (f.branches ⟨(i,[]),hb⟩)).mpr
      ⟨⟨(i,[]),hb⟩,rfl,rfl⟩
    rw [he] at hr
    cases hr
  exact ((TTree.mem_nodes_iff _ _).mp (TTree.nil_mem_nodes _)).resolve_right hb

/-- The encoded isomorphism preserves the coordinates of every child slot. -/
theorem GardenEncodedIso.child_addresses (f : GardenEncodedIso G H)
    (hroot : ∀ v : GBranch G.tree, v.1.2 = [] → (f.branches v).1.1 = v.1.1)
    (v : GBranch G.tree) (i : Fin 3) : ((f.branches v).child i).1 = (v.child i).1 :=
  congrArg (fun p : Fin w × Path => (p.1,p.2++[i])) (f.branch_addresses hroot v)

/-- Position codes recover every LP pair whose two leaves are nonroot. -/
theorem GardenEncodedIso.nonroot_leaf_pair (f : GardenEncodedIso G H)
    (hroot : ∀ v : GBranch G.tree, v.1.2 = [] → (f.branches v).1.1 = v.1.1)
    (hP : G.IsPlain) (l : GLeaf G.tree) (hl : l.1.2 ≠ []) (hp : (G.pair l).1.2 ≠ []) :
    ∃ m : GLeaf H.tree, m.1 = l.1 ∧ (H.pair m).1 = (G.pair l).1 := by
  let x : GardenDart G := .inr ⟨l,hP l,hl,hp⟩
  have hx : dartPosition H (f.darts x) = (l.1.2.getLast hl).succ := f.position_comm x
  have hm : dartPosition H (H.molecule.mate (f.darts x)) = ((G.pair l).1.2.getLast hp).succ := by
    rw [f.mate_comm,f.position_comm]
    rfl
  obtain ⟨m,hm1,hm2⟩ := positions_recovers_leaf_pair H (f.darts x) _ _ hx hm
  have ha : H.molecule.atom (f.darts x) = f.branches (GNode.parent l.toNode hl) := f.atom_comm x
  have hb : H.molecule.atom (H.molecule.mate (f.darts x)) =
      f.branches (GNode.parent (G.pair l).toNode hp) := by
    rw [f.mate_comm,f.atom_comm]
    rfl
  have hchild1 := f.child_addresses hroot (GNode.parent l.toNode hl) (l.1.2.getLast hl)
  have hchild2 := f.child_addresses hroot (GNode.parent (G.pair l).toNode hp) ((G.pair l).1.2.getLast hp)
  have hv1 := congrArg (fun a : GNode H.tree => a.1) hm1
  have hv2 := congrArg (fun a : GNode H.tree => a.1) hm2
  rw [ha] at hv1
  rw [hb] at hv2
  refine ⟨m,hv1.trans (hchild1.trans ?_),hv2.trans (hchild2.trans ?_)⟩
  · exact congrArg (fun a : GNode G.tree => a.1) (parent_child_eq_node l.toNode hl)
  · exact congrArg (fun a : GNode G.tree => a.1) (parent_child_eq_node (G.pair l).toNode hp)

/-- Root records recover every pair incident to a trivial root, including
the pairs of two trivial roots invisible in the molecule. -/
theorem root_record_recovers_pair (f : GardenMoleculeIso G M) (g : GardenMoleculeIso H M)
    (hc : encodePositions G M f = encodePositions H M g)
    (hr : encodeRoot G M f = encodeRoot H M g) (l : GLeaf G.tree) (hl : l.1.2 = []) :
    ∃ m : GLeaf H.tree, m.1 = l.1 ∧ (H.pair m).1 = (G.pair l).1 := by
  let F := isoOfCodes G M f g hc
  have hroot := roots_determine_order G M f g hc hr
  have heG := encodeRoot_of_leaf f l hl
  rw [hr] at heG
  by_cases hp : (G.pair l).1.2 = []
  · rw [dite_eq_left hp] at heG
    have hmleaf := encodeRoot_inr_implies_leaf g l.1.1 (.inr (G.pair l).1.1) heG
    let m : GLeaf H.tree := ⟨(l.1.1,[]),hmleaf⟩
    refine ⟨m,Prod.ext rfl hl.symm,?_⟩
    have heH := encodeRoot_of_leaf g m rfl
    change encodeRoot H M g l.1.1 = _ at heH
    rw [heH] at heG
    split at heG
    · rename_i hmroot
      have hi := Sum.inr.inj (Sum.inr.inj heG)
      exact Prod.ext hi (hmroot.trans hp.symm)
    · cases Sum.inr.inj heG
  · rw [dite_eq_right hp] at heG
    have hmleaf := encodeRoot_inr_implies_leaf g l.1.1
      (.inl (f.branches (GNode.parent (G.pair l).toNode hp),(G.pair l).1.2.getLast hp)) heG
    let m : GLeaf H.tree := ⟨(l.1.1,[]),hmleaf⟩
    refine ⟨m,Prod.ext rfl hl.symm,?_⟩
    have heH := encodeRoot_of_leaf g m rfl
    change encodeRoot H M g l.1.1 = _ at heH
    rw [heH] at heG
    split at heG
    · cases Sum.inr.inj heG
    · rename_i hmnonroot
      have he := Sum.inl.inj (Sum.inr.inj heG)
      have hbranches := congrArg Prod.fst he
      have hlast := congrArg Prod.snd he
      dsimp only [Prod.fst] at hbranches
      dsimp only [Prod.snd] at hlast
      let p := GNode.parent (G.pair l).toNode hp
      let q := GNode.parent (H.pair m).toNode hmnonroot
      have hF : F.branches p = q := by
        change g.branches.symm (f.branches p) = q
        simpa only [Equiv.symm_apply_apply] using (congrArg g.branches.symm hbranches).symm
      have hpq : q.1 = p.1 := by
        rw [← hF]
        exact F.branch_addresses hroot p
      have hchild : (q.child ((H.pair m).1.2.getLast hmnonroot)).1 =
          (p.child ((G.pair l).1.2.getLast hp)).1 := by
        change (q.1.1,q.1.2++[(H.pair m).1.2.getLast hmnonroot]) =
          (p.1.1,p.1.2++[(G.pair l).1.2.getLast hp])
        rw [hpq]
        exact congrArg (fun i => (p.1.1,p.1.2++[i])) hlast
      exact (congrArg (fun a : GNode H.tree => a.1)
        (parent_child_eq_node (H.pair m).toNode hmnonroot)).symm.trans
          (hchild.trans (congrArg (fun a : GNode G.tree => a.1)
            (parent_child_eq_node (G.pair l).toNode hp)))

end WaveTurbulence.Mole
