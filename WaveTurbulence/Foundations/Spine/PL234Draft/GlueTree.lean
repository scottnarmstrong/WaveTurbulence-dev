/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayerGate
public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-!
# Plugging a subtree at the lone position of a chain (tree level)

TARGET L1236–L1240 split a coherent regular chain into its same-layer blocks; the tree of the chain is
the tree of the top block with the rest plugged at its lone position. This file records how the node
sets of `X.plug ζ h` depend on `h`:

* `plug_mem_off`: off the lone subtree (`¬ X.lonePath <+: p`), membership of `p` in the nodes, leaves
  and branching nodes of `X.plug ζ h` does not depend on `h`;
* `plug_mem_on`: at `X.lonePath ++ q` it is membership of `q` in `h`;
* `plug_leaf_prefix`: in `X.plug ζ •`, the only node below the lone position is the lone leaf.
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg

theorem mem_node3_nodes (f : Fin 3 → TTree) (i : Fin 3) (s : Path) :
    (i :: s ∈ (node3 f).nodes ↔ s ∈ (f i).nodes) ∧
    (i :: s ∈ (node3 f).leaves ↔ s ∈ (f i).leaves) ∧
    (i :: s ∈ (node3 f).branching ↔ s ∈ (f i).branching) := by
  have e : ![f 0, f 1, f 2] i = f i := by fin_cases i <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · show i :: s ∈ (TTree.node (f 0) (f 1) (f 2)).nodes ↔ _
    rw [cons_mem_nodes_node, e]
  · show i :: s ∈ (TTree.node (f 0) (f 1) (f 2)).leaves ↔ _
    rw [cons_mem_leaves_node, e]
  · show i :: s ∈ (TTree.node (f 0) (f 1) (f 2)).branching ↔ _
    rw [cons_mem_branching_node, e]

theorem mem_node3_nil (f : Fin 3 → TTree) :
    ([] : Path) ∈ (node3 f).nodes ∧ ([] : Path) ∉ (node3 f).leaves ∧ ([] : Path) ∈ (node3 f).branching := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [node3, TTree.nodes, TTree.leaves, TTree.branching, TTree.pre]

/-- **At the lone position the plugged subtree is read.** -/
theorem plug_mem_on (X : RegChain) (ζ : ℤˣ) (h : TTree) (q : Path) :
    (X.lonePath ++ q ∈ (X.plug ζ h).nodes ↔ q ∈ h.nodes) ∧
    (X.lonePath ++ q ∈ (X.plug ζ h).leaves ↔ q ∈ h.leaves) ∧
    (X.lonePath ++ q ∈ (X.plug ζ h).branching ↔ q ∈ h.branching) := by
  have := mem_subtreeAt (X.plug ζ h) X.lonePath (lonePath_mem_plug X ζ h) q
  rw [Links.plug_subtreeAt_lonePath] at this
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

/-- **Off the lone subtree the plugged subtree is invisible.** -/
theorem plug_mem_off (X : RegChain) (ζ : ℤˣ) (h h' : TTree) (p : Path)
    (hp : ¬ X.lonePath <+: p) :
    (p ∈ (X.plug ζ h).nodes ↔ p ∈ (X.plug ζ h').nodes) ∧
    (p ∈ (X.plug ζ h).leaves ↔ p ∈ (X.plug ζ h').leaves) ∧
    (p ∈ (X.plug ζ h).branching ↔ p ∈ (X.plug ζ h').branching) := by
  cases X with
  | nil => exact absurd (List.nil_prefix) hp
  | pair m Qr Qg inner rest =>
    simp only [RegChain.lonePath] at hp
    cases p with
    | nil =>
      simp only [RegChain.plug]
      have h1 := mem_node3_nil (fun i => if i = m.c then
          inner.plug (slotSign ζ m.c) (node3 fun k =>
            if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
            else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
            else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
        else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
        else treeOfSign Qg.trees (slotSign ζ i))
      have h2 := mem_node3_nil (fun i => if i = m.c then
          inner.plug (slotSign ζ m.c) (node3 fun k =>
            if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h'
            else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
            else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
        else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
        else treeOfSign Qg.trees (slotSign ζ i))
      exact ⟨iff_of_true h1.1 h2.1, iff_of_false h1.2.1 h2.2.1, iff_of_true h1.2.2 h2.2.2⟩
    | cons i p' =>
      simp only [RegChain.plug]
      rw [(mem_node3_nodes _ i p').1, (mem_node3_nodes _ i p').1, (mem_node3_nodes _ i p').2.1,
        (mem_node3_nodes _ i p').2.1, (mem_node3_nodes _ i p').2.2, (mem_node3_nodes _ i p').2.2]
      by_cases hi : i = m.c
      · subst hi
        simp only [ite_true]
        have hp' : ¬ (inner.lonePath ++ [m.lone] ++ rest.lonePath) <+: p' := by
          intro hpre
          apply hp
          have : [m.c] ++ inner.lonePath ++ [m.lone] ++ rest.lonePath =
              m.c :: (inner.lonePath ++ [m.lone] ++ rest.lonePath) := by simp
          rw [this]
          exact (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩)
        by_cases hin : inner.lonePath <+: p'
        · obtain ⟨p'', rfl⟩ := hin
          rw [(plug_mem_on _ _ _ p'').1, (plug_mem_on _ _ _ p'').1, (plug_mem_on _ _ _ p'').2.1,
            (plug_mem_on _ _ _ p'').2.1, (plug_mem_on _ _ _ p'').2.2, (plug_mem_on _ _ _ p'').2.2]
          have hp'' : ¬ (m.lone :: rest.lonePath) <+: p'' := by
            intro hpre
            apply hp'
            rw [List.append_assoc]
            exact List.prefix_append_right_inj inner.lonePath |>.mpr (by simpa using hpre)
          cases p'' with
          | nil =>
            have h1 := mem_node3_nil (fun k =>
              if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
              else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
              else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
            have h2 := mem_node3_nil (fun k =>
              if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h'
              else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
              else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
            exact ⟨iff_of_true h1.1 h2.1, iff_of_false h1.2.1 h2.2.1, iff_of_true h1.2.2 h2.2.2⟩
          | cons k p''' =>
            rw [(mem_node3_nodes _ k p''').1, (mem_node3_nodes _ k p''').1,
              (mem_node3_nodes _ k p''').2.1, (mem_node3_nodes _ k p''').2.1,
              (mem_node3_nodes _ k p''').2.2, (mem_node3_nodes _ k p''').2.2]
            by_cases hk : k = m.lone
            · subst hk
              simp only [ite_true]
              have hr : ¬ rest.lonePath <+: p''' := fun hpre =>
                hp'' (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩)
              exact plug_mem_off rest _ h h' p''' hr
            · simp only [hk, ite_false]
              exact ⟨trivial, trivial, trivial⟩
        · exact plug_mem_off inner _ _ _ p' hin
      · simp only [hi, ite_false]
        exact ⟨trivial, trivial, trivial⟩
termination_by structural X

/-- In `X.plug ζ •`, a node below the lone position is the lone leaf. -/
theorem plug_leaf_prefix (X : RegChain) (ζ : ℤˣ) {p : Path} (hp : p ∈ (X.plug ζ .leaf).nodes)
    (hpre : X.lonePath <+: p) : p = X.lonePath := by
  obtain ⟨q, rfl⟩ := hpre
  have := (plug_mem_on X ζ .leaf q).1.mp hp
  simp [TTree.nodes] at this
  simp [this]

theorem lonePath_mem_leaves (X : RegChain) (ζ : ℤˣ) :
    X.lonePath ∈ (X.plug ζ .leaf).leaves := by
  have := (plug_mem_on X ζ .leaf []).2.1
  simp only [List.append_nil] at this
  exact this.mpr (by simp [TTree.leaves])

end WaveTurbulence.PL234
