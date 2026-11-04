/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeNodes
public import WaveTurbulence.Foundations.RegStruct.DecodedLeaves
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts

/-! # A chain's represented nodes exclude its terminal hole and its descendants

The node-count bound is proved directly from the code. Combined with the exact
node-set identity, it separates the chain from the subtree occupying its hole.
-/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Prefixing node addresses preserves their cardinality. -/
theorem nodeAddresses_card {w : ℕ} (t : TTree) (a : Fin w × Path) :
    (nodeAddresses t a).card = 3 * t.order + 1 := by
  have hi : Function.Injective (addrExt a) := by
    intro p q h
    have hp := congrArg Prod.snd h
    exact List.append_cancel_left hp
  rw [nodeAddresses,Finset.card_image_of_injective _ hi,Comb.card_nodes]

/-- Two rooted trees represent at most three times their order plus two nodes. -/
theorem coupleNodes_card_le {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    (coupleNodes Q a b).card ≤ 3 * Q.size + 2 := by
  have hc := Finset.card_union_le (nodeAddresses Q.trees.1 a) (nodeAddresses Q.trees.2 b)
  rw [couple_nodeAddresses,nodeAddresses_card,nodeAddresses_card] at hc
  have ho := code_trees_order Q
  omega

/-- A chain represents at most three nodes per branching node, excluding its hole. -/
theorem chainNodes_card_le {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (chainNodes X ζ a).card ≤ 3 * X.size := by
  cases X with
  | nil => simp [chainNodes,RegChain.size]
  | pair m r g i s =>
    let roots : Finset (Fin w × Path) := {a,addrExt a ([m.c] ++ i.lonePath)}
    let red : Finset (Fin w × Path) := if slotSign ζ m.red.1 = 1 then
      coupleNodes r (addrExt a [m.red.1]) (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
      else coupleNodes r (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
    let green : Finset (Fin w × Path) := if slotSign ζ m.green.1 = 1 then
      coupleNodes g (addrExt a [m.green.1]) (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
      else coupleNodes g (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
    let inner := chainNodes i (slotSign ζ m.c) (addrExt a [m.c])
    let rest := chainNodes s (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))
    have hr : roots.card ≤ 2 := by
      simpa only [roots,Finset.card_singleton] using
        (Finset.card_insert_le a ({addrExt a ([m.c] ++ i.lonePath)} : Finset (Fin w × Path)))
    have hred : red.card ≤ 3 * r.size + 2 := by
      dsimp only [red]
      split_ifs <;> exact coupleNodes_card_le _ _ _
    have hgreen : green.card ≤ 3 * g.size + 2 := by
      dsimp only [green]
      split_ifs <;> exact coupleNodes_card_le _ _ _
    have hi := chainNodes_card_le i (slotSign ζ m.c) (addrExt a [m.c])
    have hs := chainNodes_card_le s (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))
    have h1 := Finset.card_union_le roots red
    have h2 := Finset.card_union_le (roots ∪ red) green
    have h3 := Finset.card_union_le ((roots ∪ red) ∪ green) inner
    have h4 := Finset.card_union_le (((roots ∪ red) ∪ green) ∪ inner) rest
    change ((((roots ∪ red) ∪ green) ∪ inner) ∪ rest).card ≤ _
    simp only [RegChain.size]
    change inner.card ≤ _ at hi
    change rest.card ≤ _ at hs
    omega
termination_by structural X

/-- The terminal hole is not one of the chain's represented nodes. -/
theorem chainNodes_no_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    addrExt a X.lonePath ∉ chainNodes X ζ a := by
  intro h
  have he := chain_nodeAddresses X ζ .leaf a
  rw [nodeAddresses_leaf,Finset.union_singleton,Finset.insert_eq_of_mem h] at he
  have hc := congrArg Finset.card he
  rw [nodeAddresses_card,code_plug_order,TTree.order,Nat.add_zero] at hc
  have hb := chainNodes_card_le X ζ a
  omega

/-- The terminal path is an actual leaf in the chain with a trivial filling. -/
theorem chain_lone_mem_leaves (X : RegChain) (ζ : ℤˣ) :
    X.lonePath ∈ (X.plug ζ .leaf).leaves := by
  have hh : ((0 : Fin 1),X.lonePath) ∈ leafAddresses (X.plug ζ .leaf) (0,[]) := by
    rw [chain_leafAddresses,leafAddresses_leaf]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hh
  have heP : p = X.lonePath := by
    simpa only [addrExt,List.nil_append] using congrArg Prod.snd he
  simpa only [heP] using hp

/-- A leaf cannot have a strict descendant that is a node. -/
theorem leaf_prefix_node_eq {t : TTree} {p q : Path}
    (hp : p ∈ t.leaves) (hq : q ∈ t.nodes) (hpq : p <+: q) : p = q := by
  obtain ⟨r,hr⟩ := hpq
  cases r with
  | nil => simpa only [List.append_nil] using hr
  | cons i r =>
    have hchild : p ++ [i] ∈ t.nodes := by
      refine Comb.TreePath.mem_nodes_of_prefix t (q := q) hq ⟨r,?_⟩
      simpa only [List.append_assoc,List.singleton_append] using hr
    exact (Comb.TreePath.not_mem_branching_of_mem_leaves t hp
      (Comb.TreePath.branching_of_append_mem t hchild)).elim

/-- No represented chain node is at or below the terminal hole. -/
theorem chainNodes_not_below_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path)
    (hz : z ∈ chainNodes X ζ a) : ¬ Below (addrExt a X.lonePath) z := by
  intro hb
  have hactual : z ∈ nodeAddresses (X.plug ζ .leaf) a := by
    rw [chain_nodeAddresses]
    exact Finset.mem_union_left _ hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hactual
  have hprefix := hb.2
  change a.2 ++ X.lonePath <+: a.2 ++ p at hprefix
  have hlocal := (List.prefix_append_right_inj a.2).mp hprefix
  have he := leaf_prefix_node_eq (chain_lone_mem_leaves X ζ) hp hlocal
  rw [← he] at hz
  exact chainNodes_no_lone X ζ a hz

end WaveTurbulence.Reg
