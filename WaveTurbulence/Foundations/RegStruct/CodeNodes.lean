/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.LeafAddresses
public import WaveTurbulence.Foundations.RegStruct.RelocationGeometry

/-! # Actual node occurrences represented by regular-object codes

A chain represents its spine and side couples. Its terminal hole belongs to
the inserted terminal couple, so an empty chain represents no nodes by itself.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- The literal node addresses below one global root. -/
def nodeAddresses {w : ℕ} (t : TTree) (a : Fin w × Path) : Finset (Fin w × Path) :=
  t.nodes.image (addrExt a)

@[simp] theorem nodeAddresses_leaf {w : ℕ} (a : Fin w × Path) : nodeAddresses .leaf a = {a} := by
  simp [nodeAddresses,TTree.nodes,addrExt]

/-- Node addresses split into the root and the three child subtrees. -/
theorem nodeAddresses_node {w : ℕ} (l m r : TTree) (a : Fin w × Path) :
    nodeAddresses (.node l m r) a =
      {a} ∪ nodeAddresses l (addrExt a [0]) ∪ nodeAddresses m (addrExt a [1]) ∪
        nodeAddresses r (addrExt a [2]) := by
  simp only [nodeAddresses,TTree.nodes,Finset.image_insert,Finset.image_union,TTree.pre,
    Finset.image_image,Function.comp_def]
  have h0 : (fun p => addrExt a ((0 : Fin 3) :: p)) = addrExt (addrExt a [0]) :=
    funext (addrExt_cons a 0)
  have h1 : (fun p => addrExt a ((1 : Fin 3) :: p)) = addrExt (addrExt a [1]) :=
    funext (addrExt_cons a 1)
  have h2 : (fun p => addrExt a ((2 : Fin 3) :: p)) = addrExt (addrExt a [2]) :=
    funext (addrExt_cons a 2)
  rw [h0,h1,h2]
  simp only [addrExt,List.append_nil,Prod.eta,Finset.insert_eq]
  ac_rfl

mutual
/-- Nodes of both rooted trees, classified by the structure-code positions. -/
def coupleNodes {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) → Finset (Fin w × Path)
  | .triv, a, b => {a,b}
  | .type1 c r g d, a, b =>
    {a,b} ∪ coupleNodes r (addrExt a [0]) (addrExt b [c.partner 0]) ∪
      coupleNodes g (addrExt b [1]) (addrExt a [1]) ∪
      coupleNodes d (addrExt a [2]) (addrExt b [c.partner 2])
  | .type2 p m q, a, b =>
    chainNodes p 1 a ∪ chainNodes m (-1) b ∪
      coupleNodes q (addrExt a p.lonePath) (addrExt b m.lonePath)

/-- Nodes of a chain spine and its side couples, excluding the unfilled terminal hole. -/
def chainNodes {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) → Finset (Fin w × Path)
  | .nil, _, _ => ∅
  | .pair m r g i s, ζ, a =>
    {a,addrExt a ([m.c] ++ i.lonePath)} ∪
      (if slotSign ζ m.red.1 = 1 then
        coupleNodes r (addrExt a [m.red.1]) (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
      else coupleNodes r (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∪
      (if slotSign ζ m.green.1 = 1 then
        coupleNodes g (addrExt a [m.green.1]) (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
      else coupleNodes g (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∪
      chainNodes i (slotSign ζ m.c) (addrExt a [m.c]) ∪
      chainNodes s (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))
end

mutual
/-- The code occurrence set is exactly the actual node set of its two trees. -/
theorem couple_nodeAddresses {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    nodeAddresses Q.trees.1 a ∪ nodeAddresses Q.trees.2 b = coupleNodes Q a b := by
  cases Q with
  | triv => simp [RegCpl.trees,coupleNodes]
  | type1 c r g d =>
    rw [coupleNodes,← couple_nodeAddresses r,← couple_nodeAddresses g,← couple_nodeAddresses d]
    fin_cases c <;> simp [RegCpl.trees,MiniCplCode.partner,nodeAddresses_node] <;> simp only [Finset.insert_eq] <;> ac_rfl
  | type2 p m q =>
    rw [RegCpl.trees,chain_nodeAddresses p,chain_nodeAddresses m,coupleNodes,← couple_nodeAddresses q]
    ac_rfl
termination_by structural Q

/-- Filling a chain's hole adds precisely the node set of the inserted subtree. -/
theorem chain_nodeAddresses {w : ℕ} (X : RegChain) (ζ : ℤˣ) (h : TTree) (a : Fin w × Path) :
    nodeAddresses (X.plug ζ h) a = chainNodes X ζ a ∪ nodeAddresses h (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [RegChain.plug,RegChain.lonePath,chainNodes,addrExt]
  | pair m r g i s =>
    have hr := couple_nodeAddresses r
      (if slotSign ζ m.red.1 = 1 then addrExt a [m.red.1]
       else addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
      (if slotSign ζ m.red.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])
       else addrExt a [m.red.1])
    have hg := couple_nodeAddresses g
      (if slotSign ζ m.green.1 = 1 then addrExt a [m.green.1]
       else addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
      (if slotSign ζ m.green.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])
       else addrExt a [m.green.1])
    obtain ⟨c,b⟩ := m
    rcases Int.units_eq_one_or ζ with hz | hz <;> subst ζ
    all_goals
      fin_cases c <;> fin_cases b
      all_goals
        simp [MiniTreeCode.red,MiniTreeCode.green,slotSign] at hr hg
        simp [RegChain.plug,RegChain.lonePath,chainNodes,node3,MiniTreeCode.lone,
          MiniTreeCode.red,MiniTreeCode.green,slotSign,treeOfSign,nodeAddresses_node,
          chain_nodeAddresses i,chain_nodeAddresses s,← hr,← hg,addrExt_append,List.append_assoc]
        simp only [Finset.insert_eq]
        ac_rfl
termination_by structural X
end

/-- Each couple root is an actual represented node. -/
theorem coupleNodes_left_mem {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    a ∈ coupleNodes Q a b := by
  rw [← couple_nodeAddresses]
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨[],TTree.nil_mem_nodes _,by simp [addrExt]⟩

theorem coupleNodes_right_mem {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    b ∈ coupleNodes Q a b := by
  rw [← couple_nodeAddresses]
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨[],TTree.nil_mem_nodes _,by simp [addrExt]⟩

/-- Every code occurrence is genuinely below one of the code's two roots. -/
theorem coupleNodes_below {w : ℕ} (Q : RegCpl) (a b z : Fin w × Path)
    (hz : z ∈ coupleNodes Q a b) : Below a z ∨ Below b z := by
  rw [← couple_nodeAddresses] at hz
  rcases Finset.mem_union.mp hz with ha | hb
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact Or.inl (below_extend a p)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact Or.inr (below_extend b p)

/-- Every represented chain node lies below the chain's global root. -/
theorem chainNodes_below {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path)
    (hz : z ∈ chainNodes X ζ a) : Below a z := by
  have hh : z ∈ nodeAddresses (X.plug ζ .leaf) a := by
    rw [chain_nodeAddresses]
    exact Finset.mem_union_left _ hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
  exact below_extend a p

end WaveTurbulence.Reg
