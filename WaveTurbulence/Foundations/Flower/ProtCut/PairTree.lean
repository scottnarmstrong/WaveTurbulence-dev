/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Glue

/-! # D2c PROT-CUT: the tree of a closing chain pair

A closing pair is the chain code `Z = pair m Qr Qg inner nil` (o73 Prop 13.1: the partner `𝔫_a` of the terminal
node is the root, the terminal node `𝔫_b` sits at `bPath = [m.c] ++ inner.lonePath`). Its tree is
`pairTree m Qr Qg inner ζ`. This file locates the pieces inside it:
* the interior chain below `[m.c]` (off the interior lone path), `mem_pairTree_inner`;
* the three children of `𝔫_b` (`mem_pairTree_b`), the two top side trees (`mem_pairTree_top`);
* the two trees of each side couple at `rBase j`, `gBase j` (tree `0` = the `+` tree), `mem_pairTree_rBase`;
* the classification of all nodes, branching nodes and leaves (`pairTree_cases`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The path of the terminal node `𝔫_b` of a closing pair. -/
def bPath (m : MiniTreeCode) (inner : RegChain) : Path := [m.c] ++ inner.lonePath

/-- The lone position of a closing pair. -/
def lonePos (m : MiniTreeCode) (inner : RegChain) : Path := bPath m inner ++ [m.lone]

/-- The position of tree `j` of the red side couple (`0` = the `+` tree). -/
def rBase (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) : Path :=
  if (j = 0) = (slotSign ζ m.red.1 = 1) then [m.red.1] else bPath m inner ++ [m.red.2]

/-- The position of tree `j` of the green side couple. -/
def gBase (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) : Path :=
  if (j = 0) = (slotSign ζ m.green.1 = 1) then [m.green.1] else bPath m inner ++ [m.green.2]

/-- The subtree at `𝔫_b`. -/
def bTree (m : MiniTreeCode) (Qr Qg : RegCpl) (ζ' : ℤˣ) : TTree :=
  node3 fun k => if k = m.lone then .leaf else if k = m.red.2 then treeOfSign Qr.trees (slotSign ζ' k)
    else treeOfSign Qg.trees (slotSign ζ' k)

/-- The tree of a closing pair. -/
def pairTree (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ) : TTree :=
  (RegChain.pair m Qr Qg inner .nil).plug ζ .leaf

theorem pairTree_eq (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ) :
    pairTree m Qr Qg inner ζ = node3 fun i => if i = m.c then
      inner.plug (slotSign ζ m.c) (bTree m Qr Qg (slotSign ζ m.c))
      else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i) else treeOfSign Qg.trees (slotSign ζ i) := by
  unfold pairTree bTree
  simp only [RegChain.plug]

theorem slot_cases (m : MiniTreeCode) (i : Fin 3) : i = m.c ∨ i = m.red.1 ∨ i = m.green.1 := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> fin_cases i <;> simp [MiniTreeCode.red, MiniTreeCode.green]

theorem slot2_cases (m : MiniTreeCode) (k : Fin 3) : k = m.lone ∨ k = m.red.2 ∨ k = m.green.2 := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;> fin_cases k <;>
    simp [MiniTreeCode.red, MiniTreeCode.green, MiniTreeCode.lone]

variable (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (ζ : ℤˣ)

theorem mem_leaf_nodes (q : Path) : q ∈ TTree.leaf.nodes ↔ q = [] := by
  simp [TTree.nodes]

theorem mem_leaf_leaves (q : Path) : q ∈ TTree.leaf.leaves ↔ q = [] := by
  simp [TTree.leaves]

theorem not_mem_leaf_branching (q : Path) : q ∉ TTree.leaf.branching := by
  simp [TTree.branching]

/-- **The interior region.** -/
theorem mem_pairTree_inner (q : Path) (hq : ¬ inner.lonePath <+: q) :
    (m.c :: q ∈ (pairTree m Qr Qg inner ζ).nodes ↔ q ∈ (inner.plug (slotSign ζ m.c) .leaf).nodes) ∧
    (m.c :: q ∈ (pairTree m Qr Qg inner ζ).leaves ↔ q ∈ (inner.plug (slotSign ζ m.c) .leaf).leaves) ∧
    (m.c :: q ∈ (pairTree m Qr Qg inner ζ).branching ↔
      q ∈ (inner.plug (slotSign ζ m.c) .leaf).branching) := by
  rw [pairTree_eq, (mem_node3_nodes _ m.c q).1, (mem_node3_nodes _ m.c q).2.1,
    (mem_node3_nodes _ m.c q).2.2]
  simp only [ite_true]
  exact plug_mem_off inner _ _ _ q hq

/-- **Below `𝔫_b`.** -/
theorem mem_pairTree_b (k : Fin 3) (q : Path) :
    (bPath m inner ++ k :: q ∈ (pairTree m Qr Qg inner ζ).nodes ↔ q ∈ (if k = m.lone then TTree.leaf
      else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
      else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k)).nodes) ∧
    (bPath m inner ++ k :: q ∈ (pairTree m Qr Qg inner ζ).leaves ↔ q ∈ (if k = m.lone then TTree.leaf
      else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
      else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k)).leaves) ∧
    (bPath m inner ++ k :: q ∈ (pairTree m Qr Qg inner ζ).branching ↔ q ∈ (if k = m.lone then TTree.leaf
      else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
      else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k)).branching) := by
  have e : bPath m inner ++ k :: q = m.c :: (inner.lonePath ++ k :: q) := by
    simp [bPath]
  rw [e, pairTree_eq, (mem_node3_nodes _ m.c _).1, (mem_node3_nodes _ m.c _).2.1,
    (mem_node3_nodes _ m.c _).2.2]
  simp only [ite_true]
  rw [(plug_mem_on inner _ _ (k :: q)).1, (plug_mem_on inner _ _ (k :: q)).2.1,
    (plug_mem_on inner _ _ (k :: q)).2.2]
  unfold bTree
  exact mem_node3_nodes _ k q

theorem bPath_mem_branching : bPath m inner ∈ (pairTree m Qr Qg inner ζ).branching := by
  have e : bPath m inner = m.c :: (inner.lonePath ++ []) := by simp [bPath]
  rw [e, pairTree_eq, (mem_node3_nodes _ m.c _).2.2]
  simp only [ite_true]
  rw [(plug_mem_on inner _ _ []).2.2]
  exact (mem_node3_nil _).2.2

theorem nil_mem_pairTree_branching : ([] : Path) ∈ (pairTree m Qr Qg inner ζ).branching := by
  rw [pairTree_eq]
  exact (mem_node3_nil _).2.2

theorem lonePos_mem_leaves : lonePos m inner ∈ (pairTree m Qr Qg inner ζ).leaves := by
  have h := (mem_pairTree_b m Qr Qg inner ζ m.lone []).2.1
  simp only [ite_true] at h
  unfold lonePos
  have e : bPath m inner ++ [m.lone] = bPath m inner ++ m.lone :: [] := rfl
  rw [e, h]
  exact (mem_leaf_leaves []).2 rfl

/-- **The two top side trees.** -/
theorem mem_pairTree_top (i : Fin 3) (hi : i ≠ m.c) (q : Path) :
    (i :: q ∈ (pairTree m Qr Qg inner ζ).nodes ↔ q ∈ (if i = m.red.1 then
      treeOfSign Qr.trees (slotSign ζ i) else treeOfSign Qg.trees (slotSign ζ i)).nodes) ∧
    (i :: q ∈ (pairTree m Qr Qg inner ζ).leaves ↔ q ∈ (if i = m.red.1 then
      treeOfSign Qr.trees (slotSign ζ i) else treeOfSign Qg.trees (slotSign ζ i)).leaves) ∧
    (i :: q ∈ (pairTree m Qr Qg inner ζ).branching ↔ q ∈ (if i = m.red.1 then
      treeOfSign Qr.trees (slotSign ζ i) else treeOfSign Qg.trees (slotSign ζ i)).branching) := by
  rw [pairTree_eq, (mem_node3_nodes _ i q).1, (mem_node3_nodes _ i q).2.1, (mem_node3_nodes _ i q).2.2]
  simp only [hi, ite_false]
  exact ⟨trivial, trivial, trivial⟩

/-- Membership in a tree, all three kinds. -/
def MemT (p : Path) (T : TTree) (q : Path) (t : TTree) : Prop :=
  (p ∈ T.nodes ↔ q ∈ t.nodes) ∧ (p ∈ T.leaves ↔ q ∈ t.leaves) ∧ (p ∈ T.branching ↔ q ∈ t.branching)

theorem memT_redTop (q : Path) :
    MemT (m.red.1 :: q) (pairTree m Qr Qg inner ζ) q (treeOfSign Qr.trees (slotSign ζ m.red.1)) := by
  have h := mem_pairTree_top m Qr Qg inner ζ m.red.1 (red_ne_c m) q
  rw [if_pos rfl] at h
  exact h

theorem memT_greenTop (q : Path) :
    MemT (m.green.1 :: q) (pairTree m Qr Qg inner ζ) q (treeOfSign Qg.trees (slotSign ζ m.green.1)) := by
  have h := mem_pairTree_top m Qr Qg inner ζ m.green.1 (green_ne_c m) q
  rw [if_neg (fun h => red_ne_green m h.symm)] at h
  exact h

theorem memT_redBot (q : Path) :
    MemT (bPath m inner ++ m.red.2 :: q) (pairTree m Qr Qg inner ζ) q
      (treeOfSign Qr.trees (-slotSign ζ m.red.1)) := by
  have h := mem_pairTree_b m Qr Qg inner ζ m.red.2 q
  rw [if_neg (red2_ne_lone m), if_pos rfl, slotSign_red] at h
  exact h

theorem memT_greenBot (q : Path) :
    MemT (bPath m inner ++ m.green.2 :: q) (pairTree m Qr Qg inner ζ) q
      (treeOfSign Qg.trees (-slotSign ζ m.green.1)) := by
  have h := mem_pairTree_b m Qr Qg inner ζ m.green.2 q
  rw [if_neg (green2_ne_lone m), if_neg (fun h => red2_ne_green2 m h.symm), slotSign_green] at h
  exact h

/-- The trees of the red couple (`+` first). -/
def rTree (j : Fin 2) : TTree := if j = 0 then Qr.trees.1 else Qr.trees.2

theorem treeOfSign_eq (T : TTree × TTree) (σ : ℤˣ) :
    treeOfSign T σ = if σ = 1 then T.1 else T.2 := rfl

theorem units_ne_neg (σ : ℤˣ) : σ ≠ -σ := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> decide

theorem neg_units_eq_one {σ : ℤˣ} (hσ : σ ≠ 1) : -σ = 1 := by
  rcases Int.units_eq_one_or σ with rfl | rfl
  · exact absurd rfl hσ
  · rfl

theorem neg_units_ne_one {σ : ℤˣ} (hσ : σ = 1) : -σ ≠ 1 := by subst hσ; decide

theorem memT_base (P : RegCpl) (top bot : Path) (σ : ℤˣ)
    (htop : ∀ q, MemT (top ++ q) (pairTree m Qr Qg inner ζ) q (treeOfSign P.trees σ))
    (hbot : ∀ q, MemT (bot ++ q) (pairTree m Qr Qg inner ζ) q (treeOfSign P.trees (-σ)))
    (j : Fin 2) (q : Path) :
    MemT ((if (j = 0) = (σ = 1) then top else bot) ++ q) (pairTree m Qr Qg inner ζ) q
      (if j = 0 then P.trees.1 else P.trees.2) := by
  by_cases hs : σ = 1 <;> fin_cases j
  · have := htop q
    rw [treeOfSign_eq, if_pos hs] at this
    simpa [hs] using this
  · have := hbot q
    rw [treeOfSign_eq, if_neg (neg_units_ne_one hs)] at this
    simpa [hs] using this
  · have := hbot q
    rw [treeOfSign_eq, if_pos (neg_units_eq_one hs)] at this
    simpa [hs] using this
  · have := htop q
    rw [treeOfSign_eq, if_neg hs] at this
    simpa [hs] using this

/-- **The red couple, tree by tree.** -/
theorem memT_rBase (j : Fin 2) (q : Path) :
    MemT (rBase m inner ζ j ++ q) (pairTree m Qr Qg inner ζ) q (rTree Qr j) :=
  memT_base m Qr Qg inner ζ Qr [m.red.1] (bPath m inner ++ [m.red.2]) (slotSign ζ m.red.1)
    (fun q => memT_redTop m Qr Qg inner ζ q)
    (fun q => by simpa [List.append_assoc] using memT_redBot m Qr Qg inner ζ q) j q

/-- **The green couple, tree by tree.** -/
theorem memT_gBase (j : Fin 2) (q : Path) :
    MemT (gBase m inner ζ j ++ q) (pairTree m Qr Qg inner ζ) q (rTree Qg j) :=
  memT_base m Qr Qg inner ζ Qg [m.green.1] (bPath m inner ++ [m.green.2]) (slotSign ζ m.green.1)
    (fun q => memT_greenTop m Qr Qg inner ζ q)
    (fun q => by simpa [List.append_assoc] using memT_greenBot m Qr Qg inner ζ q) j q

section Regions

/-! ### Regions of the tree of a closing pair -/

/-- The region of an address of a closing pair. -/
inductive PReg
  | root | bnode | lone | red (j : Fin 2) | green (j : Fin 2) | inner | other
  deriving DecidableEq

variable (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ)

/-- The region of a path, by prefix tests (couples before the interior). -/
def regionOf (p : Path) : PReg :=
  if p = [] then .root else if p = bPath m inner then .bnode else if p = lonePos m inner then .lone
  else if rBase m inner ζ 0 <+: p then .red 0 else if rBase m inner ζ 1 <+: p then .red 1
  else if gBase m inner ζ 0 <+: p then .green 0 else if gBase m inner ζ 1 <+: p then .green 1
  else if [m.c] <+: p then .inner else .other

theorem bPath_eq : bPath m inner = m.c :: inner.lonePath := rfl

theorem lonePos_eq : lonePos m inner = m.c :: (inner.lonePath ++ [m.lone]) := by
  simp [lonePos, bPath]

theorem regionOf_nil : regionOf m inner ζ [] = .root := by simp [regionOf]

theorem regionOf_bPath : regionOf m inner ζ (bPath m inner) = .bnode := by
  simp [regionOf, bPath_eq]

theorem regionOf_lonePos : regionOf m inner ζ (lonePos m inner) = .lone := by
  have : m.c :: (inner.lonePath ++ [m.lone]) ≠ bPath m inner := by simp [bPath_eq]
  simp [regionOf, lonePos_eq, this]

theorem prefix_append_self (l q : Path) : l <+: l ++ q := List.prefix_append l q

theorem not_prefix_cons_of_ne {a b : Fin 3} (h : a ≠ b) (l l' : Path) : ¬ (a :: l) <+: (b :: l') := by
  rw [List.cons_prefix_cons]; exact fun h' => h h'.1

theorem regionOf_rBase (j : Fin 2) (q : Path) : regionOf m inner ζ (rBase m inner ζ j ++ q) = .red j := by
  have h1 := red_ne_c m
  have h2 := red2_ne_lone m
  by_cases hs : slotSign ζ m.red.1 = 1 <;> fin_cases j <;>
    simp [regionOf, rBase, hs, bPath_eq, lonePos_eq, h1, h2, h1.symm, List.cons_prefix_cons]

theorem regionOf_gBase (j : Fin 2) (q : Path) :
    regionOf m inner ζ (gBase m inner ζ j ++ q) = .green j := by
  have h1 := green_ne_c m
  have h2 := green2_ne_lone m
  have h3 := red_ne_c m
  have h4 := red_ne_green m
  have h5 := red2_ne_green2 m
  by_cases hs : slotSign ζ m.green.1 = 1 <;> by_cases hr : slotSign ζ m.red.1 = 1 <;> fin_cases j <;>
    simp [regionOf, rBase, gBase, hs, hr, bPath_eq, lonePos_eq, h1, h2, h3, h4, h5, h1.symm, h3.symm,
      h4.symm, h5.symm, List.cons_prefix_cons]

theorem regionOf_inner (q : Path) (hq : ¬ inner.lonePath <+: q) :
    regionOf m inner ζ (m.c :: q) = .inner := by
  have h3 := red_ne_c m
  have h1 := green_ne_c m
  have hq1 : q ≠ inner.lonePath := fun h => hq (h ▸ List.prefix_refl _)
  have hq2 : q ≠ inner.lonePath ++ [m.lone] := fun h => hq (h ▸ List.prefix_append _ _)
  have hq3 : ∀ k : Fin 3, ¬ (inner.lonePath ++ [k]) <+: q := fun k h =>
    hq ((List.prefix_append _ _).trans h)
  by_cases hs : slotSign ζ m.green.1 = 1 <;> by_cases hr : slotSign ζ m.red.1 = 1 <;>
    simp [regionOf, rBase, gBase, hs, hr, bPath_eq, lonePos_eq, h1, h3, h1.symm, h3.symm, hq1, hq2, hq3,
      List.cons_prefix_cons]

/-- **The shape of every node of a closing pair.** -/
theorem pairTree_cases (Qr Qg : RegCpl) (p : Path) (hp : p ∈ (pairTree m Qr Qg inner ζ).nodes) :
    p = [] ∨ p = bPath m inner ∨ p = lonePos m inner ∨
      (∃ q, p = m.c :: q ∧ ¬ inner.lonePath <+: q ∧ q ∈ (inner.plug (slotSign ζ m.c) .leaf).nodes) ∨
      (∃ j q, p = rBase m inner ζ j ++ q ∧ q ∈ (rTree Qr j).nodes) ∨
      (∃ j q, p = gBase m inner ζ j ++ q ∧ q ∈ (rTree Qg j).nodes) := by
  rcases p with _ | ⟨i, q⟩
  · exact Or.inl rfl
  right
  rcases slot_cases m i with rfl | rfl | rfl
  · by_cases hq : inner.lonePath <+: q
    · obtain ⟨q', rfl⟩ := hq
      rcases q' with _ | ⟨k, q''⟩
      · left; simp [bPath_eq]
      · have hp' : bPath m inner ++ k :: q'' ∈ (pairTree m Qr Qg inner ζ).nodes := by
          simpa [bPath_eq] using hp
        rcases slot2_cases m k with rfl | rfl | rfl
        · have := (mem_pairTree_b m Qr Qg inner ζ m.lone q'').1.mp hp'
          rw [if_pos rfl, mem_leaf_nodes] at this
          subst this
          right; left; simp [lonePos_eq]
        · right; right; right; left
          have hj : ∃ j, rBase m inner ζ j = bPath m inner ++ [m.red.2] := by
            by_cases hs : slotSign ζ m.red.1 = 1
            · exact ⟨1, by simp [rBase, hs]⟩
            · exact ⟨0, by simp [rBase, hs]⟩
          obtain ⟨j, hj⟩ := hj
          refine ⟨j, q'', by rw [hj]; simp [bPath_eq], ?_⟩
          have := (memT_rBase m Qr Qg inner ζ j q'').1
          rw [hj] at this
          exact this.mp (by simpa [bPath_eq] using hp)
        · right; right; right; right
          have hj : ∃ j, gBase m inner ζ j = bPath m inner ++ [m.green.2] := by
            by_cases hs : slotSign ζ m.green.1 = 1
            · exact ⟨1, by simp [gBase, hs]⟩
            · exact ⟨0, by simp [gBase, hs]⟩
          obtain ⟨j, hj⟩ := hj
          refine ⟨j, q'', by rw [hj]; simp [bPath_eq], ?_⟩
          have := (memT_gBase m Qr Qg inner ζ j q'').1
          rw [hj] at this
          exact this.mp (by simpa [bPath_eq] using hp)
    · right; right; left
      exact ⟨q, rfl, hq, (mem_pairTree_inner m Qr Qg inner ζ q hq).1.mp hp⟩
  · right; right; right; left
    have hj : ∃ j, rBase m inner ζ j = [m.red.1] := by
      by_cases hs : slotSign ζ m.red.1 = 1
      · exact ⟨0, by simp [rBase, hs]⟩
      · exact ⟨1, by simp [rBase, hs]⟩
    obtain ⟨j, hj⟩ := hj
    refine ⟨j, q, by rw [hj]; rfl, ?_⟩
    have := (memT_rBase m Qr Qg inner ζ j q).1
    rw [hj] at this
    exact this.mp hp
  · right; right; right; right
    have hj : ∃ j, gBase m inner ζ j = [m.green.1] := by
      by_cases hs : slotSign ζ m.green.1 = 1
      · exact ⟨0, by simp [gBase, hs]⟩
      · exact ⟨1, by simp [gBase, hs]⟩
    obtain ⟨j, hj⟩ := hj
    refine ⟨j, q, by rw [hj]; rfl, ?_⟩
    have := (memT_gBase m Qr Qg inner ζ j q).1
    rw [hj] at this
    exact this.mp hp

end Regions

end WaveTurbulence.Flower.ProtCut
