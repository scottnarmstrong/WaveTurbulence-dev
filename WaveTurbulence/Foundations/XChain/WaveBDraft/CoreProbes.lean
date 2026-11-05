/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-!
# Wave B tier B1 core — non-vacuity probes and audit lemmas (sorry-free)

* explicit trees and gardens (the trivial couple, the two `(1,1)`-mini-couples, the layered garden
  of TARGET Figures `LayerGarden.png` / `CanonGarden.png`), with their predicates decided;
* `IsCanonG 3` holds for the garden of Figure `CanonGarden.png` (WAVE-B §5 unit test (iii)), it is
  not in `𝒢₂`, and its truncation data are those of the figure;
* `IsCanonC 1` holds for the trivial couple and the mini-couples with all layers `0` (§5 (v));
* finiteness of the set of layered gardens of bounded order and depth (the `finsum`s of WAVE-B §2.4.3
  are genuine finite sums);
* `|ℒ| = 2 n(𝒯) + 1`, `|𝒩| = n(𝒯)`, and the parameter relations of WAVE-B §2.1;
* the stage-1 audit garden E1 (two attached gardens in one top tree): `e1_canon2`, `e1_topOrder`,
  `e1_trunc` (second truncation unit test);
* `omegaNode_latticeDecoration`: `Ω_𝔫` of a lattice decoration is `Ω` of its lattice vectors (the
  bridges to the landed `NLS.resonance` are in `WaveB1-Bridges.lean`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.WaveBProbes

open TTree

/-! ### Building gardens from address-level data -/

/-- Build a plain garden from an address-level pairing `f`, given the (decidable) garden axioms on
the leaf set. -/
def mkGarden (w : ℕ) (sig : Fin w → ℤˣ) (tree : Fin w → TTree) (f : Fin w × Path → Fin w × Path)
    (hf : ∀ a ∈ forestSet tree TTree.leaves, f a ∈ forestSet tree TTree.leaves ∧ f (f a) = a ∧
      f a ≠ a ∧ nodeSign sig (f a) = -nodeSign sig a) : Garden w where
  sig := sig
  tree := tree
  pair ℓ := ⟨f ℓ.1, (mem_forestSet tree).1 (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).1⟩
  mark _ := none
  pair_pair ℓ := Subtype.ext ((hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.1)
  pair_eq_iff ℓ := by
    simp only [ne_eq, not_true_eq_false, iff_false]
    intro h
    exact (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.2.1 (congrArg Subtype.val h)
  pair_sign ℓ _ := (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.2.2

theorem mkGarden_isPlain (w : ℕ) (sig : Fin w → ℤˣ) (tree) (f) (hf) :
    (mkGarden w sig tree f hf).IsPlain := fun _ => rfl

/-- Build a garden with marked leaves (the fixed points of `f`, with marks `mk`). -/
def mkGardenM (w : ℕ) (sig : Fin w → ℤˣ) (tree : Fin w → TTree)
    (f : Fin w × Path → Fin w × Path) (mk : Fin w × Path → Option MarkTag)
    (hf : ∀ a ∈ forestSet tree TTree.leaves, f a ∈ forestSet tree TTree.leaves ∧ f (f a) = a ∧
      (f a = a ↔ mk a ≠ none) ∧ (f a ≠ a → nodeSign sig (f a) = -nodeSign sig a)) : Garden w where
  sig := sig
  tree := tree
  pair ℓ := ⟨f ℓ.1, (mem_forestSet tree).1 (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).1⟩
  mark ℓ := mk ℓ.1
  pair_pair ℓ := Subtype.ext ((hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.1)
  pair_eq_iff ℓ := by
    have h := (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.2.1
    exact ⟨fun e => h.1 (congrArg Subtype.val e), fun e => Subtype.ext (h.2 e)⟩
  pair_sign ℓ h := (hf ℓ.1 ((mem_forestSet tree).2 ℓ.2)).2.2.2 (fun h' => h (Subtype.ext h'))

/-- Swap the two entries of each listed pair; fix everything else. -/
def swapList {α : Type*} [DecidableEq α] (l : List (α × α)) (a : α) : α :=
  match l.find? (fun x => x.1 = a) with
  | some x => x.2
  | none => match l.find? (fun x => x.2 = a) with
    | some x => x.1
    | none => a

/-! ### The trivial couple and the mini-couples -/

/-- The trivial couple `(•, •)`. -/
def trivialCouple : Garden 2 :=
  mkGarden 2 ![1, -1] ![TTree.leaf, TTree.leaf] (swapList [((0, []), (1, []))]) (by decide)

theorem trivialCouple_isCouple : IsCouple trivialCouple := by decide

theorem trivialCouple_order : trivialCouple.order = 0 := by decide

/-- The tree of order one. -/
def tree1 : TTree := .node .leaf .leaf .leaf

/-- The `(1,1)`-mini-couple of code `00` (WAVE-B §3.1): `L⁺ ↔ L⁻, M⁺ ↔ M⁻, R⁺ ↔ R⁻`. -/
def miniCouple00 : Garden 2 :=
  mkGarden 2 ![1, -1] ![tree1, tree1]
    (swapList [((0, [0]), (1, [0])), ((0, [1]), (1, [1])), ((0, [2]), (1, [2]))]) (by decide)

/-- The `(1,1)`-mini-couple of code `01`: `L⁺ ↔ R⁻, M⁺ ↔ M⁻, R⁺ ↔ L⁻`. -/
def miniCouple01 : Garden 2 :=
  mkGarden 2 ![1, -1] ![tree1, tree1]
    (swapList [((0, [0]), (1, [2])), ((0, [1]), (1, [1])), ((0, [2]), (1, [0]))]) (by decide)

/-- Pairing the left and right leaves of the `+` tree violates the sign rule. -/
example : ¬ (nodeSign (![1, -1] : Fin 2 → ℤˣ) (0, [0]) =
    -nodeSign (![1, -1] : Fin 2 → ℤˣ) (0, [2])) := by decide

theorem trivialCouple_balanced : trivialCouple.IsBalanced := by decide

/-- Layering all nodes in layer `0`. -/
abbrev layerZero {w : ℕ} (G : Garden w) : LayeredGarden w :=
  ⟨G, fun _ => 0, ⟨fun _ _ => le_rfl, fun _ => rfl⟩⟩

theorem trivialCouple_canon : IsCanonC 1 (layerZero trivialCouple) := by decide

theorem miniCouple00_canon : IsCanonC 1 (layerZero miniCouple00) := by decide

theorem miniCouple01_canon : IsCanonC 1 (layerZero miniCouple01) := by decide

theorem miniCouple00_order : miniCouple00.order = 2 := by decide

/-! ### A flower garden and a paired tree (T Def `defflower`, T L637) -/

/-- Two flower trees of order one, signs `(+,-)`, flowers at the left leaves; the mid and right
leaves are paired across. -/
def flowerPairs : List ((Fin 2 × Path) × (Fin 2 × Path)) :=
  [((0, [1]), (1, [1])), ((0, [2]), (1, [2]))]

def flowerGarden : Garden 2 :=
  mkGardenM 2 ![1, -1] ![tree1, tree1] (swapList flowerPairs)
    (fun a => if a.2 = [0] then some MarkTag.equal else none) (by decide)

theorem flowerGarden_isFlowerGarden : flowerGarden.IsFlowerGarden := by decide

theorem flowerGarden_not_plain : ¬ flowerGarden.IsPlain := by decide

/-- With all layers `0`, the flower garden is in `ℋ₁`. -/
theorem flowerGarden_canonH : IsCanonH 1 (layerZero flowerGarden) := by decide

/-- The mini-tree of code `10` (WAVE-B §3.2): root `u`, inner node `u' = c₁` (left), pairs
`c₂ ↔ d₃` (red), `c₃ ↔ d₂` (green), lone leaf `d₁`. -/
def miniTree10 : Garden 1 :=
  mkGardenM 1 ![1] ![.node tree1 .leaf .leaf]
    (swapList [((0, [1]), (0, [0, 2])), ((0, [2]), (0, [0, 1]))])
    (fun a => if a.2 = [0, 0] then some MarkTag.lower else none) (by decide)

theorem miniTree10_isPairedTree : IsPairedTree miniTree10 := by decide

/-! ### The layered garden of Figures `LayerGarden.png` / `CanonGarden.png` (T L649–L750) -/

/-- `𝒯₁` (sign `+`): root, children `(leaf, branching, leaf)`. -/
def figT1 : TTree := .node .leaf tree1 .leaf
/-- `𝒯₂` (sign `-`): root, children `(branching, leaf, leaf)`. -/
def figT2 : TTree := .node tree1 .leaf .leaf
/-- `𝒯₃` (sign `+`): the tree of order one. -/
def figT3 : TTree := tree1
/-- `𝒯₄` (sign `-`): trivial. -/
def figT4 : TTree := .leaf

/-- The seven leaf pairs of the figure, by colour: red, grey, magenta, green, yellow, blue, brown
(T L733–L750: `k₁₁ = k₁₆`, `k₁₄ = k₃₃`, `k₁₅ = k₂₃`, `k₁₃ = k₂₆`, `k₂₄ = k₃₁`, `k₂₅ = k₄`,
`k₂₂ = k₃₂`). -/
def figPairs : List ((Fin 4 × Path) × (Fin 4 × Path)) :=
  [((0, [0]), (0, [1, 2])), ((0, [1, 0]), (2, [2])), ((0, [1, 1]), (1, [2])),
   ((0, [2]), (1, [0, 2])), ((1, [0, 0]), (2, [0])), ((1, [0, 1]), (3, [])),
   ((1, [1]), (2, [1]))]

/-- The garden of Figure `LayerGarden.png`, signature `(+,-,+,-)`. -/
def figGarden : Garden 4 :=
  mkGarden 4 ![1, -1, 1, -1] ![figT1, figT2, figT3, figT4] (swapList figPairs) (by decide)

/-- The layers of Figure `LayerGarden.png`. -/
def figLayerAddr : Fin 4 × Path → ℕ
  | (0, []) => 2 | (0, [0]) => 2 | (0, [1]) => 2 | (0, [2]) => 1
  | (0, [1, 0]) => 0 | (0, [1, 1]) => 2 | (0, [1, 2]) => 2
  | (1, []) => 2 | (1, [0]) => 1 | (1, [1]) => 0 | (1, [2]) => 2
  | (1, [0, 0]) => 0 | (1, [0, 1]) => 1 | (1, [0, 2]) => 1
  | (2, _) => 0
  | (3, []) => 1
  | _ => 0

theorem figLayer_isLayering : IsLayering figGarden (fun a => figLayerAddr a.1) := by decide

/-- The layered garden of Figure `LayerGarden.png`. -/
def figLG : LayeredGarden 4 := ⟨figGarden, fun a => figLayerAddr a.1, figLayer_isLayering⟩

theorem figGarden_order : figGarden.order = 5 := by decide

theorem figGarden_irreducible : figGarden.Irreducible := by decide

/-- **WAVE-B §5 unit test (iii):** the garden of Figure `CanonGarden.png` is canonical of depth 3. -/
theorem figLG_canon3 : IsCanonG 3 figLG := by decide

/-- It is not of depth 2 (it has nodes in layer 2). -/
theorem figLG_not_canon2 : ¬ IsCanonG 2 figLG := by decide

/-- Lowering the layer of the red pair from `2` to `1` (still a layering) breaks criterion (ii):
the red leaves are paired, incomparable, with parent layers `2`, so `max(1,1) ≥ min(2,2)` fails.
This is the canonical obstruction "a leaf pair below the top layer must come from an attached
garden". -/
def figLayerAddrBad : Fin 4 × Path → ℕ := fun a =>
  if a = (0, [0]) ∨ a = (0, [1, 2]) then 1 else figLayerAddr a

theorem figLayerBad_isLayering : IsLayering figGarden (fun a => figLayerAddrBad a.1) := by decide

theorem figLGBad_not_canon3 :
    ¬ IsCanonG 3 ⟨figGarden, fun a => figLayerAddrBad a.1, figLayerBad_isLayering⟩ := by decide

/-- Truncation data of the figure at `p = 2`: the top trees `𝒯_j²` have orders `2, 1, 0, 0`. -/
theorem figLG_topOrder : (List.ofFn fun j => figLG.topOrder 2 j) = [2, 1, 0, 0] := by decide

/-- The six attachment nodes of Figure `CanonGarden.png` (the six-element leaf subset replaced by
`𝒢' ∈ 𝒢₂`). -/
theorem figLG_attachNodes_card : (figLG.attachNodes 2).card = 6 := by decide

theorem figLG_attach_total : ∑ u ∈ figLG.attachNodes 2, u.orderBelow = 2 := by decide

theorem attachedOrder_le_total {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (u : GNode LG.garden.tree) :
    LG.attachedOrder p u ≤ ∑ u' ∈ LG.attachNodes p, u'.orderBelow := by
  classical
  unfold LayeredGarden.attachedOrder
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The figure's garden is truncated for `(N_{p+1}, N_p) = (2, 2)` and not for `(1, ·)`. -/
theorem figLG_trunc : figLG.IsTrunc 2 2 2 := by
  refine ⟨?_, fun u _ => (attachedOrder_le_total figLG 2 u).trans (le_of_eq figLG_attach_total)⟩
  decide

theorem figLG_not_trunc (Natt : ℕ) : ¬ figLG.IsTrunc 2 1 Natt := by
  intro h
  have := h.1 0
  revert this
  decide

/-! ### Second truncation unit test: two attached gardens in one top tree (stage-1 audit E1)

The garden of the stage-1 audit (wt-orch, `scratch/WaveB-stage1-E1.lean`): width 4, signature
`(+,-,+,-)`, `𝒯₁ = node(node(tree1, •, •), •, tree1)`, `𝒯₂ = 𝒯₃ = 𝒯₄ = •`, the nodes `[]`, `[0]` of
`𝒯₁` in layer 1 and everything else in layer 0. At `p = 1` there are two attached gardens of
order 1, at `{[0,0],[0,1],[0,2],[1]}` of `𝒯₁` and at `{[2] of 𝒯₁, 𝒯₂, 𝒯₃, 𝒯₄}`. Generating the
linking relation on all nodes merged them through the root of `𝒯₁`; with `AttachLinkedOn` every
attached garden has order `≤ 1`, so the garden is in `𝒢^tr₂` for `(N₂, N₁) = (2, 1)`, as in
T Def `defgtr`. The figure garden alone cannot detect the merging (it has one attached garden). -/

/-- `𝒯₁ = node(node(tree1, •, •), •, tree1)`. -/
def e1T1 : TTree := .node (.node tree1 .leaf .leaf) .leaf tree1

/-- The pairs: `G₁` inside `𝒯₁` and `G₂` across `[2]` of `𝒯₁` and `𝒯₂, 𝒯₃, 𝒯₄`. -/
def e1Pairs : List ((Fin 4 × Path) × (Fin 4 × Path)) :=
  [((0, [0, 0, 0]), (0, [0, 1])), ((0, [0, 0, 1]), (0, [0, 2])), ((0, [0, 0, 2]), (0, [1])),
   ((0, [2, 0]), (1, [])), ((0, [2, 1]), (2, [])), ((0, [2, 2]), (3, []))]

def e1Garden : Garden 4 :=
  mkGarden 4 ![1, -1, 1, -1] ![e1T1, .leaf, .leaf, .leaf] (swapList e1Pairs) (by decide)

/-- The layers: `(0,[])` and `(0,[0])` in layer 1, everything else in layer 0. -/
def e1Layer : Fin 4 × Path → ℕ
  | (0, []) => 1
  | (0, [0]) => 1
  | _ => 0

theorem e1_isLayering : IsLayering e1Garden (fun a => e1Layer a.1) := by decide

def e1LG : LayeredGarden 4 := ⟨e1Garden, fun a => e1Layer a.1, e1_isLayering⟩

/-- The garden is in `𝒢₂` (criterion form). -/
theorem e1_canon2 : IsCanonG 2 e1LG := by decide

/-- Its top trees at `p = 1` have orders `(2, 0, 0, 0)`. -/
theorem e1_topOrder : (List.ofFn fun j => e1LG.topOrder 1 j) = [2, 0, 0, 0] := by decide

instance {w : ℕ} (LG : LayeredGarden w) (u u' : GNode LG.garden.tree) :
    Decidable (LG.AttachLinked u u') := by
  unfold LayeredGarden.AttachLinked
  infer_instance

/-- The attachment nodes of the first attached garden. -/
def e1S1 : Finset (Fin 4 × Path) := {(0, [0, 0]), (0, [0, 1]), (0, [0, 2]), (0, [1])}

theorem e1_linkedOn_preserves :
    ∀ x y : GNode e1LG.garden.tree, e1LG.AttachLinkedOn 1 x y → (x.1 ∈ e1S1 ↔ y.1 ∈ e1S1) := by
  unfold LayeredGarden.AttachLinkedOn
  decide

theorem e1_eqvGen_preserves {x y : GNode e1LG.garden.tree}
    (h : Relation.EqvGen (e1LG.AttachLinkedOn 1) x y) : (x.1 ∈ e1S1 ↔ y.1 ∈ e1S1) := by
  induction h with
  | rel x y hxy => exact e1_linkedOn_preserves x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Each of the two attached gardens has order `≤ 1`. -/
theorem e1_attachedOrder_le (u : GNode e1LG.garden.tree) : e1LG.attachedOrder 1 u ≤ 1 := by
  classical
  unfold LayeredGarden.attachedOrder
  by_cases h1 : u.1 ∈ e1S1
  · calc _ ≤ ∑ x ∈ (e1LG.attachNodes 1).filter (fun x => x.1 ∈ e1S1), x.orderBelow := by
          refine Finset.sum_le_sum_of_subset fun x hx => ?_
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, (e1_eqvGen_preserves hx.2).1 h1⟩
      _ = 1 := by decide
  · calc _ ≤ ∑ x ∈ (e1LG.attachNodes 1).filter (fun x => x.1 ∉ e1S1), x.orderBelow := by
          refine Finset.sum_le_sum_of_subset fun x hx => ?_
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun hx1 => h1 ((e1_eqvGen_preserves hx.2).2 hx1)⟩
      _ = 1 := by decide

/-- **The E1 garden is truncated for `(N₂, N₁) = (2, 1)`**, as in T Def `defgtr` (stage-1 R1). -/
theorem e1_trunc : e1LG.IsTrunc 1 2 1 :=
  ⟨by decide, fun u _ => e1_attachedOrder_le u⟩

/-! ### The resonance factor -/

/-- `Ω = 2⟨k₁ - k, k - k₃⟩` when `k₁ - k₂ + k₃ = k` (T (res)). -/
theorem resFactor_eq {d : ℕ} {k₁ k₂ k₃ k : Mom d} (h : k₁ - k₂ + k₃ = k) :
    resFactor k₁ k₂ k₃ k = 2 * inner ℝ (k₁ - k) (k - k₃) := by
  have hk₂ : k₂ = k₁ + k₃ - k := by rw [← h]; abel
  subst hk₂
  simp only [resFactor, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  linarith [real_inner_comm k₁ k₃, real_inner_comm k₁ k, real_inner_comm k₃ k]

/-- `omegaNode` (used by `kernelK`) of a lattice decoration is `Ω` of its lattice vectors, the form
used by `treeTerm` (stage-1 O3). -/
theorem omegaNode_latticeDecoration {w d : ℕ} (G : Garden w) (L : ℝ)
    (κ : GNode G.tree → (Fin d → ℤ)) (b : GBranch G.tree) :
    omegaNode G (cosetDecoration G L 0 κ) b =
      resFactor (latticePoint L (κ (b.child 0))) (latticePoint L (κ (b.child 1)))
        (latticePoint L (κ (b.child 2))) (latticePoint L (κ b.toNode)) := by
  simp only [omegaNode, cosetDecoration, zero_add]

/-! ### Trees: counting lemmas -/

theorem card_pre (i : Fin 3) (S : Finset Path) : (pre i S).card = S.card :=
  Finset.card_image_of_injective _ (List.cons_injective)

theorem pre_disjoint {i j : Fin 3} (hij : i ≠ j) (S T : Finset Path) :
    Disjoint (pre i S) (pre j T) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨q, -, rfl⟩ := mem_pre.1 hp
  exact hij (cons_mem_pre.1 hq).1.symm

/-- `|𝒩| = n(𝒯)`. -/
theorem card_branching : ∀ t : TTree, t.branching.card = t.order
  | .leaf => rfl
  | .node l m r => by
    rw [branching, Finset.card_insert_of_notMem (by simp [nil_notMem_pre]),
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_pre, card_pre, card_pre,
      card_branching l, card_branching m, card_branching r, order]
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨pre_disjoint (by decide) _ _, pre_disjoint (by decide) _ _⟩

/-- `|ℒ| = 2 n(𝒯) + 1` (T L630). -/
theorem card_leaves : ∀ t : TTree, t.leaves.card = 2 * t.order + 1
  | .leaf => rfl
  | .node l m r => by
    rw [leaves, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_pre, card_pre,
      card_pre, card_leaves l, card_leaves m, card_leaves r, order]
    · ring
    · exact pre_disjoint (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨pre_disjoint (by decide) _ _, pre_disjoint (by decide) _ _⟩

/-! ### Finiteness of layered gardens of bounded order and depth -/

theorem finite_order_le : ∀ n : ℕ, {T : TTree | T.order ≤ n}.Finite
  | 0 => by
    refine (Set.finite_singleton TTree.leaf).subset ?_
    intro T hT
    cases T with
    | leaf => rfl
    | node l m r => simp [order] at hT
  | n + 1 => by
    have ih := finite_order_le n
    refine ((Set.finite_singleton TTree.leaf).union
      (((ih.prod (ih.prod ih)).image fun x => TTree.node x.1 x.2.1 x.2.2))).subset ?_
    intro T hT
    cases T with
    | leaf => exact Or.inl rfl
    | node l m r =>
      simp only [Set.mem_ofPred_eq, order] at hT
      refine Or.inr ⟨(l, m, r), ⟨?_, ?_, ?_⟩, rfl⟩ <;> simp only [Set.mem_ofPred_eq] <;> omega

/-- The garden data with layers bounded by `p`, before imposing the axioms. -/
def RawData {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Type :=
  (Fin w → ℤˣ) × (GLeaf t → GLeaf t) × (GLeaf t → Option MarkTag) × (GNode t → Fin (p + 1))

instance {w : ℕ} (p : ℕ) (t : Fin w → TTree) : Finite (RawData p t) := by
  unfold RawData
  infer_instance

/-- The axioms of a layered garden on raw data. -/
def RawOK {w : ℕ} (p : ℕ) (t : Fin w → TTree) (x : RawData p t) : Prop :=
  (∀ ℓ, x.2.1 (x.2.1 ℓ) = ℓ) ∧ (∀ ℓ, x.2.1 ℓ = ℓ ↔ x.2.2.1 ℓ ≠ none) ∧
    (∀ ℓ, x.2.1 ℓ ≠ ℓ → nodeSign x.1 (x.2.1 ℓ).1 = -nodeSign x.1 ℓ.1) ∧
    (∀ b : GBranch t, ∀ i : Fin 3, ((x.2.2.2 (b.child i) : Fin (p + 1)) : ℕ) ≤ x.2.2.2 b.toNode) ∧
    ∀ ℓ : GLeaf t, ((x.2.2.2 ℓ.toNode : Fin (p + 1)) : ℕ) = x.2.2.2 (x.2.1 ℓ).toNode

/-- Assemble a layered garden from raw data satisfying the axioms. -/
def assemble {w : ℕ} (p : ℕ) (t : Fin w → TTree) (x : {x : RawData p t // RawOK p t x}) :
    LayeredGarden w where
  garden := ⟨x.1.1, t, x.1.2.1, x.1.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1⟩
  layer a := x.1.2.2.2 a
  isLayering := ⟨x.2.2.2.2.1, x.2.2.2.2.2⟩

/-- **Finiteness:** for every width `w`, order bound `n` and depth `p`, there are finitely many
layered gardens of order `≤ n` with all layers `≤ p`. Hence the `finsum`s over canonical layered
gardens of fixed order (T (ansatz3), (ansatz5), `layergarden`, `flowerest1`) are finite sums. -/
theorem finite_layeredGardens (w n p : ℕ) :
    {LG : LayeredGarden w | LG.garden.order ≤ n ∧ ∀ a, LG.layer a ≤ p}.Finite := by
  let B : Set (Fin w → TTree) := Set.pi Set.univ fun _ => {T : TTree | T.order ≤ n}
  have hB : B.Finite := Set.Finite.pi fun _ => finite_order_le n
  have : Finite B := hB.to_subtype
  let g : (Σ t : B, {x : RawData p t.1 // RawOK p t.1 x}) → LayeredGarden w :=
    fun y => assemble p y.1.1 y.2
  refine (Set.finite_range g).subset ?_
  rintro ⟨⟨sig, t, pair, mk, h1, h2, h3⟩, layer, hlay⟩ ⟨hord, hp⟩
  have ht : t ∈ B := by
    intro j _
    have : (t j).order ≤ ∑ j, (t j).order :=
      Finset.single_le_sum (f := fun j => (t j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
    exact this.trans hord
  refine ⟨⟨⟨t, ht⟩, ⟨(sig, pair, mk, fun a => ⟨layer a, Nat.lt_succ_of_le (hp a)⟩),
    ⟨h1, h2, h3, hlay.1, hlay.2⟩⟩⟩, rfl⟩

/-! ### Parameters (WAVE-B §2.1 audit lemmas) -/

/-- `Λ_p = 40d · Λ_{p+1}` for `p < 𝔇` (more precisely `p + 1 ≤ 𝔇 + 1`). -/
theorem Lambda_succ (P : WTParams) {p : ℕ} (hp : p ≤ P.D) :
    P.Lambda p = 40 * P.d * P.Lambda (p + 1) := by
  unfold WTParams.Lambda
  rw [show P.D + 1 - p = (P.D + 1 - (p + 1)) + 1 by omega, pow_succ, mul_comm]

/-- `θ_{p+1} < (4θ_{p+1} + θ_p)/5 < θ_p` (T L611) for `η > 0`. -/
theorem theta_chain (P : WTParams) (hη : 0 < P.η) (p : ℕ) :
    P.theta (p + 1) < (4 * P.theta (p + 1) + P.theta p) / 5 ∧
      (4 * P.theta (p + 1) + P.theta p) / 5 < P.theta p := by
  have hlt : P.theta (p + 1) < P.theta p := by
    unfold WTParams.theta
    have h20 : 0 < P.η ^ 20 := pow_pos hη 20
    have : (2 : ℝ)⁻¹ ^ (p + 1) < (2 : ℝ)⁻¹ ^ p :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self p)
    nlinarith
  constructor <;> linarith

/-- `R_{p-1} = N_p^{40d}` (T (parameters2)) for `1 ≤ p ≤ 𝔇`. -/
theorem R_pred (P : WTParams) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ P.D) :
    P.R (p - 1) = P.N p ^ (40 * P.d) := by
  unfold WTParams.R WTParams.N
  rw [show P.D - (p - 1) = (P.D - p) + 1 by omega]
  rfl

/-- `R_𝔇 = ⌊(log L)^{40d}⌋` (T (parameters2)). -/
theorem R_top (P : WTParams) : P.R P.D = ⌊Real.log P.L ^ (40 * P.d)⌋₊ := by
  unfold WTParams.R
  rw [Nat.sub_self]
  rfl

/-- The prefix is not self-contradictory: it holds for the trivially true statement. (Its
hypotheses are satisfiable as soon as (WKE) has a Schwartz solution, which is Wave A's
`wkelwp`.) -/
theorem wtPrefix_true : WTPrefix fun _ => True := by
  intro d _ γ _
  refine ⟨1, one_pos, fun η _ φin _ τstar _ φ _ => ⟨1, le_rfl, 1, one_pos, fun ν _ => ?_⟩⟩
  exact ⟨1, one_pos, fun δ _ D _ _ => ⟨1, le_rfl, 2, le_rfl, fun L _ => trivial⟩⟩

end WaveTurbulence.WaveBProbes
