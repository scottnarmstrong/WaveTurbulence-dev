/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Dominant

/-!
# Encoded trees (packet C5; DH21 §4.4.4, Defs 4.19–4.22, Props 4.20, 4.23, L874–L895)

* `EncTree`: a ternary tree with a code `𝚌_𝔫 ∈ {0,1,2,3}` (`ECode`) at each branching node;
* `EncTree.canonPath` (L876): from the root follow the `𝚌`-th child while `𝚌 ∈ {1,2,3}`;
* `EncTree.IsChain` (Def 4.19): the canonical path ends at a leaf (the tail leaf) and the two
  off-path children of every path node are leaves;
* types: `•`, type 1 (root code `0`), type 2 (root code in `{1,2,3}`);
* Prop 4.20 (`structure+`): a type-2 tree is `build L t` for a unique chain datum `L` (the codes
  `𝚌_j` and the trees `𝒯_{j,1}, 𝒯_{j,2}` replacing the off-path leaves) and tail `t` (`•` or type
  1): `build_spine`, `spine_tail`, `spine_build`; the encoded chain `𝒯₀` is
  `build (codes, •, •) •` (`isChain_build`);
* Def 4.21: equivalence via `Shape` (`EncTree.setoid`), clauses `EncTree.shape_node_c0` and
  `EncTree.shape_type2`;
* Def 4.22: the encoded tree `cplEnc 𝒬` of a dominant couple;
* Prop 4.23: `cplEnc` is onto (`cplEnc_encCode`), `𝒬 ~ 𝒬'` iff `cplEnc 𝒬 ~ cplEnc 𝒬'`
  (`domCpl_equiv_iff_enc`), and it induces a bijection of the equivalence classes
  (`domClassEquiv`). The key identity is `shape_cplEnc`: the encoded tree has exactly the shape of
  `(𝒬, ∅)`.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

/-- The code `𝚌_𝔫 ∈ {0, 1, 2, 3}` of a branching node of an encoded tree. -/
inductive ECode : Type
  | c0 | c1 | c2 | c3
  deriving DecidableEq

/-- **Encoded trees** (DH21 L874): ternary trees with a code at each branching node. -/
inductive EncTree : Type
  | leaf : EncTree
  | node (c : ECode) (t₁ t₂ t₃ : EncTree) : EncTree
  deriving DecidableEq

namespace EncTree

/-- **The canonical path** (DH21 L876), as the list of child slots `𝚌 - 1` taken from the root. -/
def canonPath : EncTree → List (Fin 3)
  | leaf => []
  | node .c0 _ _ _ => []
  | node .c1 t _ _ => 0 :: t.canonPath
  | node .c2 _ t _ => 1 :: t.canonPath
  | node .c3 _ _ t => 2 :: t.canonPath

/-- The subtree at the end of the canonical path (a leaf or a node of code `0`). -/
def canonEnd : EncTree → EncTree
  | leaf => leaf
  | node .c0 a b c => node .c0 a b c
  | node .c1 t _ _ => t.canonEnd
  | node .c2 _ t _ => t.canonEnd
  | node .c3 _ _ t => t.canonEnd

/-- **Encoded chains** (DH21 Def 4.19): the canonical path ends at a leaf (the tail leaf), and the
two children of every path node other than the next path node are leaves. -/
def IsChain : EncTree → Prop
  | leaf => True
  | node .c0 _ _ _ => False
  | node .c1 t a b => a = leaf ∧ b = leaf ∧ t.IsChain
  | node .c2 a t b => a = leaf ∧ b = leaf ∧ t.IsChain
  | node .c3 a b t => a = leaf ∧ b = leaf ∧ t.IsChain

/-- Type 1: the root has code `0` (DH21 Prop 4.20). -/
def IsType1 : EncTree → Prop
  | node .c0 _ _ _ => True
  | _ => False

/-- Type 2: the root has code in `{1, 2, 3}`. -/
def IsType2 : EncTree → Prop
  | node .c0 _ _ _ => False
  | node _ _ _ _ => True
  | leaf => False

/-- The node with code `k + 1`: its `(k+1)`-th child is `n`, its other children are `a, b` (left to
right). -/
def encNode (k : Fin 3) (a b n : EncTree) : EncTree :=
  if k = 0 then node .c1 n a b else if k = 1 then node .c2 a n b else node .c3 a b n

/-- **The decomposition along the canonical path** (DH21 Prop 4.20): the triples
`(𝚌_j - 1, 𝒯_{j,1}, 𝒯_{j,2})` of the path nodes (top to bottom) and the tail `𝒯_ta`. -/
def spine : EncTree → List (Fin 3 × EncTree × EncTree) × EncTree
  | leaf => ([], leaf)
  | node .c0 a b c => ([], node .c0 a b c)
  | node .c1 t a b => ((0, a, b) :: t.spine.1, t.spine.2)
  | node .c2 a t b => ((1, a, b) :: t.spine.1, t.spine.2)
  | node .c3 a b t => ((2, a, b) :: t.spine.1, t.spine.2)

/-- Rebuild a tree from a chain datum and a tail. -/
def build : List (Fin 3 × EncTree × EncTree) → EncTree → EncTree
  | [], t => t
  | (k, a, b) :: L, t => encNode k a b (build L t)

theorem build_spine : (t : EncTree) → build t.spine.1 t.spine.2 = t
  | leaf => rfl
  | node .c0 a b c => rfl
  | node .c1 t a b => by simp [spine, build, encNode, build_spine t]
  | node .c2 a t b => by simp [spine, build, encNode, build_spine t]
  | node .c3 a b t => by simp [spine, build, encNode, build_spine t]

/-- The tail is trivial or of type 1. -/
def IsTail (t : EncTree) : Prop := t = leaf ∨ t.IsType1

theorem spine_tail : (t : EncTree) → IsTail t.spine.2
  | leaf => Or.inl rfl
  | node .c0 _ _ _ => Or.inr trivial
  | node .c1 t _ _ => spine_tail t
  | node .c2 _ t _ => spine_tail t
  | node .c3 _ _ t => spine_tail t

theorem spine_encNode (k : Fin 3) (a b n : EncTree) :
    (encNode k a b n).spine = ((k, a, b) :: n.spine.1, n.spine.2) := by
  unfold encNode
  split_ifs with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · have : k = 2 := by revert k h0 h1; decide
    subst this; rfl

/-- **Uniqueness in DH21 Prop 4.20**: the chain datum and the tail of `build L t` are `L` and `t`. -/
theorem spine_build : (L : List (Fin 3 × EncTree × EncTree)) → (t : EncTree) → IsTail t →
    (build L t).spine = (L, t)
  | [], leaf, _ => rfl
  | [], node .c0 a b c, _ => rfl
  | [], node .c1 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | [], node .c2 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | [], node .c3 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | (k, a, b) :: L, t, h => by
    rw [build, spine_encNode, spine_build L t h]

/-- **DH21 Prop 4.20**: a type-2 encoded tree is obtained from a unique nontrivial chain datum
(codes and off-path trees) and a unique tail that is `•` or of type 1. -/
theorem structure_plus (T : EncTree) (hT : T.IsType2) :
    T.spine.1 ≠ [] ∧ IsTail T.spine.2 ∧ build T.spine.1 T.spine.2 = T ∧
      ∀ L t, IsTail t → build L t = T → L = T.spine.1 ∧ t = T.spine.2 := by
  refine ⟨?_, spine_tail T, build_spine T, fun L t ht hb => ?_⟩
  · cases T with
    | leaf => exact absurd hT id
    | node c a b d => cases c <;> simp_all [IsType2, spine]
  · have := spine_build L t ht
    rw [hb] at this
    rw [this]; exact ⟨rfl, rfl⟩

/-- The encoded chain `𝒯₀` of a chain datum: its off-path leaves and its tail are `•`. -/
def chainOf (L : List (Fin 3)) : EncTree := build (L.map fun k => (k, leaf, leaf)) leaf

theorem isChain_encNode (k : Fin 3) (n : EncTree) (h : n.IsChain) :
    (encNode k leaf leaf n).IsChain := by
  unfold encNode
  split_ifs <;> exact ⟨rfl, rfl, h⟩

/-- `𝒯₀` is an encoded chain (DH21 Def 4.19). -/
theorem isChain_chainOf : (L : List (Fin 3)) → (chainOf L).IsChain
  | [] => trivial
  | k :: L => isChain_encNode k _ (isChain_chainOf L)

theorem canonPath_encNode (k : Fin 3) (a b n : EncTree) :
    (encNode k a b n).canonPath = k :: n.canonPath := by
  unfold encNode
  split_ifs with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · have : k = 2 := by revert k h0 h1; decide
    subst this; rfl

/-- The canonical path of `build L t` follows the codes of `L` (and stops at the tail). -/
theorem canonPath_build : (L : List (Fin 3 × EncTree × EncTree)) → (t : EncTree) → IsTail t →
    (build L t).canonPath = L.map Prod.fst
  | [], leaf, _ => rfl
  | [], node .c0 a b c, _ => rfl
  | [], node .c1 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | [], node .c2 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | [], node .c3 _ _ _, h => by rcases h with h | h <;> simp_all [IsType1]
  | (k, a, b) :: L, t, h => by rw [build, canonPath_encNode, canonPath_build L t h]; rfl

/-! ### Shapes and the equivalence of encoded trees (DH21 Def 4.21) -/

/-- Assemble the shape from chain tuples and a tail shape. -/
def toShape : Tuples × Shape → Shape
  | (.nil, s) => s
  | (L, s) => .type2 L s

/-- The tuples `(0, 𝚌_j - 1, 𝒵_{j,1}, 𝒵_{j,2})` along the canonical path and the tail's shape. -/
def shapeAux : EncTree → Tuples × Shape
  | leaf => (.nil, .triv)
  | node .c0 a b c => (.nil, .type1 (toShape a.shapeAux) (toShape b.shapeAux) (toShape c.shapeAux))
  | node .c1 t a b => (.cons false 0 (toShape a.shapeAux) (toShape b.shapeAux) t.shapeAux.1,
      t.shapeAux.2)
  | node .c2 a t b => (.cons false 1 (toShape a.shapeAux) (toShape b.shapeAux) t.shapeAux.1,
      t.shapeAux.2)
  | node .c3 a b t => (.cons false 2 (toShape a.shapeAux) (toShape b.shapeAux) t.shapeAux.1,
      t.shapeAux.2)

/-- The shape of an encoded tree. -/
def shape (t : EncTree) : Shape := toShape t.shapeAux

/-- **The equivalence of encoded trees** (DH21 Def 4.21). -/
instance setoid : Setoid EncTree where
  r t t' := Shape.Equiv t.shape t'.shape
  iseqv := ⟨fun _ => Shape.equiv_refl _, Shape.Equiv.symm, Shape.Equiv.trans⟩

/-- Type 1 clause (DH21 Def 4.21): componentwise. -/
theorem shape_node_c0 (a b c : EncTree) : (node .c0 a b c).shape = .type1 a.shape b.shape c.shape :=
  rfl

/-- The tuples of a chain datum. -/
def tuplesOf : List (Fin 3 × EncTree × EncTree) → Tuples
  | [] => .nil
  | (k, a, b) :: L => .cons false k a.shape b.shape (tuplesOf L)

theorem shapeAux_encNode (k : Fin 3) (a b n : EncTree) :
    (encNode k a b n).shapeAux = (.cons false k a.shape b.shape n.shapeAux.1, n.shapeAux.2) := by
  unfold encNode
  split_ifs with h0 h1
  · subst h0; rfl
  · subst h1; rfl
  · have : k = 2 := by revert k h0 h1; decide
    subst this; rfl

theorem shapeAux_spine : (t : EncTree) → t.shapeAux = (tuplesOf t.spine.1, t.spine.2.shape)
  | leaf => rfl
  | node .c0 a b c => rfl
  | node .c1 t a b => by
    simp only [shapeAux, spine, tuplesOf, shapeAux_spine t]; rfl
  | node .c2 a t b => by
    simp only [shapeAux, spine, tuplesOf, shapeAux_spine t]; rfl
  | node .c3 a b t => by
    simp only [shapeAux, spine, tuplesOf, shapeAux_spine t]; rfl

/-- **Type 2 clause** (DH21 Def 4.21): the shape of a type-2 tree is its triples
`(𝚌_j, 𝒵_{j,1}, 𝒵_{j,2})` (with `𝙸 = 0`) and the shape of its tail; equivalence is a permutation
of the triples with equivalent trees and equivalent tails (`Shape.equiv_type2_iff`). -/
theorem shape_type2 (T : EncTree) (hT : T.IsType2) :
    T.shape = .type2 (tuplesOf T.spine.1) T.spine.2.shape := by
  rw [shape, shapeAux_spine]
  obtain ⟨hne, -⟩ := structure_plus T hT
  cases h : T.spine.1 with
  | nil => exact absurd h hne
  | cons x L => obtain ⟨k, a, b⟩ := x; rfl

end EncTree

/-! ### Dominant couples and encoded trees (DH21 Def 4.22, Prop 4.23) -/

open EncTree

mutual
/-- **The encoded tree of a dominant couple** (DH21 Def 4.22): `• ↦ •`; type 1 ↦ root code `0`
with the trees of `𝒬₁, 𝒬₂, 𝒬₃`; type 2 ↦ the encoded chain of the triples
`(𝚌_{j,ε}, 𝒬_{j,ε,1}, 𝒬_{j,ε,2})`, `+` chain first, increasing `j`, with tail the tree of `𝒬_lp`. -/
def cplEnc : RegCpl → EncTree
  | .triv => .leaf
  | .type1 _ Q₁ Q₂ Q₃ => .node .c0 (cplEnc Q₁) (cplEnc Q₂) (cplEnc Q₃)
  | .type2 Xp Xm Qlp => chainEnc Xp (chainEnc Xm (cplEnc Qlp))

/-- The chain part of `cplEnc`, continued by `t` at the tail. -/
def chainEnc : RegChain → EncTree → EncTree
  | .nil, t => t
  | .pair m Qr Qg _ rest, t => encNode m.c (cplEnc Qr) (cplEnc Qg) (chainEnc rest t)
end

mutual
/-- The shape of `(𝒬, ∅)`, independent of the placement. -/
def cplShape0 : RegCpl → Shape
  | .triv => .triv
  | .type1 _ Q₁ Q₂ Q₃ => .type1 (cplShape0 Q₁) (cplShape0 Q₂) (cplShape0 Q₃)
  | .type2 Xp Xm Qlp => .type2 ((chainTuples0 Xp).append (chainTuples0 Xm)) (cplShape0 Qlp)

/-- The tuples of a chain with `Z = ∅`. -/
def chainTuples0 : RegChain → Tuples
  | .nil => .nil
  | .pair m Qr Qg _ rest => .cons false m.c (cplShape0 Qr) (cplShape0 Qg) (chainTuples0 rest)
end

mutual
theorem cplShape_empty {w : ℕ} : (Q : RegCpl) → (a b : Fin w × Path) →
    cplShape ∅ Q a b = cplShape0 Q
  | .triv, _, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, a, b => by
    simp only [cplShape, cplShape0, cplShape_empty Q₁, cplShape_empty Q₂, cplShape_empty Q₃]
  | .type2 Xp Xm Qlp, a, b => by
    simp only [cplShape, cplShape0, chainTuples_empty Xp, chainTuples_empty Xm, cplShape_empty Qlp]

theorem chainTuples_empty {w : ℕ} : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    chainTuples ∅ X ζ a = chainTuples0 X
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, ζ, a => by
    simp only [chainTuples, chainTuples0, Finset.notMem_empty, decide_false, cplShape_empty Qr,
      cplShape_empty Qg, ite_self, chainTuples_empty rest]
end

theorem Tuples.append_nil : (L : Tuples) → L.append .nil = L
  | .nil => rfl
  | .cons I c X₁ X₂ rest => by rw [Tuples.append, Tuples.append_nil rest]

theorem tuples_append_cons (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) (L L' : Tuples) :
    (Tuples.cons I c X₁ X₂ L).append L' = .cons I c X₁ X₂ (L.append L') := rfl

mutual
/-- **The encoded tree has the shape of the enhanced couple `(𝒬, ∅)`.** -/
theorem shape_cplEnc : (Q : RegCpl) → Q.wf = true → (cplEnc Q).shape = cplShape0 Q
  | .triv, _ => rfl
  | .type1 _ Q₁ Q₂ Q₃, h => by
    simp only [RegCpl.wf, Bool.and_eq_true] at h
    simp only [cplEnc, shape_node_c0, cplShape0, shape_cplEnc Q₁ h.1.1, shape_cplEnc Q₂ h.1.2,
      shape_cplEnc Q₃ h.2]
  | .type2 Xp Xm Qlp, h => by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hp, hm⟩, hl⟩, hlt⟩, hnn⟩ := h
    have htail : (cplEnc Qlp).shapeAux = (.nil, cplShape0 Qlp) := by
      cases Qlp with
      | triv => rfl
      | type1 c Q₁ Q₂ Q₃ =>
        have := shape_cplEnc (.type1 c Q₁ Q₂ Q₃) hl
        simp only [cplEnc, shapeAux] at this ⊢
        rw [← this]; rfl
      | type2 _ _ _ => simp [RegCpl.isType2] at hlt
    have hm' := chainEnc_shapeAux Xm hm (cplEnc Qlp)
    have hp' := chainEnc_shapeAux Xp hp (chainEnc Xm (cplEnc Qlp))
    rw [hm', htail] at hp'
    simp only [shape, cplEnc, hp', cplShape0, Tuples.append_nil]
    -- the chain tuples are nonempty
    cases Xp with
    | pair m Qr Qg inner rest => rfl
    | nil =>
      cases Xm with
      | pair m Qr Qg inner rest => rfl
      | nil => simp [RegChain.isNil] at hnn

/-- The shape data of `chainEnc X t`: the chain tuples followed by those of `t`. -/
theorem chainEnc_shapeAux : (X : RegChain) → X.wf = true → (t : EncTree) →
    (chainEnc X t).shapeAux = ((chainTuples0 X).append t.shapeAux.1, t.shapeAux.2)
  | .nil, _, t => rfl
  | .pair m Qr Qg _ rest, h, t => by
    simp only [RegChain.wf, Bool.and_eq_true] at h
    simp only [chainEnc, shapeAux_encNode, chainEnc_shapeAux rest h.2 t, chainTuples0,
      tuples_append_cons, shape_cplEnc Qr h.1.1.1, shape_cplEnc Qg h.1.1.2]
end

/-! ### The inverse construction -/

/-- The chain code of a list of pairs `(mini-tree code, red couple, green couple)` with
consecutive pairs (`inner = nil`). -/
def chainOfList : List (MiniTreeCode × RegCpl × RegCpl) → RegChain
  | [] => .nil
  | (m, qr, qg) :: L => .pair m qr qg .nil (chainOfList L)

/-- Assemble a couple code from chain pairs and the lone-pair couple. -/
def assemble : List (MiniTreeCode × RegCpl × RegCpl) × RegCpl → RegCpl
  | ([], q) => q
  | (L, q) => .type2 (chainOfList L) .nil q

/-- The chain pairs and the tail couple read off an encoded tree (codes `𝚌 - 1` with second digit
`0`, mini-couple code `0` at type-1 nodes). -/
def encCodeAux : EncTree → List (MiniTreeCode × RegCpl × RegCpl) × RegCpl
  | .leaf => ([], .triv)
  | .node .c0 a b c =>
    ([], .type1 0 (assemble (encCodeAux a)) (assemble (encCodeAux b)) (assemble (encCodeAux c)))
  | .node .c1 t a b => ((⟨0, 0⟩, assemble (encCodeAux a), assemble (encCodeAux b)) ::
      (encCodeAux t).1, (encCodeAux t).2)
  | .node .c2 a t b => ((⟨1, 0⟩, assemble (encCodeAux a), assemble (encCodeAux b)) ::
      (encCodeAux t).1, (encCodeAux t).2)
  | .node .c3 a b t => ((⟨2, 0⟩, assemble (encCodeAux a), assemble (encCodeAux b)) ::
      (encCodeAux t).1, (encCodeAux t).2)

/-- A dominant couple code with a given encoded tree. -/
def encCode (t : EncTree) : RegCpl := assemble (encCodeAux t)

end WaveTurbulence.Links
