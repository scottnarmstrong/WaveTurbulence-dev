/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Enhanced

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

/-- The node with code `k + 1`: its `(k+1)`-th child is `n`, its other children are `a, b` (left to
right). -/
def encNode (k : Fin 3) (a b n : EncTree) : EncTree :=
  if k = 0 then node .c1 n a b else if k = 1 then node .c2 a n b else node .c3 a b n

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
