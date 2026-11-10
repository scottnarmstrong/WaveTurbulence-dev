/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Shape
public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Special

/-!
# Enhanced dominant couples and trees, and their equivalence (packet C5)

* DH21 Def 4.17 (`defstd`): dominant couples — the B2 draft's `RegCpl.dominant` (checked against the
  source in `Dominant.lean`).
* DH21 Def 4.18 (`equivcpl`), TARGET Def 6.4 (`defencpl`): an **enhanced dominant couple** is
  `(𝒬, Z)` with `𝒬` dominant and `Z ⊆ 𝒩^ch` special (`EnhCpl`); `(𝒬, Z) ~ (𝒬', Z')` is defined
  recursively: trivial only with trivial, different types never; type 1 componentwise on
  `(𝒬_j, Z_j)`; type 2 when the tuples `(𝙸_{j,ε}, 𝚌_{j,ε}, 𝒳_{j,ε,1}, 𝒳_{j,ε,2})` of both chains
  form a permutation of those of `𝒬'` (with equivalent sub-objects) and `𝒴 = 𝒴'` (class of
  `(𝒬_lp, Z_lp)`). TARGET adds "different layers are never equivalent" (`LayEnhCpl`).
* TARGET Def 6.5 (`defentree`): **enhanced dominant trees** `(𝒯, Z)` (`EnhTree`), equivalent iff same
  layer and the tuples `(𝙸_{j,0}, 𝚌_{j,0}, 𝒳_{j,0,1}, 𝒳_{j,0,2})` form a permutation (`LayEnhTree`).

The recursive comparison is `Shape.Equiv` on the shapes `cplShape` / `chainTuples`; the source
clauses are `equiv_triv_iff`, `equiv_type1_iff`, `equiv_type2_iff`, and the invariants of DH21 L873
are `EnhCpl.size_eq_of_equiv`, `EnhCpl.card_eq_of_equiv` (`n(𝒬) = n(𝒬')`, `|Z| = |Z'|`).

**Readings.** (R1) Sub-objects are compared with the global `Z`, tested only at their own nodes; this
is `(𝒬_j, Z_j)` with `Z_j = Z ∩ 𝒩_j^ch`. (R2) `𝚌_{j,ε} ∈ {1,2,3}` is stored as `m.c = 𝚌 - 1 : Fin 3`.
(R3) The tuples of a chain are read along its pairs `{2j-1, 2j}`; for non-dominant chains (excluded
from enhanced objects) the nested pairs are ignored.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-! ### Generic clauses of the equivalence -/

theorem Shape.equiv_type2_iff (L L' : Tuples) (Y Y' : Shape) :
    Shape.Equiv (.type2 L Y) (.type2 L' Y') ↔
      (∃ e : Fin L.length ≃ Fin L'.length, ∀ i,
        (L.get i).1 = (L'.get (e i)).1 ∧ (L.get i).2.1 = (L'.get (e i)).2.1 ∧
        Shape.Equiv (L.get i).2.2.1 (L'.get (e i)).2.2.1 ∧
        Shape.Equiv (L.get i).2.2.2 (L'.get (e i)).2.2.2) ∧ Shape.Equiv Y Y' := by
  constructor
  · intro h
    cases h with
    | type2 e hI hc h₁ h₂ hY => exact ⟨⟨e, fun i => ⟨hI i, hc i, h₁ i, h₂ i⟩⟩, hY⟩
  · rintro ⟨⟨e, he⟩, hY⟩
    exact .type2 e (fun i => (he i).1) (fun i => (he i).2.1) (fun i => (he i).2.2.1)
      (fun i => (he i).2.2.2) hY

/-! ### Shapes of codes -/

mutual
/-- **The shape of the enhanced couple `(𝒬, Z)`** placed with its `+` tree at `a` and its `-` tree
at `b` (sub-couples placed as in `RegCpl.linksAt`). -/
def cplShape (Z : Finset (Fin w × Path)) : RegCpl → (Fin w × Path) → (Fin w × Path) → Shape
  | .triv, _, _ => .triv
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    .type1 (cplShape Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]))
      (cplShape Z Q₂ (addrExt b [1]) (addrExt a [1]))
      (cplShape Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]))
  | .type2 Xp Xm Qlp, a, b =>
    .type2 ((chainTuples Z Xp 1 a).append (chainTuples Z Xm (-1) b))
      (cplShape Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))

/-- **The tuples `(𝙸_j, 𝚌_j - 1, 𝒳_{j,1}, 𝒳_{j,2})` of a chain** rooted at `a` with root sign `ζ`,
one per pair `{2j-1, 2j}` in order: `𝙸_j = [𝔫_{2j-1} ∈ Z]`, `𝚌_j - 1 = m.c`, and the shapes of the
red and green couples `𝒬_{j,1}`, `𝒬_{j,2}`. -/
def chainTuples (Z : Finset (Fin w × Path)) : RegChain → ℤˣ → (Fin w × Path) → Tuples
  | .nil, _, _ => .nil
  | .pair m Qr Qg inner rest, ζ, a =>
    .cons (decide (a ∈ Z)) m.c
      (if slotSign ζ m.red.1 = 1 then
        cplShape Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else cplShape Z Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1]))
      (if slotSign ζ m.green.1 = 1 then
        cplShape Z Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else
        cplShape Z Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1]))
      (chainTuples Z rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

theorem Tuples.zcount_append : (L L' : Tuples) → (L.append L').zcount = L.zcount + L'.zcount
  | .nil, L' => by simp [Tuples.append, Tuples.zcount]
  | .cons I c X₁ X₂ rest, L' => by
    simp [Tuples.append, Tuples.zcount, Tuples.zcount_append rest L']; omega

/-! ### Enhanced dominant couples -/

/-- **An enhanced dominant couple** (DH21 Def 4.18, TARGET Def 6.4): a well-formed dominant couple
code with a special subset `Z ⊆ 𝒩^ch` (TARGET's definition, equal to DH21's by
`mem_specialSets_iff`). -/
structure EnhCpl where
  /-- the dominant couple (its structure code) -/
  code : RegCpl
  wf : code.wf = true
  dominant : code.dominant = true
  /-- the special subset -/
  Z : Finset (Fin 2 × Path)
  special : Z ∈ specialSets code.links

/-- The shape of an enhanced dominant couple. -/
def EnhCpl.shape (q : EnhCpl) : Shape := cplShape q.Z q.code (0, []) (1, [])

/-- **The equivalence of enhanced dominant couples** (DH21 Def 4.18). -/
instance EnhCpl.setoid : Setoid EnhCpl where
  r q q' := Shape.Equiv q.shape q'.shape
  iseqv := ⟨fun _ => Shape.equiv_refl _, Shape.Equiv.symm, Shape.Equiv.trans⟩

/-! ### TARGET's layered versions -/

/-- **An enhanced dominant couple with all nodes in layer `r`** (TARGET Def 6.4). -/
structure LayEnhCpl where
  /-- the common layer `𝔏` of all nodes -/
  layer : ℕ
  /-- the enhanced dominant couple -/
  enh : EnhCpl

/-- **TARGET's equivalence** (Def 6.4): same layer, and equivalent as in DH21 Def 4.18. -/
instance LayEnhCpl.setoid : Setoid LayEnhCpl where
  r q q' := q.layer = q'.layer ∧ q.enh ≈ q'.enh
  iseqv := ⟨fun _ => ⟨rfl, Setoid.refl _⟩, fun h => ⟨h.1.symm, Setoid.symm h.2⟩,
    fun h h' => ⟨h.1.trans h'.1, Setoid.trans h.2 h'.2⟩⟩

/-- **An enhanced dominant tree** (TARGET Def 6.5): a well-formed dominant tree code of sign `ζ`
(a regular chain whose pairs are `{2j-1, 2j}`, with dominant couples) and a special subset `Z`. -/
structure EnhTree where
  /-- the dominant tree (its chain code `𝒳₀` with couples `𝒬_{j,0,ι}`) -/
  code : RegChain
  /-- the sign of the tree -/
  sign : ℤˣ
  wf : code.wf = true
  dominant : code.dominant = true
  /-- the special subset -/
  Z : Finset (Fin 1 × Path)
  special : Z ∈ specialSets (code.treeLinks sign)

/-- The tuples `(𝙸_{j,0}, 𝚌_{j,0} - 1, 𝒳_{j,0,1}, 𝒳_{j,0,2})` of an enhanced dominant tree. -/
def EnhTree.tuples (t : EnhTree) : Tuples := chainTuples t.Z t.code t.sign (0, [])

/-- The shape of an enhanced dominant tree (its tuples, no tail). -/
def EnhTree.shape (t : EnhTree) : Shape := .type2 t.tuples .triv

/-- **An enhanced dominant tree with all nodes except the lone leaf in layer `r`** (TARGET Def 6.5). -/
structure LayEnhTree where
  /-- the common layer -/
  layer : ℕ
  /-- the enhanced dominant tree -/
  enh : EnhTree

/-- **TARGET's equivalence of enhanced dominant trees** (Def 6.5): same layer, and the tuples form a
permutation of each other with equivalent sub-objects. -/
instance LayEnhTree.setoid : Setoid LayEnhTree where
  r t t' := t.layer = t'.layer ∧ Shape.Equiv t.enh.shape t'.enh.shape
  iseqv := ⟨fun _ => ⟨rfl, Shape.equiv_refl _⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

end WaveTurbulence.Links
