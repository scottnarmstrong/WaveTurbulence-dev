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

theorem Shape.equiv_triv_iff (s : Shape) : Shape.Equiv .triv s ↔ s = .triv := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .triv

theorem Shape.equiv_type1_iff (a b c a' b' c' : Shape) :
    Shape.Equiv (.type1 a b c) (.type1 a' b' c') ↔
      Shape.Equiv a a' ∧ Shape.Equiv b b' ∧ Shape.Equiv c c' := by
  constructor
  · intro h; cases h with | type1 h₁ h₂ h₃ => exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact .type1 h₁ h₂ h₃

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

/-- The type of a code: `0` trivial, `1`, `2`. -/
def cplTypeNum : RegCpl → ℕ
  | .triv => 0
  | .type1 .. => 1
  | .type2 .. => 2

theorem cplShape_type (Z : Finset (Fin w × Path)) (Q : RegCpl) (a b : Fin w × Path) :
    (cplShape Z Q a b).type = cplTypeNum Q := by
  cases Q <;> rfl

theorem Tuples.size_append : (L L' : Tuples) → (L.append L').size = L.size + L'.size
  | .nil, L' => by simp [Tuples.append, Tuples.size]
  | .cons I c X₁ X₂ rest, L' => by
    simp [Tuples.append, Tuples.size, Tuples.size_append rest L']; omega

theorem Tuples.zcount_append : (L L' : Tuples) → (L.append L').zcount = L.zcount + L'.zcount
  | .nil, L' => by simp [Tuples.append, Tuples.zcount]
  | .cons I c X₁ X₂ rest, L' => by
    simp [Tuples.append, Tuples.zcount, Tuples.zcount_append rest L']; omega

mutual
/-- For dominant codes the shape has the order of the code. -/
theorem cplShape_size (Z : Finset (Fin w × Path)) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → (cplShape Z Q a b).size = Q.size
  | .triv, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplShape, Shape.size, RegCpl.size, cplShape_size Z Q₁ h.1.1,
      cplShape_size Z Q₂ h.1.2, cplShape_size Z Q₃ h.2]
  | .type2 Xp Xm Qlp, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplShape, Shape.size, RegCpl.size, Tuples.size_append,
      chainTuples_size Z Xp h.1.1, chainTuples_size Z Xm h.1.2, cplShape_size Z Qlp h.2]

theorem chainTuples_size (Z : Finset (Fin w × Path)) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) → (chainTuples Z X ζ a).size = X.size
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    have er : (if slotSign ζ m.red.1 = 1 then
        cplShape Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplShape Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).size = Qr.size := by
      split_ifs <;> exact cplShape_size Z Qr hr _ _
    have eg : (if slotSign ζ m.green.1 = 1 then
        cplShape Z Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplShape Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).size = Qg.size := by
      split_ifs <;> exact cplShape_size Z Qg hg _ _
    simp only [chainTuples, Tuples.size, RegChain.size, er, eg, chainTuples_size Z rest hs]
    omega
end

mutual
/-- For dominant codes the special count of the shape counts the special nodes in `Z`. -/
theorem cplShape_zcount (Z : Finset (Fin w × Path)) : (Q : RegCpl) → Q.dominant = true →
    (a b : Fin w × Path) → (cplShape Z Q a b).zcount = (cplSpecial Q a b).countP (· ∈ Z)
  | .triv, _, _, _ => rfl
  | .type1 c Q₁ Q₂ Q₃, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplShape, Shape.zcount, cplSpecial, List.countP_append, cplShape_zcount Z Q₁ h.1.1,
      cplShape_zcount Z Q₂ h.1.2, cplShape_zcount Z Q₃ h.2]
  | .type2 Xp Xm Qlp, h, a, b => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at h
    simp only [cplShape, Shape.zcount, cplSpecial, Tuples.zcount_append, List.countP_append,
      chainTuples_zcount Z Xp h.1.1, chainTuples_zcount Z Xm h.1.2, cplShape_zcount Z Qlp h.2]

theorem chainTuples_zcount (Z : Finset (Fin w × Path)) : (X : RegChain) → X.dominant = true →
    (ζ : ℤˣ) → (a : Fin w × Path) →
      (chainTuples Z X ζ a).zcount = (chainSpecial X ζ a).countP (· ∈ Z)
  | .nil, _, _, _ => rfl
  | .pair m Qr Qg inner rest, h, ζ, a => by
    simp only [RegChain.dominant, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hi, hr⟩, hg⟩, hs⟩ := h
    have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
    subst hin
    have er : (if slotSign ζ m.red.1 = 1 then
        cplShape Z Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplShape Z Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).zcount =
        (if slotSign ζ m.red.1 = 1 then
        cplSpecial Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
      else cplSpecial Qr (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.red.2]))
        (addrExt a [m.red.1])).countP (· ∈ Z) := by
      split_ifs <;> exact cplShape_zcount Z Qr hr _ _
    have eg : (if slotSign ζ m.green.1 = 1 then
        cplShape Z Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplShape Z Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).zcount =
        (if slotSign ζ m.green.1 = 1 then
        cplSpecial Qg (addrExt a [m.green.1])
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
      else cplSpecial Qg (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.green.2]))
        (addrExt a [m.green.1])).countP (· ∈ Z) := by
      split_ifs <;> exact cplShape_zcount Z Qg hg _ _
    simp only [chainTuples, Tuples.zcount, chainSpecial, RegChain.isNil, ↓reduceIte,
      List.countP_append, er, eg, chainTuples_zcount Z rest hs, chainSpecial, List.countP_nil,
      List.countP_singleton]
    simp only [decide_eq_true_eq]
    omega
end

theorem countP_mem_eq_card {α : Type*} [DecidableEq α] {L : List α} (hL : L.Nodup) {Z : Finset α}
    (hZ : ∀ z ∈ Z, z ∈ L) : L.countP (· ∈ Z) = Z.card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext z
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hZ z h, h⟩⟩

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

theorem EnhCpl.equiv_iff (q q' : EnhCpl) : q ≈ q' ↔ Shape.Equiv q.shape q'.shape := Iff.rfl

/-- Equivalent enhanced dominant couples have the same type. -/
theorem EnhCpl.typeNum_eq_of_equiv {q q' : EnhCpl} (h : q ≈ q') :
    cplTypeNum q.code = cplTypeNum q'.code := by
  have := Shape.Equiv.type_eq h
  rw [EnhCpl.shape, EnhCpl.shape, cplShape_type, cplShape_type] at this
  exact this

/-- **Equivalent enhanced dominant couples have the same order** (DH21 L873). -/
theorem EnhCpl.size_eq_of_equiv {q q' : EnhCpl} (h : q ≈ q') : q.code.size = q'.code.size := by
  have := Shape.Equiv.size_eq h
  rwa [EnhCpl.shape, EnhCpl.shape, cplShape_size _ _ q.dominant, cplShape_size _ _ q'.dominant]
    at this

theorem EnhCpl.zcount_shape (q : EnhCpl) : q.shape.zcount = q.Z.card := by
  rw [EnhCpl.shape, cplShape_zcount _ _ q.dominant]
  exact countP_mem_eq_card (specialList_nodup q.code) ((mem_specialSets_iff _ _).1 q.special)

/-- **Equivalent enhanced dominant couples have the same `|Z|`** (DH21 L873). -/
theorem EnhCpl.card_eq_of_equiv {q q' : EnhCpl} (h : q ≈ q') : q.Z.card = q'.Z.card := by
  rw [← q.zcount_shape, ← q'.zcount_shape]
  exact Shape.Equiv.zcount_eq h

/-- The trivial enhanced couple is only equivalent to itself (DH21 Def 4.18). -/
theorem EnhCpl.equiv_of_triv {q q' : EnhCpl} (hq : q.code = .triv) : q ≈ q' ↔ q'.code = .triv := by
  rw [EnhCpl.equiv_iff, EnhCpl.shape, hq]
  show Shape.Equiv .triv _ ↔ _
  rw [Shape.equiv_triv_iff, EnhCpl.shape]
  generalize q'.code = Q
  cases Q <;> simp [cplShape]

/-- **Type 1 clause** (DH21 Def 4.18): `(𝒬, Z) ~ (𝒬', Z')` iff `(𝒬_j, Z_j) ~ (𝒬'_j, Z'_j)`,
`j = 1, 2, 3`. -/
theorem cplShape_type1_equiv_iff (Z Z' : Finset (Fin 2 × Path)) (c c' : MiniCplCode)
    (Q₁ Q₂ Q₃ Q₁' Q₂' Q₃' : RegCpl) (a b a' b' : Fin 2 × Path) :
    Shape.Equiv (cplShape Z (.type1 c Q₁ Q₂ Q₃) a b) (cplShape Z' (.type1 c' Q₁' Q₂' Q₃') a' b') ↔
      Shape.Equiv (cplShape Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]))
        (cplShape Z' Q₁' (addrExt a' [0]) (addrExt b' [c'.partner 0])) ∧
      Shape.Equiv (cplShape Z Q₂ (addrExt b [1]) (addrExt a [1]))
        (cplShape Z' Q₂' (addrExt b' [1]) (addrExt a' [1])) ∧
      Shape.Equiv (cplShape Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]))
        (cplShape Z' Q₃' (addrExt a' [2]) (addrExt b' [c'.partner 2])) :=
  Shape.equiv_type1_iff _ _ _ _ _ _

/-- **Type 2 clause** (DH21 Def 4.18 (i)–(iii)): `(𝒬, Z) ~ (𝒬', Z')` iff the `m⁺ + m⁻` tuples of
`𝒬` correspond bijectively to those of `𝒬'` (so `m⁺ + m⁻ = m'⁺ + m'⁻`) with equal `𝙸`, equal
`𝚌` and equivalent sub-objects, and `𝒴 ~ 𝒴'`. -/
theorem cplShape_type2_equiv_iff (Z Z' : Finset (Fin 2 × Path)) (Xp Xm Xp' Xm' : RegChain)
    (Qlp Qlp' : RegCpl) (a b a' b' : Fin 2 × Path) :
    Shape.Equiv (cplShape Z (.type2 Xp Xm Qlp) a b) (cplShape Z' (.type2 Xp' Xm' Qlp') a' b') ↔
      (∃ e : Fin ((chainTuples Z Xp 1 a).append (chainTuples Z Xm (-1) b)).length ≃
          Fin ((chainTuples Z' Xp' 1 a').append (chainTuples Z' Xm' (-1) b')).length, ∀ i,
        let t := ((chainTuples Z Xp 1 a).append (chainTuples Z Xm (-1) b)).get i
        let t' := ((chainTuples Z' Xp' 1 a').append (chainTuples Z' Xm' (-1) b')).get (e i)
        t.1 = t'.1 ∧ t.2.1 = t'.2.1 ∧ Shape.Equiv t.2.2.1 t'.2.2.1 ∧ Shape.Equiv t.2.2.2 t'.2.2.2) ∧
      Shape.Equiv (cplShape Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))
        (cplShape Z' Qlp' (addrExt a' Xp'.lonePath) (addrExt b' Xm'.lonePath)) :=
  Shape.equiv_type2_iff _ _ _ _

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

/-- The tree clause (TARGET Def 6.5): the tuples correspond bijectively. -/
theorem LayEnhTree.equiv_iff (t t' : LayEnhTree) :
    t ≈ t' ↔ t.layer = t'.layer ∧ ∃ e : Fin t.enh.tuples.length ≃ Fin t'.enh.tuples.length, ∀ i,
      (t.enh.tuples.get i).1 = (t'.enh.tuples.get (e i)).1 ∧
      (t.enh.tuples.get i).2.1 = (t'.enh.tuples.get (e i)).2.1 ∧
      Shape.Equiv (t.enh.tuples.get i).2.2.1 (t'.enh.tuples.get (e i)).2.2.1 ∧
      Shape.Equiv (t.enh.tuples.get i).2.2.2 (t'.enh.tuples.get (e i)).2.2.2 := by
  show t.layer = t'.layer ∧ Shape.Equiv (.type2 _ .triv) (.type2 _ .triv) ↔ _
  rw [Shape.equiv_type2_iff]
  exact and_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, .triv⟩⟩

theorem EnhTree.zcount_shape (t : EnhTree) : t.shape.zcount = t.Z.card := by
  rw [EnhTree.shape, Shape.zcount, Shape.zcount, add_zero, EnhTree.tuples,
    chainTuples_zcount _ _ t.dominant]
  exact countP_mem_eq_card (tree_specialList_nodup t.code t.sign)
    ((tree_mem_specialSets_iff _ _ _).1 t.special)

/-- Equivalent enhanced dominant trees have the same order and the same `|Z|`. -/
theorem LayEnhTree.size_card_eq_of_equiv {t t' : LayEnhTree} (h : t ≈ t') :
    t.enh.code.size = t'.enh.code.size ∧ t.enh.Z.card = t'.enh.Z.card := by
  refine ⟨?_, ?_⟩
  · have := Shape.Equiv.size_eq h.2
    simpa only [EnhTree.shape, EnhTree.tuples, Shape.size, chainTuples_size _ _ t.enh.dominant,
      chainTuples_size _ _ t'.enh.dominant, add_zero] using this
  · rw [← t.enh.zcount_shape, ← t'.enh.zcount_shape]
    exact Shape.Equiv.zcount_eq h.2

end WaveTurbulence.Links
