/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Shapes: the recursive data compared by the equivalence of enhanced dominant couples (packet C5)

DH21 Def 4.18 (`equivcpl`, L862–L873), TARGET Defs 6.4–6.5 (`defencpl`, `defentree`, L1126–L1144)
and DH21 Def 4.21 (`equcodetree`, L883–L886) compare objects recursively by the same pattern:

* the trivial object is only equivalent to itself, objects of different types never are;
* type 1: an ordered triple of sub-objects, compared componentwise;
* type 2: a collection of tuples `(𝙸, 𝚌, 𝒳₁, 𝒳₂)` (`𝙸 ∈ {0,1}`, `𝚌 ∈ {1,2,3}`, `𝒳_ι` sub-objects),
  compared **up to permutation** with componentwise equivalence, and a tail object `𝒴`, compared
  directly.

`Shape` records exactly these data (a mutual inductive with its own tuple lists `Tuples`; the
first code digit `𝚌 ∈ {1,2,3}` is stored as `Fin 3`, i.e. `𝚌 - 1`), and `Shape.Equiv` is the
recursive comparison: the bijection `e` between tuple positions is the permutation of the source.
It is an equivalence relation (`Shape.Equiv.refl/symm/trans`, `Shape.setoid`) and preserves the
half-order data `size` (`n(𝒬)`) and the special count `zcount` (`|Z|`).
-/

@[expose] public section

namespace WaveTurbulence.Links

mutual
/-- The recursive data of an (enhanced dominant) couple, tree, or encoded tree. -/
inductive Shape : Type
  /-- the trivial object -/
  | triv : Shape
  /-- type 1: the three sub-objects, in order -/
  | type1 (X₁ X₂ X₃ : Shape) : Shape
  /-- type 2: the tuples `(𝙸, 𝚌 - 1, 𝒳₁, 𝒳₂)` and the tail `𝒴` -/
  | type2 (tuples : Tuples) (Y : Shape) : Shape

/-- Lists of tuples `(𝙸, 𝚌 - 1, 𝒳₁, 𝒳₂)`. -/
inductive Tuples : Type
  | nil : Tuples
  | cons (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) (rest : Tuples) : Tuples
end

namespace Tuples

/-- The number of tuples. -/
def length : Tuples → ℕ
  | nil => 0
  | cons _ _ _ _ rest => rest.length + 1

/-- The `i`-th tuple. -/
def get : (L : Tuples) → Fin L.length → Bool × Fin 3 × Shape × Shape
  | nil, i => i.elim0
  | cons I c X₁ X₂ _, ⟨0, _⟩ => (I, c, X₁, X₂)
  | cons _ _ _ _ rest, ⟨k + 1, h⟩ => rest.get ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Concatenation. -/
def append : Tuples → Tuples → Tuples
  | nil, L' => L'
  | cons I c X₁ X₂ rest, L' => cons I c X₁ X₂ (rest.append L')

/-- Sums over the tuples, by position. -/
theorem sum_cons {M : Type*} [AddCommMonoid M] (I : Bool) (c : Fin 3) (X₁ X₂ : Shape)
    (rest : Tuples) (f : Bool × Fin 3 × Shape × Shape → M) :
    ∑ i, f ((cons I c X₁ X₂ rest).get i) = f (I, c, X₁, X₂) + ∑ i, f (rest.get i) := by
  show ∑ i : Fin (rest.length + 1), _ = _
  rw [Fin.sum_univ_succ]
  rfl

end Tuples

/-! ### The equivalence -/

/-- **The recursive equivalence of shapes** (DH21 Def 4.18, TARGET Defs 6.4–6.5, DH21 Def 4.21):
trivial only with trivial; type 1 componentwise; type 2 when the tuples correspond under a bijection
`e` with equal `𝙸`, equal `𝚌` and equivalent sub-objects, and the tails are equivalent. -/
inductive Shape.Equiv : Shape → Shape → Prop
  | triv : Shape.Equiv .triv .triv
  | type1 {a b c a' b' c' : Shape} : Shape.Equiv a a' → Shape.Equiv b b' → Shape.Equiv c c' →
      Shape.Equiv (.type1 a b c) (.type1 a' b' c')
  | type2 {L L' : Tuples} {Y Y' : Shape} (e : Fin L.length ≃ Fin L'.length)
      (hI : ∀ i, (L.get i).1 = (L'.get (e i)).1)
      (hc : ∀ i, (L.get i).2.1 = (L'.get (e i)).2.1)
      (h₁ : ∀ i, Shape.Equiv (L.get i).2.2.1 (L'.get (e i)).2.2.1)
      (h₂ : ∀ i, Shape.Equiv (L.get i).2.2.2 (L'.get (e i)).2.2.2)
      (hY : Shape.Equiv Y Y') : Shape.Equiv (.type2 L Y) (.type2 L' Y')

mutual
theorem Shape.equiv_refl : (s : Shape) → Shape.Equiv s s
  | .triv => .triv
  | .type1 a b c => .type1 (Shape.equiv_refl a) (Shape.equiv_refl b) (Shape.equiv_refl c)
  | .type2 L Y => .type2 (_root_.Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
      (fun i => (Tuples.equiv_refl L i).1) (fun i => (Tuples.equiv_refl L i).2) (Shape.equiv_refl Y)

theorem Tuples.equiv_refl : (L : Tuples) → ∀ i,
    Shape.Equiv (L.get i).2.2.1 (L.get i).2.2.1 ∧ Shape.Equiv (L.get i).2.2.2 (L.get i).2.2.2
  | .nil, i => i.elim0
  | .cons _ _ X₁ X₂ _, ⟨0, _⟩ => ⟨Shape.equiv_refl X₁, Shape.equiv_refl X₂⟩
  | .cons _ _ _ _ rest, ⟨k + 1, h⟩ => Tuples.equiv_refl rest ⟨k, Nat.lt_of_succ_lt_succ h⟩
end

theorem Shape.Equiv.symm {s t : Shape} (h : Shape.Equiv s t) : Shape.Equiv t s := by
  induction h with
  | triv => exact .triv
  | type1 _ _ _ ih₁ ih₂ ih₃ => exact .type1 ih₁ ih₂ ih₃
  | @type2 L L' Y Y' e hI hc _ _ _ ih₁ ih₂ ihY =>
    refine .type2 e.symm (fun j => ?_) (fun j => ?_) (fun j => ?_) (fun j => ?_) ihY
    · have := hI (e.symm j); rw [e.apply_symm_apply] at this; exact this.symm
    · have := hc (e.symm j); rw [e.apply_symm_apply] at this; exact this.symm
    · have := ih₁ (e.symm j); rwa [e.apply_symm_apply] at this
    · have := ih₂ (e.symm j); rwa [e.apply_symm_apply] at this

theorem Shape.Equiv.trans {s t u : Shape} (h₁ : Shape.Equiv s t) (h₂ : Shape.Equiv t u) :
    Shape.Equiv s u := by
  induction h₁ generalizing u with
  | triv => exact h₂
  | type1 _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | type1 k₁ k₂ k₃ => exact .type1 (ih₁ k₁) (ih₂ k₂) (ih₃ k₃)
  | type2 e hI hc _ _ _ ih₁ ih₂ ihY =>
    cases h₂ with
    | type2 e' hI' hc' k₁ k₂ kY =>
      exact .type2 (e.trans e') (fun i => (hI i).trans (hI' (e i)))
        (fun i => (hc i).trans (hc' (e i))) (fun i => ih₁ i (k₁ (e i))) (fun i => ih₂ i (k₂ (e i)))
        (ihY kY)

/-- Shapes up to equivalence. -/
def Shape.setoid : Setoid Shape where
  r := Shape.Equiv
  iseqv := ⟨Shape.equiv_refl, Shape.Equiv.symm, Shape.Equiv.trans⟩

/-! ### Invariants: order and special count -/

mutual
/-- The order `n` (number of branching nodes) of the object with this shape: type 1 adds the two
roots, every type-2 tuple adds the two nodes `𝔫_{2j-1}, 𝔫_{2j}` of its pair. -/
def Shape.size : Shape → ℕ
  | .triv => 0
  | .type1 a b c => a.size + b.size + c.size + 2
  | .type2 L Y => L.size + Y.size

/-- The order contributed by a list of tuples. -/
def Tuples.size : Tuples → ℕ
  | .nil => 0
  | .cons _ _ X₁ X₂ rest => X₁.size + X₂.size + 2 + rest.size
end

mutual
/-- The number of special nodes in `Z` (`|Z|`): the tuples with `𝙸 = 1`, recursively. -/
def Shape.zcount : Shape → ℕ
  | .triv => 0
  | .type1 a b c => a.zcount + b.zcount + c.zcount
  | .type2 L Y => L.zcount + Y.zcount

/-- The special count of a list of tuples. -/
def Tuples.zcount : Tuples → ℕ
  | .nil => 0
  | .cons I _ X₁ X₂ rest => (if I then 1 else 0) + X₁.zcount + X₂.zcount + rest.zcount
end

theorem Tuples.zcount_eq_sum : (L : Tuples) →
    L.zcount = ∑ i, ((if (L.get i).1 then 1 else 0) + (L.get i).2.2.1.zcount +
      (L.get i).2.2.2.zcount)
  | .nil => by show (0 : ℕ) = ∑ i : Fin 0, _; simp
  | .cons I c X₁ X₂ rest => by
    rw [Tuples.sum_cons (f := fun t => (if t.1 then 1 else 0) + t.2.2.1.zcount + t.2.2.2.zcount),
      ← Tuples.zcount_eq_sum rest]
    simp [Tuples.zcount]

/-- **Equivalent enhanced objects have the same number of special nodes** (DH21 L873:
`|Z| = |Z'|`). -/
theorem Shape.Equiv.zcount_eq {s t : Shape} (h : Shape.Equiv s t) : s.zcount = t.zcount := by
  induction h with
  | triv => rfl
  | type1 _ _ _ ih₁ ih₂ ih₃ => simp [Shape.zcount, ih₁, ih₂, ih₃]
  | @type2 L L' Y Y' e hI _ _ _ _ ih₁ ih₂ ihY =>
    simp only [Shape.zcount, Tuples.zcount_eq_sum, ihY]
    congr 1
    rw [← Equiv.sum_comp e (fun j => (if (L'.get j).1 then 1 else 0) + (L'.get j).2.2.1.zcount +
      (L'.get j).2.2.2.zcount)]
    exact Finset.sum_congr rfl fun i _ => by rw [hI i, ih₁ i, ih₂ i]

end WaveTurbulence.Links
