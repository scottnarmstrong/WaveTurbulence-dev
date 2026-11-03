/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

/-!
# Counting pairings by their label fibers

The finite combinatorial count used in DH21 Lemma A.2. `Nat.card` keeps the
cardinality formulas independent of choices of `Fintype` instances on fibers.
-/

public section

open scoped BigOperators Classical
noncomputable section
namespace WaveTurbulence.GaussianPairings

/-- Restrict a label-preserving equivalence to one fiber. -/
@[expose] def fiberEquivOfCompatible {A B C : Type*} (f : A → C) (g : B → C)
    (e : A ≃ B) (he : ∀ a, g (e a) = f a) (c : C) :
    {a // f a = c} ≃ {b // g b = c} where
  toFun a := ⟨e a, (he a).trans a.property⟩
  invFun b := ⟨e.symm b, by rw [← he, e.apply_symm_apply]; exact b.property⟩
  left_inv a := by ext; exact e.symm_apply_apply a
  right_inv b := by ext; exact e.apply_symm_apply b

/-- A label-preserving bijection is the same as one bijection on each label fiber. -/
@[expose] def compatibleEquivEquiv {A B C : Type*} (f : A → C) (g : B → C) :
    {e : A ≃ B // ∀ a, g (e a) = f a} ≃
      (∀ c, {a // f a = c} ≃ {b // g b = c}) where
  toFun e := fiberEquivOfCompatible f g e.1 e.2
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv e := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rfl
  right_inv e := by
    funext c
    apply Equiv.ext
    intro a
    rcases a with ⟨a, rfl⟩
    rfl

lemma card_equiv_eq_ite {A B : Type*} [Fintype A] [Fintype B] :
    Fintype.card (A ≃ B) = if Fintype.card A = Fintype.card B then (Fintype.card A).factorial else 0 := by
  classical
  by_cases h : Fintype.card A = Fintype.card B
  · rw [ite_eq_left h]
    exact Fintype.card_equiv (Fintype.equivOfCardEq h)
  · rw [ite_eq_right h]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun e => h (Fintype.card_congr e)⟩

lemma nat_card_equiv_eq_ite {A B : Type*} [Finite A] [Finite B] :
    Nat.card (A ≃ B) = if Nat.card A = Nat.card B then (Nat.card A).factorial else 0 := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite B
  simpa only [Nat.card_eq_fintype_card] using (card_equiv_eq_ite (A := A) (B := B))

lemma card_compatible_equiv {A B C : Type*} [Finite A] [Finite B] [Fintype C]
    (f : A → C) (g : B → C) :
    Nat.card {e : A ≃ B // ∀ a, g (e a) = f a} =
      ∏ c, if Nat.card {a // f a = c} = Nat.card {b // g b = c}
        then (Nat.card {a // f a = c}).factorial else 0 := by
  calc
    _ = Nat.card (∀ c, {a // f a = c} ≃ {b // g b = c}) :=
      Nat.card_congr (compatibleEquivEquiv f g)
    _ = ∏ c, Nat.card ({a // f a = c} ≃ {b // g b = c}) := Nat.card_pi
    _ = _ := Finset.prod_congr rfl fun c _ => nat_card_equiv_eq_ite
end WaveTurbulence.GaussianPairings

namespace WaveTurbulence.GaussianPairings

open scoped Classical

/-- Positions in a finite set carrying the indicated sign. -/
abbrev SignedPositions {J : Type*} (s : Finset J) (ζ : J → Bool) (ε : Bool) :=
  {j : s // ζ j = ε}

/-- An opposite-sign pairing, represented by the bijection from positive to negative positions. -/
abbrev SignedPairing {J : Type*} (s : Finset J) (ζ : J → Bool) :=
  SignedPositions s ζ true ≃ SignedPositions s ζ false

/-- The Gaussian label of a signed position, valued in the finite set of labels occurring. -/
@[expose] def positionLabel {J ι : Type*} [DecidableEq ι] (s : Finset J) (k : J → ι)
    (ζ : J → Bool) (ε : Bool) (a : SignedPositions s ζ ε) : s.image k :=
  ⟨k a.1, Finset.mem_image_of_mem k a.1.property⟩

/-- A label fiber of signed positions is the corresponding filtered set of positions. -/
@[expose] def positionLabelFiberEquiv {J ι : Type*} [DecidableEq ι]
    (s : Finset J) (k : J → ι) (ζ : J → Bool) (ε : Bool) (i : s.image k) :
    {a : SignedPositions s ζ ε // positionLabel s k ζ ε a = i} ≃
      {j // j ∈ s.filter (fun j => k j = i.1 ∧ ζ j = ε)} where
  toFun a := ⟨a.1.1, Finset.mem_filter.mpr ⟨a.1.1.property,
    congrArg Subtype.val a.2, a.1.property⟩⟩
  invFun j := ⟨⟨⟨j.1, (Finset.mem_filter.mp j.2).1⟩, (Finset.mem_filter.mp j.2).2.2⟩,
    Subtype.ext (Finset.mem_filter.mp j.2).2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cardinality of a signed label fiber. -/
theorem card_positionLabel_fiber {J ι : Type*} [DecidableEq ι]
    (s : Finset J) (k : J → ι) (ζ : J → Bool) (ε : Bool) (i : s.image k) :
    Nat.card {a : SignedPositions s ζ ε // positionLabel s k ζ ε a = i} =
      (s.filter (fun j => k j = i.1 ∧ ζ j = ε)).card := by
  rw [Nat.card_congr (positionLabelFiberEquiv s k ζ ε i), Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-- The number of pairings whose two positions have equal Gaussian labels (DH21 Lemma A.2). -/
theorem card_compatible_signedPairing {J ι : Type*} [DecidableEq ι]
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    Nat.card {e : SignedPairing s ζ // ∀ a,
      positionLabel s k ζ false (e a) = positionLabel s k ζ true a} =
      ∏ i ∈ s.image k,
        if (s.filter (fun j => k j = i ∧ ζ j = true)).card =
            (s.filter (fun j => k j = i ∧ ζ j = false)).card
        then (s.filter (fun j => k j = i ∧ ζ j = true)).card.factorial else 0 := by
  rw [card_compatible_equiv (positionLabel s k ζ true) (positionLabel s k ζ false)]
  simp_rw [card_positionLabel_fiber]
  exact Finset.prod_coe_sort (s.image k) (fun i =>
    if (s.filter (fun j => k j = i ∧ ζ j = true)).card =
        (s.filter (fun j => k j = i ∧ ζ j = false)).card
    then (s.filter (fun j => k j = i ∧ ζ j = true)).card.factorial else 0)

end WaveTurbulence.GaussianPairings

namespace WaveTurbulence.GaussianPairings
open scoped Classical

/-- The product of equality indicators counts exactly the label-preserving bijections. -/
theorem sum_equiv_weight {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : A → C) (g : B → C) :
    (∑ e : A ≃ B, ∏ a, if g (e a) = f a then (1 : ℂ) else 0) =
      (Nat.card {e : A ≃ B // ∀ a, g (e a) = f a} : ℂ) := by
  simp only [Fintype.prod_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

end WaveTurbulence.GaussianPairings
