/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.CodeConj

/-!
# Leaf pairs and links of the conjugate code (CONJ-COH)

For an address map `φ` compatible with extension (`φ (addrExt a p) = addrExt (φ a) p`; e.g. relabelling the tree
index by a permutation of the roots):
* `mem_pairsAt_conjCpl`: the leaf pairs `(+ leaf, - leaf)` of `conjCpl Q` placed at `(φ b, φ a)` are exactly the
  swapped images `(φ y, φ x)` of the leaf pairs `(x, y)` of `Q` placed at `(a, b)`;
* `links_countP_conjCpl`: for a symmetric predicate `P`, the links of `conjCpl Q` at `(φ b, φ a)` satisfy `P` in
  the same number as the links of `Q` at `(a, b)` satisfy `P ∘ φ` (link orientation is irrelevant for `P`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree

/-- An address map commuting with path extension. -/
def AddrCompat {w v : ℕ} (φ : Fin w × Path → Fin v × Path) : Prop :=
  ∀ a p, φ (addrExt a p) = addrExt (φ a) p

theorem neg_one_ne_one_units : ¬ ((-1 : ℤˣ) = 1) := by decide

variable {w v : ℕ} {φ : Fin w × Path → Fin v × Path}

mutual
theorem mem_pairsAt_conjCpl (hφ : AddrCompat φ) : ∀ (Q : RegCpl) (a b : Fin w × Path)
    (p : (Fin v × Path) × (Fin v × Path)),
    p ∈ (conjCpl Q).pairsAt (φ b) (φ a) ↔ ∃ q ∈ Q.pairsAt a b, p = (φ q.2, φ q.1)
  | .triv, a, b, p => by
    simp [conjCpl, RegCpl.pairsAt]
  | .type1 c Q₁ Q₂ Q₃, a, b, p => by
    have i1 := mem_pairsAt_conjCpl hφ Q₁
    have i2 := mem_pairsAt_conjCpl hφ Q₂
    have i3 := mem_pairsAt_conjCpl hφ Q₃
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have p00 : MiniCplCode.partner 0 0 = 0 := by decide
    have p02 : MiniCplCode.partner 0 2 = 2 := by decide
    have p10 : MiniCplCode.partner 1 0 = 2 := by decide
    have p12 : MiniCplCode.partner 1 2 = 0 := by decide
    obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    · have h0 : ((0 : MiniCplCode) = 0) := rfl
      simp only [conjCpl, ite_true, RegCpl.pairsAt, List.mem_append, p00, p02, e1, i1, i2, i3,
        or_and_right, exists_or]
    · have h0 : ¬ ((1 : MiniCplCode) = 0) := by decide
      simp only [conjCpl, h0, ite_false, RegCpl.pairsAt, List.mem_append, p10, p12, e1, i1, i2, i3,
        or_and_right, exists_or]
      constructor <;> rintro ((h | h) | h)
      exacts [Or.inr h, Or.inl (Or.inr h), Or.inl (Or.inl h), Or.inr h, Or.inl (Or.inr h), Or.inl (Or.inl h)]
  | .type2 Xp Xm Qlp, a, b, p => by
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have iq := mem_pairsAt_conjCpl hφ Qlp
    have hXm : ∀ (b : Fin w × Path) p, p ∈ (conjChain Xm).pairsAt 1 (φ b) ↔
        ∃ q ∈ Xm.pairsAt (-1) b, p = (φ q.2, φ q.1) := fun b p => by
      simpa using mem_pairsAt_conjChain hφ Xm (-1) b p
    have hXp : ∀ (a : Fin w × Path) p, p ∈ (conjChain Xp).pairsAt (-1) (φ a) ↔
        ∃ q ∈ Xp.pairsAt 1 a, p = (φ q.2, φ q.1) := fun a p => 
      mem_pairsAt_conjChain hφ Xp 1 a p
    simp only [conjCpl, RegCpl.pairsAt, List.mem_append, lonePath_conjChain, e1, iq, hXm, hXp,
      or_and_right, exists_or]
    exact or_congr_left or_comm
termination_by structural Q => Q

theorem mem_pairsAt_conjChain (hφ : AddrCompat φ) : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (p : (Fin v × Path) × (Fin v × Path)),
    p ∈ (conjChain X).pairsAt (-ζ) (φ a) ↔ ∃ q ∈ X.pairsAt ζ a, p = (φ q.2, φ q.1)
  | .nil, ζ, a, p => by
    simp [conjChain, RegChain.pairsAt]
  | .pair m Qr Qg inner rest, ζ, a, p => by
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have iR := mem_pairsAt_conjCpl hφ Qr
    have iG := mem_pairsAt_conjCpl hφ Qg
    have iI : ∀ ζ' (a' : Fin w × Path) p, p ∈ (conjChain inner).pairsAt (-ζ') (φ a') ↔
        ∃ q ∈ inner.pairsAt ζ' a', p = (φ q.2, φ q.1) := fun ζ' a' p =>
      mem_pairsAt_conjChain hφ inner ζ' a' p
    have iS : ∀ ζ' (a' : Fin w × Path) p, p ∈ (conjChain rest).pairsAt (-ζ') (φ a') ↔
        ∃ q ∈ rest.pairsAt ζ' a', p = (φ q.2, φ q.1) := fun ζ' a' p =>
      mem_pairsAt_conjChain hφ rest ζ' a' p
    rcases Int.units_eq_one_or (slotSign ζ m.red.1) with hr | hr <;>
    rcases Int.units_eq_one_or (slotSign ζ m.green.1) with hg | hg <;>
    · simp only [conjChain, RegChain.pairsAt, slotSign_neg, hr, hg, neg_one_ne_one_units, neg_neg,
        ite_true, ite_false, lonePath_conjChain, e1, List.mem_append, iR, iG, iI, iS,
        or_and_right, exists_or]
termination_by structural X => X
end


mutual
theorem links_countP_conjCpl (hφ : AddrCompat φ) (P : (Fin v × Path) → (Fin v × Path) → Bool)
    (hP : ∀ x y, P x y = P y x) : ∀ (Q : RegCpl) (a b : Fin w × Path),
    ((conjCpl Q).linksAt (φ b) (φ a)).countP (fun l => P l.1 l.2) =
      (Q.linksAt a b).countP (fun l => P (φ l.1) (φ l.2))
  | .triv, a, b => by
    simp [conjCpl, RegCpl.linksAt]
  | .type1 c Q₁ Q₂ Q₃, a, b => by
    have i1 := links_countP_conjCpl hφ P hP Q₁
    have i2 := links_countP_conjCpl hφ P hP Q₂
    have i3 := links_countP_conjCpl hφ P hP Q₃
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have p00 : MiniCplCode.partner 0 0 = 0 := by decide
    have p02 : MiniCplCode.partner 0 2 = 2 := by decide
    have p10 : MiniCplCode.partner 1 0 = 2 := by decide
    have p12 : MiniCplCode.partner 1 2 = 0 := by decide
    obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
    · simp only [conjCpl, ite_true, RegCpl.linksAt, List.countP_cons, List.countP_append, p00, p02, e1,
        i1, i2, i3, hP (φ b) (φ a)]
    · have h0 : ¬ ((1 : MiniCplCode) = 0) := by decide
      simp only [conjCpl, h0, ite_false, RegCpl.linksAt, List.countP_cons, List.countP_append, p10, p12,
        e1, i1, i2, i3, hP (φ b) (φ a)]
      omega
  | .type2 Xp Xm Qlp, a, b => by
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have iq := links_countP_conjCpl hφ P hP Qlp
    have hXm : ∀ (b : Fin w × Path), ((conjChain Xm).linksAt 1 (φ b)).countP (fun l => P l.1 l.2) =
        (Xm.linksAt (-1) b).countP (fun l => P (φ l.1) (φ l.2)) := fun b => by
      simpa using links_countP_conjChain hφ P hP Xm (-1) b
    have hXp : ∀ (a : Fin w × Path), ((conjChain Xp).linksAt (-1) (φ a)).countP (fun l => P l.1 l.2) =
        (Xp.linksAt 1 a).countP (fun l => P (φ l.1) (φ l.2)) := fun a =>
      links_countP_conjChain hφ P hP Xp 1 a
    simp only [conjCpl, RegCpl.linksAt, List.countP_append, lonePath_conjChain, e1, iq, hXm, hXp]
    omega
termination_by structural Q => Q

theorem links_countP_conjChain (hφ : AddrCompat φ) (P : (Fin v × Path) → (Fin v × Path) → Bool)
    (hP : ∀ x y, P x y = P y x) : ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path),
    ((conjChain X).linksAt (-ζ) (φ a)).countP (fun l => P l.1 l.2) =
      (X.linksAt ζ a).countP (fun l => P (φ l.1) (φ l.2))
  | .nil, ζ, a => by
    simp [conjChain, RegChain.linksAt]
  | .pair m Qr Qg inner rest, ζ, a => by
    have e1 : ∀ x y, (addrExt (φ x) y) = φ (addrExt x y) := fun x y => (hφ x y).symm
    have iR := links_countP_conjCpl hφ P hP Qr
    have iG := links_countP_conjCpl hφ P hP Qg
    have iI : ∀ ζ' (a' : Fin w × Path), ((conjChain inner).linksAt (-ζ') (φ a')).countP
        (fun l => P l.1 l.2) = (inner.linksAt ζ' a').countP (fun l => P (φ l.1) (φ l.2)) :=
      fun ζ' a' => links_countP_conjChain hφ P hP inner ζ' a'
    have iS : ∀ ζ' (a' : Fin w × Path), ((conjChain rest).linksAt (-ζ') (φ a')).countP
        (fun l => P l.1 l.2) = (rest.linksAt ζ' a').countP (fun l => P (φ l.1) (φ l.2)) :=
      fun ζ' a' => links_countP_conjChain hφ P hP rest ζ' a'
    rcases Int.units_eq_one_or (slotSign ζ m.red.1) with hr | hr <;>
    rcases Int.units_eq_one_or (slotSign ζ m.green.1) with hg | hg <;>
    · simp only [conjChain, RegChain.linksAt, slotSign_neg, hr, hg, neg_one_ne_one_units, neg_neg,
        ite_true, ite_false, lonePath_conjChain, e1, List.countP_cons, List.countP_append, iR, iG, iI, iS]
termination_by structural X => X
end

end WaveTurbulence.ConjCoh
