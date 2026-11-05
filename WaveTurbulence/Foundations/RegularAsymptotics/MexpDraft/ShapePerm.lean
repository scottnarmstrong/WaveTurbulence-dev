/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.SumPeel

/-!
# Class data of prepended codes

DH21's equivalence (Def 4.18) compares the tuples of the two chains of a type 2 couple as one unordered family.

* `TEq`: two tuple lists correspond under a bijection of positions (the type 2 clause of `Shape.Equiv`);
  `TEq.cons`, `TEq.swap`, `TEq.append_cons`: a tuple of the `-` chain may be moved to the front.
* `consShape`: put a tuple in front of a class; `shape_prepP`, `shape_prepM_equiv`: the class of a code with a
  new top pair on either chain is `consShape` of the class of the rest; `consShape_congr`: `consShape` respects
  the equivalence.
* `sw_prepP`, `sw_prepM`, `wt_add`: the special weights of the two prepended codes differ by the sign of the new
  chosen node, and `wt(+, 𝙸) + wt(-, 𝙸) = 2·[𝙸 = 0]` (the cancellation `1 + (-1)^𝙸 = 0` of DH21 Prop 7.8 with the
  F61 weights).
-/

@[expose] public section

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links

/-- Two tuple lists correspond under a bijection of positions, with equal `𝙸`, equal `𝚌` and equivalent
sub-classes. -/
def TEq (L L' : Tuples) : Prop :=
  ∃ e : Fin L.length ≃ Fin L'.length, ∀ i,
    (L.get i).1 = (L'.get (e i)).1 ∧ (L.get i).2.1 = (L'.get (e i)).2.1 ∧
    Shape.Equiv (L.get i).2.2.1 (L'.get (e i)).2.2.1 ∧ Shape.Equiv (L.get i).2.2.2 (L'.get (e i)).2.2.2

theorem equiv_type2_iff_TEq (L L' : Tuples) (Y Y' : Shape) :
    Shape.Equiv (.type2 L Y) (.type2 L' Y') ↔ TEq L L' ∧ Shape.Equiv Y Y' :=
  Shape.equiv_type2_iff L L' Y Y'

theorem TEq.refl (L : Tuples) : TEq L L :=
  ⟨Equiv.refl _, fun i => ⟨rfl, rfl, (Tuples.equiv_refl L i).1, (Tuples.equiv_refl L i).2⟩⟩

theorem TEq.trans {L L' L'' : Tuples} (h : TEq L L') (h' : TEq L' L'') : TEq L L'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun i => ⟨(he i).1.trans (he' (e i)).1, (he i).2.1.trans (he' (e i)).2.1,
    (he i).2.2.1.trans (he' (e i)).2.2.1, (he i).2.2.2.trans (he' (e i)).2.2.2⟩⟩

theorem get_cons_succ' (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) (rest : Tuples)
    (i : Fin rest.length) : (Tuples.cons I c X₁ X₂ rest).get i.succ = rest.get i := by
  obtain ⟨i, hi⟩ := i
  rfl

/-- The bijection `0 ↦ 0`, `i + 1 ↦ e(i) + 1`. -/
def consEquiv {n m : ℕ} (e : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr e).trans (finSuccEquiv m).symm)

theorem consEquiv_zero {n m : ℕ} (e : Fin n ≃ Fin m) : consEquiv e 0 = 0 := by
  simp [consEquiv, finSuccEquiv_zero, finSuccEquiv_symm_none]

theorem consEquiv_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : Fin n) : consEquiv e i.succ = (e i).succ := by
  simp [consEquiv, finSuccEquiv_succ, finSuccEquiv_symm_some]

theorem TEq.cons {L L' : Tuples} (h : TEq L L') (I : Bool) (c : Fin 3) {X₁ X₁' X₂ X₂' : Shape}
    (h₁ : Shape.Equiv X₁ X₁') (h₂ : Shape.Equiv X₂ X₂') :
    TEq (.cons I c X₁ X₂ L) (.cons I c X₁' X₂' L') := by
  obtain ⟨e, he⟩ := h
  refine ⟨consEquiv e, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · erw [consEquiv_zero]
    exact ⟨rfl, rfl, h₁, h₂⟩
  · erw [consEquiv_succ, get_cons_succ' I c X₁ X₂ L j, get_cons_succ' I c X₁' X₂' L' (e j)]
    exact he j

theorem TEq.swap (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) (I' : Bool) (c' : Fin 3) (X₁' X₂' : Shape)
    (L : Tuples) :
    TEq (.cons I c X₁ X₂ (.cons I' c' X₁' X₂' L)) (.cons I' c' X₁' X₂' (.cons I c X₁ X₂ L)) := by
  refine ⟨(Equiv.swap (0 : Fin (L.length + 1 + 1)) (1 : Fin (L.length + 1 + 1)) :), fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · erw [Equiv.swap_apply_left]
    exact ⟨rfl, rfl, Shape.equiv_refl _, Shape.equiv_refl _⟩
  · refine Fin.cases ?_ (fun k => ?_) j
    · erw [show (Fin.succ (0 : Fin (L.length + 1)) : Fin (L.length + 1 + 1)) = 1 from rfl,
        Equiv.swap_apply_right]
      exact ⟨rfl, rfl, Shape.equiv_refl _, Shape.equiv_refl _⟩
    · have h0 : (k.succ.succ : Fin (L.length + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (L.length + 1 + 1)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      erw [Equiv.swap_apply_of_ne_of_ne h0 h1, get_cons_succ' I c X₁ X₂ (.cons I' c' X₁' X₂' L) k.succ,
        get_cons_succ' I' c' X₁' X₂' L k, get_cons_succ' I' c' X₁' X₂' (.cons I c X₁ X₂ L) k.succ,
        get_cons_succ' I c X₁ X₂ L k]
      exact ⟨rfl, rfl, Shape.equiv_refl _, Shape.equiv_refl _⟩

/-- **A tuple of the second list may be moved to the front.** -/
theorem TEq.append_cons (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) :
    (L₁ L₂ : Tuples) → TEq (L₁.append (.cons I c X₁ X₂ L₂)) (.cons I c X₁ X₂ (L₁.append L₂))
  | .nil, _ => TEq.refl _
  | .cons I' c' X₁' X₂' L₁, L₂ =>
    ((TEq.append_cons I c X₁ X₂ L₁ L₂).cons I' c' (Shape.equiv_refl X₁') (Shape.equiv_refl X₂')).trans
      (TEq.swap I' c' X₁' X₂' I c X₁ X₂ (L₁.append L₂))

/-! ### Prepending a tuple to a class -/

/-- Put the tuple `(𝙸, 𝚌 - 1, X₁, X₂)` in front of a class (starting a type 2 class on a trivial or type 1
tail). -/
def consShape (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) : Shape → Shape
  | .triv => .type2 (.cons I c X₁ X₂ .nil) .triv
  | .type1 a b d => .type2 (.cons I c X₁ X₂ .nil) (.type1 a b d)
  | .type2 L Y => .type2 (.cons I c X₁ X₂ L) Y

theorem shape_prepP (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    (prepP m I er eg e').shape = consShape I m.c er.shape eg.shape e'.shape := by
  cases e' <;> rfl

theorem shape_prepM_equiv (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    Shape.Equiv (prepM m I er eg e').shape (consShape I m.c er.shape eg.shape e'.shape) := by
  cases e' with
  | triv => exact Shape.equiv_refl _
  | type1 => exact Shape.equiv_refl _
  | type2 X Y L =>
    show Shape.Equiv (.type2 (X.tuples.append (.cons I m.c er.shape eg.shape Y.tuples)) L.shape)
      (.type2 (.cons I m.c er.shape eg.shape (X.tuples.append Y.tuples)) L.shape)
    rw [equiv_type2_iff_TEq]
    exact ⟨TEq.append_cons I m.c er.shape eg.shape X.tuples Y.tuples, Shape.equiv_refl _⟩

/-- **`consShape` respects the equivalence** in each argument. -/
theorem consShape_congr (I : Bool) (c : Fin 3) {X₁ X₁' X₂ X₂' S S' : Shape} (h₁ : Shape.Equiv X₁ X₁')
    (h₂ : Shape.Equiv X₂ X₂') (h : Shape.Equiv S S') :
    Shape.Equiv (consShape I c X₁ X₂ S) (consShape I c X₁' X₂' S') := by
  cases h with
  | triv =>
    rw [consShape, consShape, equiv_type2_iff_TEq]
    exact ⟨(TEq.refl _).cons I c h₁ h₂, .triv⟩
  | type1 a b d =>
    rw [consShape, consShape, equiv_type2_iff_TEq]
    exact ⟨(TEq.refl _).cons I c h₁ h₂, .type1 a b d⟩
  | type2 e hI hc k₁ k₂ hY =>
    rw [consShape, consShape, equiv_type2_iff_TEq]
    exact ⟨TEq.cons ⟨e, fun i => ⟨hI i, hc i, k₁ i, k₂ i⟩⟩ I c h₁ h₂, hY⟩

theorem zcount_consShape (I : Bool) (c : Fin 3) (X₁ X₂ S : Shape) :
    (consShape I c X₁ X₂ S).zcount = (if I then 1 else 0) + X₁.zcount + X₂.zcount + S.zcount := by
  cases S <;> simp [consShape, Shape.zcount, Tuples.zcount, add_assoc]

theorem netSign_consShape (I : Bool) (c : Fin 3) (X₁ X₂ S : Shape) :
    (consShape I c X₁ X₂ S).netSign = codeSign c * X₁.netSign * X₂.netSign * S.netSign := by
  cases S <;> simp [consShape, Shape.netSign, Tuples.netSign, mul_assoc]

/-! ### Special weights of prepended codes -/

theorem sw_prepP (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    (prepP m I er eg e').sw = wt 1 I * er.sw * eg.sw * e'.sw := by
  cases e' with
  | type2 => simp only [prepP, ECpl.sw, EChain.sw]; ring
  | _ => simp only [prepP, ECpl.sw, EChain.sw, mul_one]

theorem sw_prepM (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    (prepM m I er eg e').sw = wt (-1) I * er.sw * eg.sw * e'.sw := by
  cases e' <;> simp only [prepM, ECpl.sw, EChain.sw, mul_one] <;> ring

/-- **The two chains cancel the `p.v.` weight** (DH21 Prop 7.8: `1 + (-1)^𝙸 = 0` for `𝙸 = 1`, with the F61
weights `(∓π i)^{-1}`). -/
theorem wt_add (I : Bool) : wt 1 I + wt (-1) I = if I then 0 else 2 := by
  cases I
  · simp [wt]; norm_num
  · simp only [wt, ↓reduceIte, Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg,
      neg_mul, neg_neg]
    rw [inv_neg, neg_add_cancel]

end WaveTurbulence.Mexp
