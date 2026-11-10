/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.JBPeel

/-!
# Sums over enhanced dominant couples, peeled at the top

A well-formed enhanced dominant couple of order `2(n+1)` is either of type 1, `(c, e₁, e₂, e₃)`, or of type 2;
a type 2 code has a top pair on its `+` chain, or on its `-` chain, or both, and removing it leaves a
well-formed code `e'`. With `n₁ + n₂ + n₃ = n` the orders of the three remaining pieces:

* `sum_t1Part`: `∑_{e ∈ ED (n+1)} t1Part H e = ∑_{(n₁,n₂,n₃)} ∑_c ∑_{e₁,e₂,e₃} H c e₁ e₂ e₃`;
* `sum_plusPart`, `sum_minusPart`: `∑_{e} plusPart H e = ∑_{(n₁,n₂,n₃)} ∑_{m, 𝙸} ∑_{e_r, e_g, e'} H m 𝙸 e_r e_g e'`
  (`e = prepP m 𝙸 e_r e_g e'`, resp. `prepM`);
* `weighted_JB_decomp`: `w(e) 𝒥ℬ*_e(t, t)` is the sum of its type 1, `+` and `-` parts (`JB_diag`).
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable {M : Type*} [AddCommMonoid M]

/-- The type 1 part of a function of enhanced codes. -/
def t1Part (H : MiniCplCode → ECpl → ECpl → ECpl → M) : ECpl → M
  | .triv => 0
  | .type1 c e₁ e₂ e₃ => H c e₁ e₂ e₃
  | .type2 .. => 0

/-- The `+` top-pair part: `H m 𝙸 e_r e_g e'` with `e'` the code with the `+` top pair removed. -/
def plusPart (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) : ECpl → M
  | .triv => 0
  | .type1 .. => 0
  | .type2 .nil _ _ => 0
  | .type2 (.pair m I er eg X) Y L => H m I er eg (mk2 X Y L)

/-- The `-` top-pair part. -/
def minusPart (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) : ECpl → M
  | .triv => 0
  | .type1 .. => 0
  | .type2 _ .nil _ => 0
  | .type2 X (.pair m I er eg Y) L => H m I er eg (mk2 X Y L)

/-! ### Well-formedness and size -/

theorem wf_prepP (m : MiniTreeCode) (I : Bool) {er eg e' : ECpl} (hr : er.wf = true) (hg : eg.wf = true)
    (he : e'.wf = true) : (prepP m I er eg e').wf = true := by
  cases e' <;> simp_all [prepP, ECpl.wf, EChain.wf, ECpl.isType2, EChain.isNil]

theorem wf_prepM (m : MiniTreeCode) (I : Bool) {er eg e' : ECpl} (hr : er.wf = true) (hg : eg.wf = true)
    (he : e'.wf = true) : (prepM m I er eg e').wf = true := by
  cases e' <;> simp_all [prepM, ECpl.wf, EChain.wf, ECpl.isType2, EChain.isNil]

theorem hsize_prepP (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    (prepP m I er eg e').hsize = er.hsize + eg.hsize + e'.hsize + 1 := by
  cases e' <;> simp [prepP, ECpl.hsize, EChain.hsize] <;> ring

theorem hsize_prepM (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) :
    (prepM m I er eg e').hsize = er.hsize + eg.hsize + e'.hsize + 1 := by
  cases e' <;> simp [prepM, ECpl.hsize, EChain.hsize] <;> ring

theorem hsize_mk2 (X Y : EChain) (L : ECpl) (h : X.isNil = true → Y.isNil = true → True := fun _ _ => trivial) :
    (mk2 X Y L).hsize = X.hsize + Y.hsize + L.hsize := by
  unfold mk2
  cases X <;> cases Y <;> simp [EChain.isNil, ECpl.hsize, EChain.hsize]

theorem wf_mk2' {X Y : EChain} {L : ECpl} (hX : X.wf = true) (hY : Y.wf = true) (hL : L.wf = true)
    (hL2 : L.isType2 = false) : (mk2 X Y L).wf = true := by
  unfold mk2
  split_ifs with h
  · exact hL
  · simp only [Bool.not_eq_true] at h
    simp [ECpl.wf, hX, hY, hL, hL2, h]

theorem plusPart_prepP (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) (m : MiniTreeCode) (I : Bool)
    (er eg : ECpl) {e' : ECpl} (he : e'.wf = true) : plusPart H (prepP m I er eg e') = H m I er eg e' := by
  cases e' with
  | triv => rfl
  | type1 => rfl
  | type2 X Y L =>
    simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at he
    simp only [prepP, plusPart, mk2, he.2, Bool.false_eq_true, ↓reduceIte]

theorem minusPart_prepM (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) (m : MiniTreeCode) (I : Bool)
    (er eg : ECpl) {e' : ECpl} (he : e'.wf = true) : minusPart H (prepM m I er eg e') = H m I er eg e' := by
  cases e' with
  | triv => rfl
  | type1 => rfl
  | type2 X Y L =>
    simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at he
    simp only [prepM, minusPart, mk2, he.2, Bool.false_eq_true, ↓reduceIte]

theorem prepP_inj {m m' : MiniTreeCode} {I I' : Bool} {er eg e' er' eg' e'' : ECpl} (he : e'.wf = true)
    (he' : e''.wf = true) (h : prepP m I er eg e' = prepP m' I' er' eg' e'') :
    m = m' ∧ I = I' ∧ er = er' ∧ eg = eg' ∧ e' = e'' := by
  have h1 := congrArg (plusPart fun m I er eg e' => ({(m, I, er, eg, e')} : Multiset _)) h
  rw [plusPart_prepP _ _ _ _ _ he, plusPart_prepP _ _ _ _ _ he', Multiset.singleton_inj] at h1
  simpa using h1

theorem prepM_inj {m m' : MiniTreeCode} {I I' : Bool} {er eg e' er' eg' e'' : ECpl} (he : e'.wf = true)
    (he' : e''.wf = true) (h : prepM m I er eg e' = prepM m' I' er' eg' e'') :
    m = m' ∧ I = I' ∧ er = er' ∧ eg = eg' ∧ e' = e'' := by
  have h1 := congrArg (minusPart fun m I er eg e' => ({(m, I, er, eg, e')} : Multiset _)) h
  rw [minusPart_prepM _ _ _ _ _ he, minusPart_prepM _ _ _ _ _ he', Multiset.singleton_inj] at h1
  simpa using h1

/-! ### The sums -/

theorem mem_antidiag3 {n : ℕ} {x : Fin 3 → ℕ} :
    x ∈ Finset.Nat.antidiagonalTuple 3 n ↔ x 0 + x 1 + x 2 = n := by
  rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]

theorem fin3_ext {x y : Fin 3 → ℕ} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  funext i; fin_cases i <;> assumption

/-- **The type 1 codes of order `2(n+1)`**. -/
theorem sum_t1Part (n : ℕ) (H : MiniCplCode → ECpl → ECpl → ECpl → M) :
    ∑ e ∈ ED (n + 1), t1Part H e = ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ c : MiniCplCode,
      ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2), H c e₁ e₂ e₃ := by
  symm
  have hS : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ c : MiniCplCode,
      ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2), H c e₁ e₂ e₃ =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple 3 n).sigma fun x =>
        (univ : Finset MiniCplCode) ×ˢ ED (x 0) ×ˢ ED (x 1) ×ˢ ED (x 2),
        H p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
    rw [Finset.sum_sigma]
    simp only [Finset.sum_product]
  rw [hS]
  refine Finset.sum_bij_ne_zero (fun p _ _ => ECpl.type1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ?_ ?_ ?_ ?_
  · rintro ⟨x, c, e₁, e₂, e₃⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_antidiag3] at hp
    rw [mem_ED]
    simp only [ECpl.wf, hp.2.1.1, hp.2.2.1.1, hp.2.2.2.1, Bool.and_self, ECpl.hsize, true_and]
    omega
  · rintro ⟨x, c, e₁, e₂, e₃⟩ hp - ⟨x', c', e₁', e₂', e₃'⟩ hp' - h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED] at hp hp'
    simp only [ECpl.type1.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have : x = x' := fin3_ext (by rw [← hp.2.1.2, hp'.2.1.2]) (by rw [← hp.2.2.1.2, hp'.2.2.1.2])
      (by rw [← hp.2.2.2.2, hp'.2.2.2.2])
    subst this
    rfl
  · intro e he hne
    rw [mem_ED] at he
    cases e with
    | triv => exact absurd rfl hne
    | type2 => exact absurd rfl hne
    | type1 c e₁ e₂ e₃ =>
      simp only [ECpl.wf, Bool.and_eq_true, ECpl.hsize] at he
      refine ⟨⟨![e₁.hsize, e₂.hsize, e₃.hsize], c, e₁, e₂, e₃⟩, ?_, hne, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_antidiag3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      exact ⟨by have := he.2; omega, ⟨he.1.1.1, trivial⟩, ⟨he.1.1.2, trivial⟩, ⟨he.1.2, trivial⟩⟩
  · intro p _ _
    rfl

/-- **The type 2 codes of order `2(n+1)` with a `+` top pair.** -/
theorem sum_plusPart (n : ℕ) (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) :
    ∑ e ∈ ED (n + 1), plusPart H e = ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode,
      ∑ I : Bool, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2), H m I er eg e' := by
  symm
  have hS : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
      ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2), H m I er eg e' =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple 3 n).sigma fun x =>
        (univ : Finset MiniTreeCode) ×ˢ (univ : Finset Bool) ×ˢ ED (x 0) ×ˢ ED (x 1) ×ˢ ED (x 2),
        H p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    rw [Finset.sum_sigma]
    simp only [Finset.sum_product]
  rw [hS]
  refine Finset.sum_bij_ne_zero
    (fun p _ _ => prepP p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ?_ ?_ ?_ ?_
  · rintro ⟨x, m, I, er, eg, e'⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_antidiag3] at hp
    show prepP m I er eg e' ∈ ED (n + 1)
    rw [mem_ED]
    refine ⟨wf_prepP m I hp.2.1.1 hp.2.2.1.1 hp.2.2.2.1, ?_⟩
    rw [hsize_prepP]
    omega
  · rintro ⟨x, m, I, er, eg, e'⟩ hp - ⟨x', m', I', er', eg', e''⟩ hp' - h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED] at hp hp'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := prepP_inj hp.2.2.2.1 hp'.2.2.2.1 h
    have : x = x' := fin3_ext (by rw [← hp.2.1.2, hp'.2.1.2]) (by rw [← hp.2.2.1.2, hp'.2.2.1.2])
      (by rw [← hp.2.2.2.2, hp'.2.2.2.2])
    subst this
    rfl
  · intro e he hne
    rw [mem_ED] at he
    cases e with
    | triv => exact absurd rfl hne
    | type1 => exact absurd rfl hne
    | type2 X Y L =>
      cases X with
      | nil => exact absurd rfl hne
      | pair m I er eg X =>
        have hw := he.1
        simp only [ECpl.wf, EChain.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          EChain.isNil, Bool.false_and, Bool.not_false, and_true] at hw
        have hL : L.isType2 = false := hw.2
        have hmk : (mk2 X Y L).wf = true := wf_mk2' hw.1.1.1.2 hw.1.1.2 hw.1.2 hL
        refine ⟨⟨![er.hsize, eg.hsize, (mk2 X Y L).hsize], m, I, er, eg, mk2 X Y L⟩, ?_, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED,
            mem_antidiag3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          refine ⟨?_, ⟨hw.1.1.1.1.1, trivial⟩, ⟨hw.1.1.1.1.2, trivial⟩, ⟨hmk, trivial⟩⟩
          have := he.2
          simp only [ECpl.hsize, EChain.hsize] at this
          rw [hsize_mk2]
          omega
        · simpa [plusPart] using hne
        · exact prepP_mk2 m I er eg X Y hL
  · rintro ⟨x, m, I, er, eg, e'⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED] at hp
    exact (plusPart_prepP H m I er eg hp.2.2.2.1).symm

/-- **The type 2 codes of order `2(n+1)` with a `-` top pair.** -/
theorem sum_minusPart (n : ℕ) (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl → M) :
    ∑ e ∈ ED (n + 1), minusPart H e = ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode,
      ∑ I : Bool, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2), H m I er eg e' := by
  symm
  have hS : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
      ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2), H m I er eg e' =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple 3 n).sigma fun x =>
        (univ : Finset MiniTreeCode) ×ˢ (univ : Finset Bool) ×ˢ ED (x 0) ×ˢ ED (x 1) ×ˢ ED (x 2),
        H p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    rw [Finset.sum_sigma]
    simp only [Finset.sum_product]
  rw [hS]
  refine Finset.sum_bij_ne_zero
    (fun p _ _ => prepM p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ?_ ?_ ?_ ?_
  · rintro ⟨x, m, I, er, eg, e'⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_antidiag3] at hp
    show prepM m I er eg e' ∈ ED (n + 1)
    rw [mem_ED]
    refine ⟨wf_prepM m I hp.2.1.1 hp.2.2.1.1 hp.2.2.2.1, ?_⟩
    rw [hsize_prepM]
    omega
  · rintro ⟨x, m, I, er, eg, e'⟩ hp - ⟨x', m', I', er', eg', e''⟩ hp' - h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED] at hp hp'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := prepM_inj hp.2.2.2.1 hp'.2.2.2.1 h
    have : x = x' := fin3_ext (by rw [← hp.2.1.2, hp'.2.1.2]) (by rw [← hp.2.2.1.2, hp'.2.2.1.2])
      (by rw [← hp.2.2.2.2, hp'.2.2.2.2])
    subst this
    rfl
  · intro e he hne
    rw [mem_ED] at he
    cases e with
    | triv => exact absurd rfl hne
    | type1 => exact absurd rfl hne
    | type2 X Y L =>
      cases Y with
      | nil => cases X <;> exact absurd rfl hne
      | pair m I er eg Y =>
        have hw := he.1
        simp only [ECpl.wf, EChain.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          EChain.isNil, Bool.and_false, Bool.not_false, and_true] at hw
        have hL : L.isType2 = false := hw.2
        have hmk : (mk2 X Y L).wf = true := wf_mk2' hw.1.1.1 hw.1.1.2.2 hw.1.2 hL
        refine ⟨⟨![er.hsize, eg.hsize, (mk2 X Y L).hsize], m, I, er, eg, mk2 X Y L⟩, ?_, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED,
            mem_antidiag3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          refine ⟨?_, ⟨hw.1.1.2.1.1, trivial⟩, ⟨hw.1.1.2.1.2, trivial⟩, ⟨hmk, trivial⟩⟩
          have := he.2
          simp only [ECpl.hsize, EChain.hsize] at this
          rw [hsize_mk2]
          omega
        · simpa [minusPart] using hne
        · exact prepM_mk2 m I er eg X Y hL
  · rintro ⟨x, m, I, er, eg, e'⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED] at hp
    exact (minusPart_prepM H m I er eg hp.2.2.2.1).symm

/-! ### The decomposition of a weighted diagonal time factor -/

variable (r : ℝ)

/-- **`w(e) 𝒥ℬ*_e(t, t)` peeled at the top**: the type 1 recursion (recurtype1) and the diagonal split
`JB_diag` of the type 2 recursion (recurtype2). -/
theorem weighted_JB_decomp (w : ECpl → ℂ) {e : ECpl} (hw : e.wf = true) (hn : e.hsize ≠ 0) {t : ℝ}
    (hrt : r ≤ t) :
    w e * (e.JB r t t : ℂ) =
      t1Part (fun c e₁ e₂ e₃ => w (.type1 c e₁ e₂ e₃) *
        ((2 * ∫ u in r..t, e₁.JB r u u * e₂.JB r u u * e₃.JB r u u : ℝ) : ℂ)) e +
      plusPart (fun m I er eg e' => w (prepP m I er eg e') *
        ((∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u : ℝ) : ℂ)) e +
      minusPart (fun m I er eg e' => w (prepM m I er eg e') *
        ((∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u : ℝ) : ℂ)) e := by
  cases e with
  | triv => simp [ECpl.hsize] at hn
  | type1 c e₁ e₂ e₃ =>
    simp only [t1Part, plusPart, minusPart, add_zero]
    congr 2
    simp [ECpl.JB, ECpl.code, RegCpl.JB]
  | type2 X Y L =>
    have hL : L.isType2 = false := by
      simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
      exact hw.1.2
    rw [JB_diag r X Y L hw hrt, Complex.ofReal_add, mul_add]
    simp only [t1Part, zero_add]
    congr 1
    · cases X with
      | nil => simp [plusTerm, plusPart]
      | pair m I er eg X =>
        simp only [plusTerm, plusPart]
        rw [prepP_mk2 m I er eg X Y hL]
    · cases Y with
      | nil => cases X <;> simp [minusTerm, minusPart]
      | pair m I er eg Y =>
        simp only [minusTerm, minusPart]
        rw [prepM_mk2 m I er eg X Y hL]

end WaveTurbulence.Mexp
