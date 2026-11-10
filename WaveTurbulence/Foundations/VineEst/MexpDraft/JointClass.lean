/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.MexpDraft.ETree

/-!
# Couple–tree pairs: joint classes and the time factor peeled at its latest time (DH23 Prop 6.3)

DH23's proof of Prop 6.3 groups pairs `(𝒬, 𝒯)` (an enhanced dominant couple and an enhanced dominant tree of sign
`+`) by the collection of all their chain tuples and the tail class `𝒴` (DH23 L1236).

* `prependT`, `jsh e f`: this joint class, as an ENHANCED `Shape` (the tree's tuples put in front of the couple's
  class); `jsh_prepP`, `jsh_prepM`, `jsh_pair`: a new top pair on either chain of `e` or on `f` puts its tuple in
  front; `mshape_jsh`, `netSign_jsh`, `zcount_jsh`.
* `Jt e f (t, s) = 𝒥ℬ*_e(t, s) 𝒥ℬ*_f(t, s)`; **`Jt_decomp`** (for `r ≤ s ≤ t`): `Jt` is its value at `t = s` plus
  `∫_s^t` of the terms with the latest time on the `+` chain of `e` or on `f` (the product rule for primitives).
* `PS N`: pairs of total order `2N`; `sum_nilPart`, `sum_plusPartP`, `sum_treePart`: the corresponding sums.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Filter intervalIntegral Finset

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable {d : ℕ}

/-! ### Joint classes -/

/-- Put the tuples `L` in front of the class `S`. -/
def prependT : Tuples → Shape → Shape
  | .nil, S => S
  | .cons I c X₁ X₂ L, S => consShape I c X₁ X₂ (prependT L S)

/-- **The joint class** of a couple–tree pair: all chain tuples and the tail class of the couple. -/
def jsh (e : ECpl) (f : EChain) : Shape := prependT f.tuples e.shape

theorem consShape_comm (I : Bool) (c : Fin 3) (X₁ X₂ : Shape) (I' : Bool) (c' : Fin 3) (X₁' X₂' S : Shape) :
    Shape.Equiv (consShape I c X₁ X₂ (consShape I' c' X₁' X₂' S))
      (consShape I' c' X₁' X₂' (consShape I c X₁ X₂ S)) := by
  cases S <;> simp only [consShape] <;> rw [equiv_type2_iff_TEq] <;>
    exact ⟨TEq.swap I c X₁ X₂ I' c' X₁' X₂' _, Shape.equiv_refl _⟩

theorem prependT_consShape (I : Bool) (c : Fin 3) (X₁ X₂ S : Shape) : (L : Tuples) →
    Shape.Equiv (prependT L (consShape I c X₁ X₂ S)) (consShape I c X₁ X₂ (prependT L S))
  | .nil => Shape.equiv_refl _
  | .cons I' c' _ _ L =>
    (consShape_congr I' c' (Shape.equiv_refl _) (Shape.equiv_refl _)
      (prependT_consShape I c X₁ X₂ S L)).trans (consShape_comm _ _ _ _ _ _ _ _ _)

theorem jsh_pair (e : ECpl) (m : MiniTreeCode) (I : Bool) (er eg : ECpl) (f : EChain) :
    jsh e (.pair m I er eg f) = consShape I m.c er.shape eg.shape (jsh e f) := rfl

theorem jsh_nil (e : ECpl) : jsh e .nil = e.shape := rfl

theorem jsh_prepP (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) (f : EChain) :
    Shape.Equiv (jsh (prepP m I er eg e') f) (consShape I m.c er.shape eg.shape (jsh e' f)) := by
  rw [jsh, shape_prepP]
  exact prependT_consShape _ _ _ _ _ _

theorem zcount_prependT : (L : Tuples) → (S : Shape) → (prependT L S).zcount = L.zcount + S.zcount
  | .nil, S => by simp [prependT, Tuples.zcount]
  | .cons I c X₁ X₂ L, S => by
    rw [prependT, zcount_consShape, zcount_prependT L S]
    simp only [Tuples.zcount]; ring

theorem netSign_prependT : (L : Tuples) → (S : Shape) → (prependT L S).netSign = L.netSign * S.netSign
  | .nil, S => by simp [prependT, Tuples.netSign]
  | .cons I c X₁ X₂ L, S => by
    rw [prependT, netSign_consShape, netSign_prependT L S]
    simp only [Tuples.netSign]; ring

theorem mshape_prependT (F : Mom d → ℝ) : (L : Tuples) → (S : Shape) → (k : Mom d) →
    Mshape F (prependT L S) k = Mtuples F L k * Mshape F S k
  | .nil, S, k => by simp [prependT, Mtuples]
  | .cons I c X₁ X₂ L, S, k => by
    rw [prependT, mshape_consShape, mshape_prependT F L S k]
    simp only [Mtuples]; ring

/-! ### The joint time factor -/

variable (r : ℝ)

/-- `𝒥ℬ*_e(t, s) 𝒥ℬ*_f(t, s)`. -/
noncomputable def Jt (e : ECpl) (f : EChain) (t s : ℝ) : ℝ := e.JB r t s * f.JBt r t s

theorem JBt_continuous (f : EChain) (s : ℝ) : Continuous fun u => f.JBt r u s := by
  have h := JBchain_continuous r f.code (max s r) (G := fun (_ : ℝ) (_ : ℝ) => (1 : ℝ)) continuous_const
  exact h.comp ((continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).prodMk continuous_id)

theorem JB_left_continuous (e : ECpl) (s : ℝ) : Continuous fun u => e.JB r u s :=
  (JB_continuous r e.code).comp (continuous_id.prodMk continuous_const)

theorem Jt_continuous (e : ECpl) (f : EChain) (s : ℝ) : Continuous fun u => Jt r e f u s :=
  (JB_left_continuous r e s).mul (JBt_continuous r f s)

/-- The `+` latest-time integrand of `𝒥ℬ*_e(·, s)`: `P(u) 𝒥ℬ*_{e'}(u, s)` (zero without a `+` chain). -/
noncomputable def alphaP (s : ℝ) : ECpl → ℝ → ℝ
  | .triv => fun _ => 0
  | .type1 .. => fun _ => 0
  | .type2 .nil _ _ => fun _ => 0
  | .type2 (.pair _ _ er eg X) Y L => fun u => er.JB r u u * eg.JB r u u * (mk2 X Y L).JB r u s

/-- The latest-time integrand of `𝒥ℬ*_f(·, s)`. -/
noncomputable def betaT (s : ℝ) : EChain → ℝ → ℝ
  | .nil => fun _ => 0
  | .pair _ _ er eg f => fun u => er.JB r u u * eg.JB r u u * f.JBt r u s

theorem alphaP_continuous (s : ℝ) (e : ECpl) : Continuous (alphaP r s e) := by
  rcases e with _ | _ | ⟨_ | ⟨m, I, er, eg, X⟩, Y, L⟩ <;> try exact continuous_const
  exact ((JB_diag_continuous r _).mul (JB_diag_continuous r _)).mul (JB_left_continuous r _ s)

theorem betaT_continuous (s : ℝ) (f : EChain) : Continuous (betaT r s f) := by
  rcases f with _ | ⟨m, I, er, eg, f⟩
  · exact continuous_const
  · exact ((JB_diag_continuous r _).mul (JB_diag_continuous r _)).mul (JBt_continuous r f s)

theorem JB_peel_s {e : ECpl} (hw : e.wf = true) {s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    e.JB r t s = e.JB r s s + ∫ u in s..t, alphaP r s e u := by
  rcases e with _ | ⟨c, e₁, e₂, e₃⟩ | ⟨X, Y, L⟩
  · simp [alphaP, ECpl.JB, ECpl.code, RegCpl.JB]
  · simp only [alphaP, intervalIntegral.integral_zero, add_zero, ECpl.JB, ECpl.code]
    rw [JB_min r (by rfl) t s, min_eq_right hst]
  · have hL : L.isType2 = false := by
      simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
      exact hw.1.2
    have hnil := hw
    simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hnil
    rcases X with _ | ⟨m, I, er, eg, X⟩
    · rcases Y with _ | ⟨m, I, er, eg, Y⟩
      · simp [EChain.isNil] at hnil
      · simp only [alphaP, intervalIntegral.integral_zero, add_zero]
        have h1 := JB_plusNil r (.pair m I er eg Y) hL hrs hst
        have h2 : mk2 .nil (.pair m I er eg Y) L = .type2 .nil (.pair m I er eg Y) L := by
          simp [mk2, EChain.isNil]
        rwa [h2] at h1
    · simp only [alphaP]
      rw [← prepP_mk2 m I er eg X Y hL, JB_prepP, JB_prepP]
      have hc : Continuous fun u => er.JB r u u * eg.JB r u u * (mk2 X Y L).JB r u s :=
        ((JB_diag_continuous r _).mul (JB_diag_continuous r _)).mul (JB_left_continuous r _ s)
      exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)).symm

theorem JBt_peel_s (f : EChain) {s t : ℝ} (hrs : r ≤ s) :
    f.JBt r t s = (if f.isNil then 1 else 0) + ∫ u in s..t, betaT r s f u := by
  rcases f with _ | ⟨m, I, er, eg, f⟩
  · simp [EChain.JBt, EChain.code, RegChain.JBtree, RegChain.JBchain, betaT, EChain.isNil]
  · simp only [EChain.JBt, EChain.code, RegChain.JBtree, RegChain.JBchain, betaT, EChain.isNil,
      Bool.false_eq_true, ↓reduceIte, zero_add, max_eq_left hrs, ECpl.JB]

/-- **The joint time factor peeled at its latest time** (`r ≤ s ≤ t`). -/
theorem Jt_decomp {e : ECpl} (hw : e.wf = true) (f : EChain) {s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    Jt r e f t s = e.JB r s s * (if f.isNil then 1 else 0) +
      ∫ u in s..t, (alphaP r s e u * f.JBt r u s + e.JB r u s * betaT r s f u) := by
  rw [Jt, JB_peel_s r hw hrs hst, JBt_peel_s r f hrs,
    primitive_mul_primitive (alphaP_continuous r s e) (betaT_continuous r s f)]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  rw [← JB_peel_s r hw hrs hu.1, ← JBt_peel_s r f hrs]

/-! ### Pairs and their sums -/

theorem finite_PS (N : ℕ) :
    {q : ECpl × EChain | q.1.wf = true ∧ q.2.wf = true ∧ q.1.hsize + q.2.hsize = N}.Finite :=
  ((finite_bounded N).1.prod (finite_bounded N).2).subset fun q hq =>
    ⟨⟨hq.1, by have := hq.2.2; omega⟩, ⟨hq.2.1, by have := hq.2.2; omega⟩⟩

/-- **Couple–tree pairs of total order `2N`.** -/
noncomputable def PS (N : ℕ) : Finset (ECpl × EChain) := (finite_PS N).toFinset

theorem mem_PS {N : ℕ} {q : ECpl × EChain} :
    q ∈ PS N ↔ q.1.wf = true ∧ q.2.wf = true ∧ q.1.hsize + q.2.hsize = N := by
  simp [PS]

variable {M : Type*} [AddCommMonoid M]

/-- The part of a function of pairs with an empty tree. -/
def nilPart (G : ECpl → M) (q : ECpl × EChain) : M := if q.2.isNil then G q.1 else 0

/-- The tree top-pair part. -/
def treePart (H : MiniTreeCode → Bool → ECpl → ECpl → EChain → M) : EChain → M
  | .nil => 0
  | .pair m I er eg f => H m I er eg f

theorem sum_nilPart (N : ℕ) (G : ECpl → M) : ∑ q ∈ PS N, nilPart G q = ∑ e ∈ ED N, G e := by
  symm
  refine Finset.sum_bij_ne_zero (fun e _ _ => (e, EChain.nil)) ?_ ?_ ?_ ?_
  · intro e he _
    rw [mem_ED] at he
    rw [mem_PS]
    exact ⟨he.1, rfl, by simp [EChain.hsize, he.2]⟩
  · intro e _ _ e' _ _ h
    exact (Prod.mk.inj h).1
  · rintro ⟨e, f⟩ hq hne
    rw [mem_PS] at hq
    rcases f with _ | f
    · refine ⟨e, ?_, ?_, rfl⟩
      · rw [mem_ED]; exact ⟨hq.1, by simpa [EChain.hsize] using hq.2.2⟩
      · simpa [nilPart, EChain.isNil] using hne
    · simp [nilPart, EChain.isNil] at hne
  · intro e _ _
    simp [nilPart, EChain.isNil]

/-- **Pairs whose couple has a `+` top pair.** -/
theorem sum_plusPartP (n : ℕ) (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl × EChain → M) :
    ∑ q ∈ PS (n + 1), plusPart (fun m I er eg e' => H m I er eg (e', q.2)) q.1 =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
        ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ q ∈ PS (x 2), H m I er eg q := by
  symm
  have hS : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
      ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ q ∈ PS (x 2), H m I er eg q =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple 3 n).sigma fun x =>
        (univ : Finset MiniTreeCode) ×ˢ (univ : Finset Bool) ×ˢ ED (x 0) ×ˢ ED (x 1) ×ˢ PS (x 2),
        H p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    rw [Finset.sum_sigma]
    simp only [Finset.sum_product]
  rw [hS]
  refine Finset.sum_bij_ne_zero
    (fun p _ _ => (prepP p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1, p.2.2.2.2.2.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, m, I, er, eg, e', f⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS,
      mem_antidiag3] at hp
    show (prepP m I er eg e', f) ∈ PS (n + 1)
    rw [mem_PS]
    refine ⟨wf_prepP m I hp.2.1.1 hp.2.2.1.1 hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩
    simp only [hsize_prepP]
    omega
  · rintro ⟨x, m, I, er, eg, e', f⟩ hp - ⟨x', m', I', er', eg', e'', f'⟩ hp' - h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS] at hp hp'
    obtain ⟨h1, rfl⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := prepP_inj hp.2.2.2.1 hp'.2.2.2.1 h1
    have : x = x' := fin3_ext (by rw [← hp.2.1.2, hp'.2.1.2]) (by rw [← hp.2.2.1.2, hp'.2.2.1.2])
      (by rw [← hp.2.2.2.2.2, hp'.2.2.2.2.2])
    subst this
    rfl
  · rintro ⟨e, f⟩ hq hne
    rw [mem_PS] at hq
    rcases e with _ | _ | ⟨_ | ⟨m, I, er, eg, X⟩, Y, L⟩ <;> try exact absurd rfl hne
    have hw := hq.1
    simp only [ECpl.wf, EChain.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      EChain.isNil, Bool.false_and, Bool.not_false, and_true] at hw
    have hL : L.isType2 = false := hw.2
    have hmk : (mk2 X Y L).wf = true := wf_mk2' hw.1.1.1.2 hw.1.1.2 hw.1.2 hL
    refine ⟨⟨![er.hsize, eg.hsize, (mk2 X Y L).hsize + f.hsize], m, I, er, eg, mk2 X Y L, f⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS,
        mem_antidiag3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨?_, ⟨hw.1.1.1.1.1, trivial⟩, ⟨hw.1.1.1.1.2, trivial⟩, hmk, hq.2.1, trivial⟩
      have := hq.2.2
      simp only [ECpl.hsize, EChain.hsize] at this
      rw [hsize_mk2]
      omega
    · simpa [plusPart] using hne
    · show (prepP m I er eg (mk2 X Y L), f) = _
      rw [prepP_mk2 m I er eg X Y hL]
  · rintro ⟨x, m, I, er, eg, e', f⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS] at hp
    exact (plusPart_prepP (fun m I er eg e' => H m I er eg (e', f)) m I er eg hp.2.2.2.1).symm

/-- **Pairs whose tree has a top pair.** -/
theorem sum_treePart (n : ℕ) (H : MiniTreeCode → Bool → ECpl → ECpl → ECpl × EChain → M) :
    ∑ q ∈ PS (n + 1), treePart (fun m I er eg f' => H m I er eg (q.1, f')) q.2 =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
        ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ q ∈ PS (x 2), H m I er eg q := by
  symm
  have hS : ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ m : MiniTreeCode, ∑ I : Bool,
      ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ q ∈ PS (x 2), H m I er eg q =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple 3 n).sigma fun x =>
        (univ : Finset MiniTreeCode) ×ˢ (univ : Finset Bool) ×ˢ ED (x 0) ×ˢ ED (x 1) ×ˢ PS (x 2),
        H p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
    rw [Finset.sum_sigma]
    simp only [Finset.sum_product]
  rw [hS]
  refine Finset.sum_bij_ne_zero
    (fun p _ _ => (p.2.2.2.2.2.1, EChain.pair p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, m, I, er, eg, e, f⟩ hp -
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS,
      mem_antidiag3] at hp
    show (e, EChain.pair m I er eg f) ∈ PS (n + 1)
    rw [mem_PS]
    refine ⟨hp.2.2.2.1, by simp [EChain.wf, hp.2.1.1, hp.2.2.1.1, hp.2.2.2.2.1], ?_⟩
    simp only [EChain.hsize]
    omega
  · rintro ⟨x, m, I, er, eg, e, f⟩ hp - ⟨x', m', I', er', eg', e', f'⟩ hp' - h
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS] at hp hp'
    obtain ⟨rfl, h2⟩ := Prod.mk.inj h
    simp only [EChain.pair.injEq] at h2
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h2
    have : x = x' := fin3_ext (by rw [← hp.2.1.2, hp'.2.1.2]) (by rw [← hp.2.2.1.2, hp'.2.2.1.2])
      (by rw [← hp.2.2.2.2.2, hp'.2.2.2.2.2])
    subst this
    rfl
  · rintro ⟨e, f⟩ hq hne
    rw [mem_PS] at hq
    rcases f with _ | ⟨m, I, er, eg, f⟩
    · exact absurd rfl hne
    have hw := hq.2.1
    simp only [EChain.wf, Bool.and_eq_true] at hw
    refine ⟨⟨![er.hsize, eg.hsize, e.hsize + f.hsize], m, I, er, eg, e, f⟩, ?_, ?_, rfl⟩
    · simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_univ, true_and, mem_ED, mem_PS,
        mem_antidiag3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨?_, ⟨hw.1.1, trivial⟩, ⟨hw.1.2, trivial⟩, hq.1, hw.2, trivial⟩
      have := hq.2.2
      simp only [EChain.hsize] at this
      omega
    · simpa [treePart] using hne
  · rintro ⟨x, m, I, er, eg, e, f⟩ _ -
    rfl

/-! ### The weighted decomposition of a pair -/

/-- **`w(e, f) Jt(e, f)(t, s)` peeled at the latest time** (`r ≤ s ≤ t`): the empty-tree value at `t = s`, the
`+` top pair of `e`, and the top pair of `f`. -/
theorem weighted_Jt_decomp (w : ECpl → EChain → ℂ) {e : ECpl} (hw : e.wf = true) (f : EChain)
    {s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    w e f * (Jt r e f t s : ℂ) =
      nilPart (fun e => w e .nil * (e.JB r s s : ℂ)) (e, f) +
      plusPart (fun m I er eg e' => w (prepP m I er eg e') f *
        ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r e' f u s : ℝ) : ℂ)) e +
      treePart (fun m I er eg f' => w e (.pair m I er eg f') *
        ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r e f' u s : ℝ) : ℂ)) f := by
  have hL : ∀ {X Y : EChain} {L : ECpl}, e = .type2 X Y L → L.isType2 = false := by
    rintro X Y L rfl
    simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    exact hw.1.2
  have hα : ∀ u, alphaP r s e u * f.JBt r u s =
      plusPart (fun _ _ er eg e' => er.JB r u u * eg.JB r u u * Jt r e' f u s) e := by
    intro u
    rcases e with _ | _ | ⟨_ | ⟨m, I, er, eg, X⟩, Y, L⟩ <;> simp [alphaP, plusPart, Jt] ; ring
  have hβ : ∀ u, e.JB r u s * betaT r s f u =
      treePart (fun _ _ er eg f' => er.JB r u u * eg.JB r u u * Jt r e f' u s) f := by
    intro u
    rcases f with _ | ⟨m, I, er, eg, f⟩ <;> simp [betaT, treePart, Jt] ; ring
  rw [Jt_decomp r hw f hrs hst]
  simp only [hα, hβ]
  have hpl : ∀ (g : MiniTreeCode → Bool → ECpl → ECpl → ECpl → ℝ → ℝ),
      ∫ u in s..t, plusPart (fun m I er eg e' => g m I er eg e' u) e =
        plusPart (fun m I er eg e' => ∫ u in s..t, g m I er eg e' u) e := by
    intro g
    rcases e with _ | _ | ⟨_ | ⟨m, I, er, eg, X⟩, Y, L⟩ <;> simp [plusPart]
  have htr : ∀ (g : MiniTreeCode → Bool → ECpl → ECpl → EChain → ℝ → ℝ),
      ∫ u in s..t, treePart (fun m I er eg f' => g m I er eg f' u) f =
        treePart (fun m I er eg f' => ∫ u in s..t, g m I er eg f' u) f := by
    intro g
    rcases f with _ | ⟨m, I, er, eg, f⟩ <;> simp [treePart]
  rw [intervalIntegral.integral_add]
  · rw [hpl (fun _ _ er eg e' u => er.JB r u u * eg.JB r u u * Jt r e' f u s),
      htr (fun _ _ er eg f' u => er.JB r u u * eg.JB r u u * Jt r e f' u s)]
    push_cast
    rw [mul_add, mul_add, ← add_assoc]
    congr 1
    congr 1
    · rcases f with _ | f <;> simp [nilPart, EChain.isNil]
    · rcases e with _ | _ | ⟨_ | ⟨m, I, er, eg, X⟩, Y, L⟩
      · simp [plusPart]
      · simp [plusPart]
      · simp [plusPart]
      · simp only [plusPart]
        rw [prepP_mk2 m I er eg X Y (hL rfl)]
    · rcases f with _ | ⟨m, I, er, eg, f⟩ <;> simp [treePart]
  · rw [← funext hα]
    exact ((alphaP_continuous r s e).mul (JBt_continuous r f s)).intervalIntegrable _ _
  · rw [← funext hβ]
    exact ((JB_left_continuous r e s).mul (betaT_continuous r s f)).intervalIntegrable _ _

end WaveTurbulence.Mexp
