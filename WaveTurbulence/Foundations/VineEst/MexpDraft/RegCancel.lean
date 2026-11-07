/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.MexpDraft.JointClass

/-!
# DH23 Prop 6.3 (`regcpltreecancel`, L940–L942): `∑ (K_𝒬)_app · conj((K*_𝒯)_app)` is real

For `r ≤ s ≤ t`, the sum over dominant couple codes `𝒬` and dominant tree codes `𝒯` of sign `+` of total order `2n`
of `(K_𝒬)_app(t,s,k) · conj((K*_𝒯)_app(t,s,k))` (B2 `RegCpl.app`, `RegChain.app`) is real.

DH23's proof (L1216–L1262): group the pairs by their joint collection of chain tuples and tail class (`jsh`). On a
joint class `ζ*ζ*` and `ℳ*ℳ*` are constant and real, so it suffices that the class sums of
`sw(Z) conj(sw(Z*)) 𝒥ℬ*_𝒬(t,s) 𝒥ℬ*_𝒯(t,s)` vanish when `|Z| + |Z*| ≠ 0` (`GJ_eq_zero`). DH23 orders all times and
sums over the partitions `(A₁, A₂, A₃)`. Here the induction peels the latest time (`weighted_Jt_decomp`):
* at `t = s` only the empty tree survives, and its class sum is DH21 Prop 7.8 (`classSum_eq_zero`);
* the latest time is a top pair of the `+` chain of `𝒬` (weight `(−π i)^{-1}` if special) or of `𝒯`
  (weight `conj((−π i)^{-1}) = (π i)^{-1}`). These are the same class, and the weights cancel. Otherwise a
  smaller class has `|Z| ≠ 0`: a couple class sum (or its conjugate) or a joint class sum, vanishing by
  induction (`triple_vanish_gen`).

**`regcancel`**: the realness statement for B2's leading terms.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Filter intervalIntegral Finset ComplexConjugate
open scoped Classical

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable {d : ℕ}

/-! ### Grouping by classes, general index types -/

theorem sum_class_eq_zero_gen {ι : Type*} (s : Finset ι) (sh : ι → Shape) (P : Shape → Prop)
    [DecidablePred P] (hP : ∀ X Y, Shape.Equiv X Y → P X → P Y) (f : ι → ℂ)
    (h : ∀ i₀ ∈ s, P (sh i₀) → ∑ i ∈ s, (if Shape.Equiv (sh i) (sh i₀) then f i else 0) = 0) :
    ∑ i ∈ s, (if P (sh i) then f i else 0) = 0 := by
  set q : ι → Quotient Shape.setoid := fun i => Quotient.mk Shape.setoid (sh i) with hq
  have hfib : ∀ i i₀, q i = q i₀ ↔ Shape.Equiv (sh i) (sh i₀) :=
    fun i i₀ => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := q) (t := s.image q)
    (fun i hi => Finset.mem_image_of_mem q hi)]
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  by_cases hP0 : P (sh i₀)
  · rw [Finset.sum_filter]
    refine Eq.trans ?_ (h i₀ hi₀ hP0)
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases he : Shape.Equiv (sh i) (sh i₀)
    · simp only [(hfib i i₀).2 he, he, hP _ _ he.symm hP0, ↓reduceIte]
    · have : ¬ q i = q i₀ := fun h' => he ((hfib i i₀).1 h')
      simp only [this, he, ↓reduceIte]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    have := (hfib i i₀).1 hi.2
    have hPi : ¬ P (sh i) := fun hPi => hP0 (hP _ _ this hPi)
    simp only [hPi, ↓reduceIte]

theorem fiber_integral_zero_gen {ι : Type*} (s : Finset ι) (sh : ι → Shape) (X : Shape) (A : ι → ℂ)
    (φ : ι → ℝ → ℝ) (hφ : ∀ i, Continuous (φ i)) {a b : ℝ} (hab : a ≤ b)
    (hX : ∀ u ∈ Icc a b, ∑ i ∈ s, (if Shape.Equiv (sh i) X then A i * (φ i u : ℂ) else 0) = 0)
    (c : ℂ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∑ i ∈ s, (if Shape.Equiv (sh i) X then A i * c * ((∫ u in a..b, φ i u * g u : ℝ) : ℂ) else 0) = 0 := by
  have hint : ∀ i, Continuous fun u => ((φ i u * g u : ℝ) : ℂ) :=
    fun i => Complex.continuous_ofReal.comp ((hφ i).mul hg)
  calc ∑ i ∈ s, (if Shape.Equiv (sh i) X then A i * c * ((∫ u in a..b, φ i u * g u : ℝ) : ℂ) else 0)
      = ∑ i ∈ s, ∫ u in a..b, (if Shape.Equiv (sh i) X then A i * c * ((φ i u * g u : ℝ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs
        · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
        · simp
    _ = ∫ u in a..b, ∑ i ∈ s, (if Shape.Equiv (sh i) X then A i * c * ((φ i u * g u : ℝ) : ℂ) else 0) := by
        rw [intervalIntegral.integral_finsetSum]
        intro i _
        split_ifs
        · exact (continuous_const.mul (hint i)).intervalIntegrable _ _
        · exact intervalIntegrable_const
    _ = ∫ u in a..b, c * (g u : ℂ) *
          ∑ i ∈ s, (if Shape.Equiv (sh i) X then A i * (φ i u : ℂ) else 0) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs
        · push_cast; ring
        · simp
    _ = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le hab] at hu
          simp only [hX u hu, mul_zero]]
        simp

/-- **Triple sums over a class condition with `|Z| ≠ 0` vanish** (general index types). -/
theorem triple_vanish_gen {ι₁ ι₂ ι₃ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (s₃ : Finset ι₃)
    (sh₁ : ι₁ → Shape) (sh₂ : ι₂ → Shape) (sh₃ : ι₃ → Shape) (A₁ : ι₁ → ℂ) (A₂ : ι₂ → ℂ) (A₃ : ι₃ → ℂ)
    (φ₁ : ι₁ → ℝ → ℝ) (φ₂ : ι₂ → ℝ → ℝ) (φ₃ : ι₃ → ℝ → ℝ) (c₁ : ∀ i, Continuous (φ₁ i))
    (c₂ : ∀ i, Continuous (φ₂ i)) (c₃ : ∀ i, Continuous (φ₃ i)) {a b : ℝ} (hab : a ≤ b)
    (Φ : Shape → Shape → Shape → Prop)
    (h₁ : ∀ X X' Y Z, Shape.Equiv X X' → Φ X Y Z → Φ X' Y Z)
    (h₂ : ∀ X Y Y' Z, Shape.Equiv Y Y' → Φ X Y Z → Φ X Y' Z)
    (h₃ : ∀ X Y Z Z', Shape.Equiv Z Z' → Φ X Y Z → Φ X Y Z')
    (hz : ∀ X Y Z, Φ X Y Z → X.zcount ≠ 0 ∨ Y.zcount ≠ 0 ∨ Z.zcount ≠ 0)
    (hA : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc a b,
      ∑ i ∈ s₁, (if Shape.Equiv (sh₁ i) X then A₁ i * (φ₁ i u : ℂ) else 0) = 0)
    (hB : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc a b,
      ∑ i ∈ s₂, (if Shape.Equiv (sh₂ i) X then A₂ i * (φ₂ i u : ℂ) else 0) = 0)
    (hC : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc a b,
      ∑ i ∈ s₃, (if Shape.Equiv (sh₃ i) X then A₃ i * (φ₃ i u : ℂ) else 0) = 0) (κ : ℂ) :
    ∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, ∑ i₃ ∈ s₃, (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) then
      κ * A₁ i₁ * A₂ i₂ * A₃ i₃ *
        ((∫ u in a..b, φ₁ i₁ u * φ₂ i₂ u * φ₃ i₃ u : ℝ) : ℂ) else 0) = 0 := by
  set F : ι₁ → ι₂ → ι₃ → ℂ := fun i₁ i₂ i₃ => κ * A₁ i₁ * A₂ i₂ * A₃ i₃ *
    ((∫ u in a..b, φ₁ i₁ u * φ₂ i₂ u * φ₃ i₃ u : ℝ) : ℂ) with hF
  have hsplit : ∀ i₁ i₂ i₃, (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) then F i₁ i₂ i₃ else 0) =
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount ≠ 0 then F i₁ i₂ i₃ else 0) +
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount = 0 ∧ (sh₂ i₂).zcount ≠ 0 then F i₁ i₂ i₃
        else 0) +
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount = 0 ∧ (sh₂ i₂).zcount = 0 ∧
        (sh₃ i₃).zcount ≠ 0 then F i₁ i₂ i₃ else 0) := by
    intro i₁ i₂ i₃
    by_cases hΦ : Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃)
    · have := hz _ _ _ hΦ
      by_cases z1 : (sh₁ i₁).zcount = 0 <;> by_cases z2 : (sh₂ i₂).zcount = 0 <;>
        by_cases z3 : (sh₃ i₃).zcount = 0 <;> simp_all
    · simp [hΦ]
  show ∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, ∑ i₃ ∈ s₃, (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) then F i₁ i₂ i₃ else 0) = 0
  simp only [hsplit, Finset.sum_add_distrib]
  have zc : ∀ X Y, Shape.Equiv X Y → X.zcount = Y.zcount := fun X Y h => h.zcount_eq
  have P1 : ∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, ∑ i₃ ∈ s₃,
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount ≠ 0 then F i₁ i₂ i₃ else 0) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i₃ _ => ?_
    refine sum_class_eq_zero_gen s₁ sh₁ (fun X => Φ X (sh₂ i₂) (sh₃ i₃) ∧ X.zcount ≠ 0)
      (fun X Y h hX => ⟨h₁ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩) _ fun i₀ _ h0 => ?_
    refine Eq.trans ?_ (fiber_integral_zero_gen s₁ sh₁ (sh₁ i₀) A₁ φ₁ c₁ hab (hA _ h0.2)
      (κ * A₂ i₂ * A₃ i₃) (g := fun u => φ₂ i₂ u * φ₃ i₃ u) ((c₂ i₂).mul (c₃ i₃)))
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    simp only [hF]
    split_ifs
    · rw [show (fun u => φ₁ i₁ u * φ₂ i₂ u * φ₃ i₃ u) = fun u => φ₁ i₁ u * (φ₂ i₂ u * φ₃ i₃ u) by
        funext u; ring]
      ring
    · rfl
  have P2 : ∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, ∑ i₃ ∈ s₃,
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount = 0 ∧ (sh₂ i₂).zcount ≠ 0 then F i₁ i₂ i₃
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun i₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i₃ _ => ?_
    by_cases z1 : (sh₁ i₁).zcount = 0
    · refine Eq.trans (Finset.sum_congr rfl fun i₂ _ => ?_)
        (sum_class_eq_zero_gen s₂ sh₂ (fun Y => Φ (sh₁ i₁) Y (sh₃ i₃) ∧ Y.zcount ≠ 0)
          (fun X Y h hX => ⟨h₂ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩)
          (fun i₂ => F i₁ i₂ i₃) ?_)
      · simp only [z1, true_and]
      · intro i₀ _ h0
        refine Eq.trans ?_ (fiber_integral_zero_gen s₂ sh₂ (sh₂ i₀) A₂ φ₂ c₂ hab (hB _ h0.2)
          (κ * A₁ i₁ * A₃ i₃) (g := fun u => φ₁ i₁ u * φ₃ i₃ u) ((c₁ i₁).mul (c₃ i₃)))
        refine Finset.sum_congr rfl fun i₂ _ => ?_
        simp only [hF]
        split_ifs
        · rw [show (fun u => φ₁ i₁ u * φ₂ i₂ u * φ₃ i₃ u) = fun u => φ₂ i₂ u * (φ₁ i₁ u * φ₃ i₃ u) by
            funext u; ring]
          ring
        · rfl
    · refine Finset.sum_eq_zero fun i₂ _ => ?_
      simp [z1]
  have P3 : ∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, ∑ i₃ ∈ s₃,
      (if Φ (sh₁ i₁) (sh₂ i₂) (sh₃ i₃) ∧ (sh₁ i₁).zcount = 0 ∧ (sh₂ i₂).zcount = 0 ∧
        (sh₃ i₃).zcount ≠ 0 then F i₁ i₂ i₃ else 0) = 0 := by
    refine Finset.sum_eq_zero fun i₁ _ => ?_
    refine Finset.sum_eq_zero fun i₂ _ => ?_
    by_cases z12 : (sh₁ i₁).zcount = 0 ∧ (sh₂ i₂).zcount = 0
    · refine Eq.trans (Finset.sum_congr rfl fun i₃ _ => ?_)
        (sum_class_eq_zero_gen s₃ sh₃ (fun Z => Φ (sh₁ i₁) (sh₂ i₂) Z ∧ Z.zcount ≠ 0)
          (fun X Y h hX => ⟨h₃ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩)
          (fun i₃ => F i₁ i₂ i₃) ?_)
      · simp only [z12.1, z12.2, true_and]
      · intro i₀ _ h0
        refine Eq.trans ?_ (fiber_integral_zero_gen s₃ sh₃ (sh₃ i₀) A₃ φ₃ c₃ hab (hC _ h0.2)
          (κ * A₁ i₁ * A₂ i₂) (g := fun u => φ₁ i₁ u * φ₂ i₂ u) ((c₁ i₁).mul (c₂ i₂)))
        refine Finset.sum_congr rfl fun i₃ _ => ?_
        simp only [hF]
        split_ifs
        · rw [show (fun u => φ₁ i₁ u * φ₂ i₂ u * φ₃ i₃ u) = fun u => φ₃ i₃ u * (φ₁ i₁ u * φ₂ i₂ u) by
            funext u; ring]
          ring
        · rfl
    · refine Finset.sum_eq_zero fun i₃ _ => ?_
      split_ifs with h
      · exact absurd ⟨h.2.1, h.2.2.1⟩ z12
      · rfl
  rw [P1, P2, P3, add_zero, add_zero]

/-! ### The joint class sums -/

variable (r : ℝ)

/-- **The joint class sum** `∑_{(e,f) ∼ S} sw(e) conj(sw(f)) 𝒥ℬ*_e(t,s) 𝒥ℬ*_f(t,s)` (DH23 (realcancel4)). -/
noncomputable def GJ (N : ℕ) (S : Shape) (t s : ℝ) : ℂ :=
  ∑ q ∈ PS N, if Shape.Equiv (jsh q.1 q.2) S then q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 t s : ℂ)
    else 0

theorem conj_wt (I : Bool) : conj (wt 1 I) = wt (-1) I := by
  cases I
  · simp [wt]
  · simp only [wt, ↓reduceIte, Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg,
      neg_mul, neg_neg, map_inv₀, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

theorem EChain.eq_nil_of_hsize {f : EChain} (h : f.hsize = 0) : f = .nil := by
  cases f with
  | nil => rfl
  | pair => simp [EChain.hsize] at h

theorem conj_classSum (a : ℕ) (X : Shape) (u : ℝ) :
    ∑ e ∈ ED a, (if Shape.Equiv e.shape X then conj e.sw * (e.JB r u u : ℂ) else 0) =
      conj (classSum r a X u) := by
  rw [classSum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · rw [map_mul, Complex.conj_ofReal]
  · simp

/-- **DH23 Prop 6.3, the cancellation**: the joint class sums with `|Z| + |Z*| ≠ 0` vanish (`r ≤ s ≤ t`). -/
theorem GJ_eq_zero (N : ℕ) : ∀ S : Shape, S.zcount ≠ 0 → ∀ s t, r ≤ s → s ≤ t → GJ r N S t s = 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro S hS s t hrs hst
  rcases N with _ | N
  · refine Finset.sum_eq_zero fun q hq => ?_
    rw [mem_PS] at hq
    have h1 : q.1 = .triv := ECpl.eq_triv_of_hsize hq.1 (by omega)
    have h2 : q.2 = .nil := EChain.eq_nil_of_hsize (by omega)
    have : ¬ Shape.Equiv (jsh q.1 q.2) S := fun h => hS (by
      rw [← h.zcount_eq, h1, h2]; rfl)
    simp only [this, ↓reduceIte]
  -- the induction hypothesis on `[s, t]`
  have IH : ∀ j ≤ N, ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc s t,
      ∑ q ∈ PS j, (if Shape.Equiv (jsh q.1 q.2) X then
        q.1.sw * conj (q.2.sw 1) * (Jt r q.1 q.2 u s : ℂ) else 0) = 0 :=
    fun j hj X hX u hu => ih j (by omega) X hX s u hrs hu.1
  have CS : ∀ a, ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc s t,
      ∑ e ∈ ED a, (if Shape.Equiv e.shape X then e.sw * (e.JB r u u : ℂ) else 0) = 0 :=
    fun a X hX u hu => classSum_eq_zero r a X hX u (hrs.trans hu.1)
  have CS' : ∀ a, ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc s t,
      ∑ e ∈ ED a, (if Shape.Equiv e.shape X then conj e.sw * (e.JB r u u : ℂ) else 0) = 0 := by
    intro a X hX u hu
    rw [conj_classSum, classSum_eq_zero r a X hX u (hrs.trans hu.1), map_zero]
  set w : ECpl → EChain → ℂ := fun e f =>
    if Shape.Equiv (jsh e f) S then e.sw * conj (f.sw 1) else 0 with hw
  have hdec : GJ r (N + 1) S t s = ∑ q ∈ PS (N + 1), w q.1 q.2 * (Jt r q.1 q.2 t s : ℂ) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hw, ite_mul, zero_mul]
  rw [hdec, Finset.sum_congr rfl fun q hq => weighted_Jt_decomp r w (mem_PS.1 hq).1 q.2 hrs hst]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_nilPart]
  -- the empty tree: DH21 Prop 7.8 at `t = s`
  have h0 : ∑ e ∈ ED (N + 1), w e .nil * (e.JB r s s : ℂ) = 0 := by
    rw [← classSum_eq_zero r (N + 1) S hS s hrs]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hw, jsh_nil, EChain.sw, map_one, mul_one, ite_mul, zero_mul]
  rw [h0, zero_add]
  rw [show ∑ q ∈ PS (N + 1), plusPart (fun m I er eg e' => w (prepP m I er eg e') q.2 *
      ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r e' q.2 u s : ℝ) : ℂ)) q.1 =
      ∑ q ∈ PS (N + 1), plusPart (fun m I er eg e' => (fun m I er eg (q' : ECpl × EChain) =>
        w (prepP m I er eg q'.1) q'.2 *
          ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q'.1 q'.2 u s : ℝ) : ℂ)) m I er eg (e', q.2))
        q.1 from rfl, sum_plusPartP N (fun m I er eg (q' : ECpl × EChain) =>
        w (prepP m I er eg q'.1) q'.2 *
          ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q'.1 q'.2 u s : ℝ) : ℂ))]
  rw [show ∑ q ∈ PS (N + 1), treePart (fun m I er eg f' => w q.1 (.pair m I er eg f') *
      ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q.1 f' u s : ℝ) : ℂ)) q.2 =
      ∑ q ∈ PS (N + 1), treePart (fun m I er eg f' => (fun m I er eg (q' : ECpl × EChain) =>
        w q'.1 (.pair m I er eg q'.2) *
          ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q'.1 q'.2 u s : ℝ) : ℂ)) m I er eg (q.1, f'))
        q.2 from rfl, sum_treePart N (fun m I er eg (q' : ECpl × EChain) =>
        w q'.1 (.pair m I er eg q'.2) *
          ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q'.1 q'.2 u s : ℝ) : ℂ))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [mem_antidiag3] at hx
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun I _ => ?_
  -- the two latest-time positions, in the same joint class
  set Φ : Shape → Shape → Shape → Prop :=
    fun Xr Xg Xq => Shape.Equiv (consShape I m.c Xr Xg Xq) S with hΦ
  have hP : ∀ er eg e' f, w (prepP m I er eg e') f =
      if Φ er.shape eg.shape (jsh e' f) then wt 1 I * er.sw * eg.sw * (e'.sw * conj (f.sw 1)) else 0 := by
    intro er eg e' f
    have hiff : Shape.Equiv (jsh (prepP m I er eg e') f) S ↔ Φ er.shape eg.shape (jsh e' f) :=
      ⟨fun h => (jsh_prepP m I er eg e' f).symm.trans h, fun h => (jsh_prepP m I er eg e' f).trans h⟩
    simp only [hw, hiff, sw_prepP]
    split_ifs <;> ring
  have hT : ∀ er eg e f, w e (.pair m I er eg f) =
      if Φ er.shape eg.shape (jsh e f) then
        conj (wt 1 I) * conj er.sw * conj eg.sw * (e.sw * conj (f.sw 1)) else 0 := by
    intro er eg e f
    simp only [hw, jsh_pair, hΦ, EChain.sw, map_mul]
    split_ifs <;> ring
  have hcl1 : ∀ X X' Y Z, Shape.Equiv X X' → Φ X Y Z → Φ X' Y Z := fun X X' Y Z h h' =>
    (consShape_congr I m.c h.symm (Shape.equiv_refl Y) (Shape.equiv_refl Z)).trans h'
  have hcl2 : ∀ X Y Y' Z, Shape.Equiv Y Y' → Φ X Y Z → Φ X Y' Z := fun X Y Y' Z h h' =>
    (consShape_congr I m.c (Shape.equiv_refl X) h.symm (Shape.equiv_refl Z)).trans h'
  have hcl3 : ∀ X Y Z Z', Shape.Equiv Z Z' → Φ X Y Z → Φ X Y Z' := fun X Y Z Z' h h' =>
    (consShape_congr I m.c (Shape.equiv_refl X) (Shape.equiv_refl Y) h.symm).trans h'
  -- split off the all-`Z = ∅` sub-pieces
  set Ψ : Shape → Shape → Shape → Prop := fun X Y Z => Φ X Y Z ∧
    ¬ (X.zcount = 0 ∧ Y.zcount = 0 ∧ Z.zcount = 0) with hΨ
  have hΨz : ∀ X Y Z, Ψ X Y Z → X.zcount ≠ 0 ∨ Y.zcount ≠ 0 ∨ Z.zcount ≠ 0 := by
    intro X Y Z h; by_contra hc; push Not at hc; exact h.2 hc
  have hΨ1 : ∀ X X' Y Z, Shape.Equiv X X' → Ψ X Y Z → Ψ X' Y Z := fun X X' Y Z h h' =>
    ⟨hcl1 _ _ _ _ h h'.1, by rw [← h.zcount_eq]; exact h'.2⟩
  have hΨ2 : ∀ X Y Y' Z, Shape.Equiv Y Y' → Ψ X Y Z → Ψ X Y' Z := fun X Y Y' Z h h' =>
    ⟨hcl2 _ _ _ _ h h'.1, by rw [← h.zcount_eq]; exact h'.2⟩
  have hΨ3 : ∀ X Y Z Z', Shape.Equiv Z Z' → Ψ X Y Z → Ψ X Y Z' := fun X Y Z Z' h h' =>
    ⟨hcl3 _ _ _ _ h h'.1, by rw [← h.zcount_eq]; exact h'.2⟩
  set Aq : ECpl × EChain → ℂ := fun q => q.1.sw * conj (q.2.sw 1) with hAq
  set φq : ECpl × EChain → ℝ → ℝ := fun q u => Jt r q.1 q.2 u s with hφq
  have cq : ∀ q, Continuous (φq q) := fun q => Jt_continuous r q.1 q.2 s
  have cJ : ∀ e : ECpl, Continuous fun u => e.JB r u u := fun e => JB_diag_continuous r _
  have hC : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc s t,
      ∑ q ∈ PS (x 2), (if Shape.Equiv (jsh q.1 q.2) X then Aq q * (φq q u : ℂ) else 0) = 0 :=
    fun X hX u hu => IH (x 2) (by omega) X hX u hu
  have vP := triple_vanish_gen (ED (x 0)) (ED (x 1)) (PS (x 2)) ECpl.shape ECpl.shape
    (fun q => jsh q.1 q.2) ECpl.sw ECpl.sw Aq (fun e u => e.JB r u u) (fun e u => e.JB r u u) φq
    cJ cJ cq hst Ψ hΨ1 hΨ2 hΨ3 hΨz (CS (x 0)) (CS (x 1)) hC (wt 1 I)
  have vT := triple_vanish_gen (ED (x 0)) (ED (x 1)) (PS (x 2)) ECpl.shape ECpl.shape
    (fun q => jsh q.1 q.2) (fun e => conj e.sw) (fun e => conj e.sw) Aq (fun e u => e.JB r u u)
    (fun e u => e.JB r u u) φq cJ cJ cq hst Ψ hΨ1 hΨ2 hΨ3 hΨz (CS' (x 0)) (CS' (x 1)) hC (conj (wt 1 I))
  refine Eq.trans ?_ ((congrArg₂ (· + ·) vP vT).trans (add_zero 0))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun er _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun eg _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP, hT]
  simp only [hΨ, hAq, hφq]
  by_cases hΦ0 : Φ er.shape eg.shape (jsh q.1 q.2)
  · by_cases haz : er.shape.zcount = 0 ∧ eg.shape.zcount = 0 ∧ (jsh q.1 q.2).zcount = 0
    · -- all `Z = ∅` below: the special top weights cancel
      have hS' := hΦ0.zcount_eq
      rw [zcount_consShape, haz.1, haz.2.1, haz.2.2] at hS'
      have hI : I = true := by
        cases I
        · exact absurd hS'.symm (by simpa using hS)
        · rfl
      subst hI
      have h1 := ECpl.sw_eq_one er haz.1
      have h2 := ECpl.sw_eq_one eg haz.2.1
      have hw2 := wt_add true
      simp only [↓reduceIte] at hw2
      simp only [hΦ0, haz, and_self, not_true_eq_false, and_false, ↓reduceIte, h1, h2,
        map_one, conj_wt, mul_one, add_zero]
      linear_combination (q.1.sw * (starRingEnd ℂ) (q.2.sw 1) *
        ((∫ u in s..t, er.JB r u u * eg.JB r u u * Jt r q.1 q.2 u s : ℝ) : ℂ)) * hw2
    · simp only [hΦ0, haz, not_false_eq_true, and_self, ↓reduceIte]
  · simp only [hΦ0, false_and, ↓reduceIte, add_zero, zero_mul]

end WaveTurbulence.Mexp
