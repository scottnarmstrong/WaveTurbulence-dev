/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.ShapePerm

/-!
# DH21 Prop 7.8 (`nonemptyZ`, L1838–L1855): the class sums with `Z ≠ ∅` vanish

For a class `X` of enhanced dominant couples of order `2n` (ENHANCED `Shape` up to `Shape.Equiv`) with `|Z| ≠ 0`,

  `𝒢_X(t) = ∑_{(𝒬,Z) ∈ X} ∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1} · 𝒥ℬ*_𝒬(t, t) = 0`     for `t ≥ r`,

with the F61-corrected weight (`specialWeight`). DH21 sums over all permutations of the tuples and all
interleavings `(A, B)` of the two chains at once. Here the induction peels one time at a time: the latest time
belongs to the type 1 root, or to the top pair of the `+` chain, or to that of the `-` chain (`JB_diag`). The two
chains give the same class (`shape_prepM_equiv`) and weights `(∓πi)^{-1}` at a special top node, which cancel
(`wt_add`); otherwise one of the three remaining classes has `|Z| ≠ 0` and its class sum vanishes by induction
(`triple_vanish`, grouping by classes with `sum_class_eq_zero`).

* `classSum r n S t`: `𝒢_S(t)` over the enhanced codes `ED n`; **`classSum_eq_zero`**.
* **`prop78`**: the statement for B2's couple codes and special subsets; `prop78_mstar`: with `ℳ*` (constant on
  the class, Prop 7.7), the sum of the leading terms over a class with `Z ≠ ∅` vanishes.
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset
open scoped Classical

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable (r : ℝ)

/-- **The class sum** `𝒢_S(t) = ∑_{e ∈ ED n, e ∼ S} sw(e) 𝒥ℬ*_e(t, t)` (DH21 (nonemptyZ1), F61 weights). -/
noncomputable def classSum (n : ℕ) (S : Shape) (t : ℝ) : ℂ :=
  ∑ e ∈ ED n, if Shape.Equiv e.shape S then e.sw * (e.JB r t t : ℂ) else 0

/-! ### Grouping by classes -/

/-- If the sum over each class meeting `P` vanishes, so does the sum over `P`. -/
theorem sum_class_eq_zero (s : Finset ECpl) (P : Shape → Prop) [DecidablePred P]
    (hP : ∀ X Y, Shape.Equiv X Y → P X → P Y) (f : ECpl → ℂ)
    (h : ∀ e₀ ∈ s, P e₀.shape → ∑ e ∈ s, (if Shape.Equiv e.shape e₀.shape then f e else 0) = 0) :
    ∑ e ∈ s, (if P e.shape then f e else 0) = 0 := by
  set q : ECpl → Quotient Shape.setoid := fun e => Quotient.mk Shape.setoid e.shape with hq
  have hfib : ∀ e e₀, q e = q e₀ ↔ Shape.Equiv e.shape e₀.shape :=
    fun e e₀ => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := q) (t := s.image q)
    (fun e he => Finset.mem_image_of_mem q he)]
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 hy
  by_cases hP0 : P e₀.shape
  · rw [Finset.sum_filter]
    refine Eq.trans ?_ (h e₀ he₀ hP0)
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : Shape.Equiv e.shape e₀.shape
    · simp only [(hfib e e₀).2 he, he, hP _ _ he.symm hP0, ↓reduceIte]
    · have : ¬ q e = q e₀ := fun h' => he ((hfib e e₀).1 h')
      simp only [this, he, ↓reduceIte]
  · refine Finset.sum_eq_zero fun e he => ?_
    rw [Finset.mem_filter] at he
    have := (hfib e e₀).1 he.2
    have hPe : ¬ P e.shape := fun hPe => hP0 (hP _ _ this hPe)
    simp only [hPe, ↓reduceIte]

/-- A class with vanishing class sum on `[r, t]` contributes nothing to a sum of time integrals. -/
theorem fiber_integral_zero {a : ℕ} {X : Shape} {t : ℝ} (hrt : r ≤ t)
    (hX : ∀ u ∈ Icc r t, classSum r a X u = 0) (c : ℂ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∑ e ∈ ED a, (if Shape.Equiv e.shape X then
      e.sw * c * ((∫ u in r..t, e.JB r u u * g u : ℝ) : ℂ) else 0) = 0 := by
  have hint : ∀ e : ECpl, Continuous fun u => ((e.JB r u u * g u : ℝ) : ℂ) :=
    fun e => Complex.continuous_ofReal.comp ((JB_diag_continuous r _).mul hg)
  calc ∑ e ∈ ED a, (if Shape.Equiv e.shape X then
        e.sw * c * ((∫ u in r..t, e.JB r u u * g u : ℝ) : ℂ) else 0)
      = ∑ e ∈ ED a, ∫ u in r..t, (if Shape.Equiv e.shape X then
          e.sw * c * ((e.JB r u u * g u : ℝ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs
        · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
        · simp
    _ = ∫ u in r..t, ∑ e ∈ ED a, (if Shape.Equiv e.shape X then
          e.sw * c * ((e.JB r u u * g u : ℝ) : ℂ) else 0) := by
        rw [intervalIntegral.integral_finsetSum]
        intro e _
        split_ifs
        · exact (continuous_const.mul (hint e)).intervalIntegrable _ _
        · exact intervalIntegrable_const
    _ = ∫ u in r..t, c * (g u : ℂ) * classSum r a X u := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [classSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs
        · push_cast; ring
        · simp
    _ = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le hrt] at hu
          simp only [hX u hu, mul_zero]]
        simp

/-- **Triple sums over a class condition with `|Z| ≠ 0` vanish**, given the vanishing of the class sums of the
three pieces. -/
theorem triple_vanish {a b c : ℕ} {t : ℝ} (hrt : r ≤ t) (Φ : Shape → Shape → Shape → Prop)
    (h₁ : ∀ X X' Y Z, Shape.Equiv X X' → Φ X Y Z → Φ X' Y Z)
    (h₂ : ∀ X Y Y' Z, Shape.Equiv Y Y' → Φ X Y Z → Φ X Y' Z)
    (h₃ : ∀ X Y Z Z', Shape.Equiv Z Z' → Φ X Y Z → Φ X Y Z')
    (hz : ∀ X Y Z, Φ X Y Z → X.zcount ≠ 0 ∨ Y.zcount ≠ 0 ∨ Z.zcount ≠ 0)
    (hA : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc r t, classSum r a X u = 0)
    (hB : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc r t, classSum r b X u = 0)
    (hC : ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc r t, classSum r c X u = 0) (κ : ℂ) :
    ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c, (if Φ e₁.shape e₂.shape e₃.shape then
      κ * e₁.sw * e₂.sw * e₃.sw *
        ((∫ u in r..t, e₁.JB r u u * e₂.JB r u u * e₃.JB r u u : ℝ) : ℂ) else 0) = 0 := by
  set F : ECpl → ECpl → ECpl → ℂ := fun e₁ e₂ e₃ => κ * e₁.sw * e₂.sw * e₃.sw *
    ((∫ u in r..t, e₁.JB r u u * e₂.JB r u u * e₃.JB r u u : ℝ) : ℂ) with hF
  have hsplit : ∀ e₁ e₂ e₃ : ECpl, (if Φ e₁.shape e₂.shape e₃.shape then F e₁ e₂ e₃ else 0) =
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount ≠ 0 then F e₁ e₂ e₃ else 0) +
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount = 0 ∧ e₂.shape.zcount ≠ 0 then F e₁ e₂ e₃
        else 0) +
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount = 0 ∧ e₂.shape.zcount = 0 ∧
        e₃.shape.zcount ≠ 0 then F e₁ e₂ e₃ else 0) := by
    intro e₁ e₂ e₃
    by_cases hΦ : Φ e₁.shape e₂.shape e₃.shape
    · have := hz _ _ _ hΦ
      by_cases z1 : e₁.shape.zcount = 0 <;> by_cases z2 : e₂.shape.zcount = 0 <;>
        by_cases z3 : e₃.shape.zcount = 0 <;> simp_all
    · simp [hΦ]
  show ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c,
    (if Φ e₁.shape e₂.shape e₃.shape then F e₁ e₂ e₃ else 0) = 0
  simp only [hsplit, Finset.sum_add_distrib]
  have zc : ∀ X Y, Shape.Equiv X Y → X.zcount = Y.zcount := fun X Y h => h.zcount_eq
  have P1 : ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c,
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount ≠ 0 then F e₁ e₂ e₃ else 0) = 0 := by
    -- `e₁` carries `|Z| ≠ 0`
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e₃ _ => ?_
    refine sum_class_eq_zero (ED a) (fun X => Φ X e₂.shape e₃.shape ∧ X.zcount ≠ 0)
      (fun X Y h hX => ⟨h₁ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩) _ fun e₀ _ h0 => ?_
    have := fiber_integral_zero r hrt (hA _ h0.2) (κ * e₂.sw * e₃.sw)
      (g := fun u => e₂.JB r u u * e₃.JB r u u)
      ((JB_diag_continuous r _).mul (JB_diag_continuous r _))
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    simp only [hF]
    split_ifs
    · rw [show (fun u => e₁.JB r u u * e₂.JB r u u * e₃.JB r u u) =
          fun u => e₁.JB r u u * (e₂.JB r u u * e₃.JB r u u) by funext u; ring]
      ring
    · rfl
  have P2 : ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c,
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount = 0 ∧ e₂.shape.zcount ≠ 0 then F e₁ e₂ e₃
        else 0) = 0 := by
    -- `e₂` carries `|Z| ≠ 0`
    refine Finset.sum_eq_zero fun e₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e₃ _ => ?_
    by_cases z1 : e₁.shape.zcount = 0
    · refine Eq.trans (Finset.sum_congr rfl fun e₂ _ => ?_)
        (sum_class_eq_zero (ED b) (fun Y => Φ e₁.shape Y e₃.shape ∧ Y.zcount ≠ 0)
          (fun X Y h hX => ⟨h₂ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩)
          (fun e₂ => F e₁ e₂ e₃) ?_)
      · simp only [z1, true_and]
      · intro e₀ _ h0
        have := fiber_integral_zero r hrt (hB _ h0.2) (κ * e₁.sw * e₃.sw)
          (g := fun u => e₁.JB r u u * e₃.JB r u u)
          ((JB_diag_continuous r _).mul (JB_diag_continuous r _))
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun e₂ _ => ?_
        simp only [hF]
        split_ifs
        · rw [show (fun u => e₁.JB r u u * e₂.JB r u u * e₃.JB r u u) =
              fun u => e₂.JB r u u * (e₁.JB r u u * e₃.JB r u u) by funext u; ring]
          ring
        · rfl
    · refine Finset.sum_eq_zero fun e₂ _ => ?_
      simp [z1]
  have P3 : ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c,
      (if Φ e₁.shape e₂.shape e₃.shape ∧ e₁.shape.zcount = 0 ∧ e₂.shape.zcount = 0 ∧
        e₃.shape.zcount ≠ 0 then F e₁ e₂ e₃ else 0) = 0 := by
    -- `e₃` carries `|Z| ≠ 0`
    refine Finset.sum_eq_zero fun e₁ _ => ?_
    refine Finset.sum_eq_zero fun e₂ _ => ?_
    by_cases z12 : e₁.shape.zcount = 0 ∧ e₂.shape.zcount = 0
    · refine Eq.trans (Finset.sum_congr rfl fun e₃ _ => ?_)
        (sum_class_eq_zero (ED c) (fun Z => Φ e₁.shape e₂.shape Z ∧ Z.zcount ≠ 0)
          (fun X Y h hX => ⟨h₃ _ _ _ _ h hX.1, by rw [← zc X Y h]; exact hX.2⟩)
          (fun e₃ => F e₁ e₂ e₃) ?_)
      · simp only [z12.1, z12.2, true_and]
      · intro e₀ _ h0
        have := fiber_integral_zero r hrt (hC _ h0.2) (κ * e₁.sw * e₂.sw)
          (g := fun u => e₁.JB r u u * e₂.JB r u u)
          ((JB_diag_continuous r _).mul (JB_diag_continuous r _))
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun e₃ _ => ?_
        simp only [hF]
        split_ifs
        · rw [show (fun u => e₁.JB r u u * e₂.JB r u u * e₃.JB r u u) =
              fun u => e₃.JB r u u * (e₁.JB r u u * e₂.JB r u u) by funext u; ring]
          ring
        · rfl
    · refine Finset.sum_eq_zero fun e₃ _ => ?_
      split_ifs with h
      · exact absurd ⟨h.2.1, h.2.2.1⟩ z12
      · rfl
  rw [P1, P2, P3, add_zero, add_zero]

/-! ### The induction -/

theorem ECpl.eq_triv_of_hsize {e : ECpl} (hw : e.wf = true) (h : e.hsize = 0) : e = .triv := by
  cases e with
  | triv => rfl
  | type1 => simp [ECpl.hsize] at h
  | type2 X Y L =>
    simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_false_iff] at hw
    simp only [ECpl.hsize, Nat.add_eq_zero_iff] at h
    rcases hw.2 with h' | h'
    · have := EChain.one_le_hsize h'; omega
    · have := EChain.one_le_hsize h'; omega

/-- **DH21 Prop 7.8 for enhanced codes**: the class sums with `|Z| ≠ 0` vanish for `t ≥ r`. -/
theorem classSum_eq_zero (n : ℕ) : ∀ S : Shape, S.zcount ≠ 0 → ∀ t, r ≤ t → classSum r n S t = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS t hrt
  rcases n with _ | n
  · refine Finset.sum_eq_zero fun e he => ?_
    rw [mem_ED] at he
    rw [ECpl.eq_triv_of_hsize he.1 he.2]
    have : ¬ Shape.Equiv ECpl.triv.shape S := fun h => hS (by rw [← h.zcount_eq]; rfl)
    simp only [this, ↓reduceIte]
  -- the induction hypothesis on `[r, t]`
  have IH : ∀ j ≤ n, ∀ X : Shape, X.zcount ≠ 0 → ∀ u ∈ Icc r t, classSum r j X u = 0 :=
    fun j hj X hX u hu => ih j (by omega) X hX u hu.1
  set w : ECpl → ℂ := fun e => if Shape.Equiv e.shape S then e.sw else 0 with hw
  have hdec : classSum r (n + 1) S t = ∑ e ∈ ED (n + 1), w e * (e.JB r t t : ℂ) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hw, ite_mul, zero_mul]
  rw [hdec, Finset.sum_congr rfl fun e he => weighted_JB_decomp r w (mem_ED.1 he).1
    (by rw [(mem_ED.1 he).2]; omega) hrt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_t1Part, sum_plusPart, sum_minusPart]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [mem_antidiag3] at hx
  have hA := IH (x 0) (by omega)
  have hB := IH (x 1) (by omega)
  have hC := IH (x 2) (by omega)
  -- the type 1 part
  have h1 : ∀ c : MiniCplCode, ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2),
      w (.type1 c e₁ e₂ e₃) * ((2 * ∫ u in r..t, e₁.JB r u u * e₂.JB r u u * e₃.JB r u u : ℝ) : ℂ) = 0 := by
    intro c
    rw [← triple_vanish r hrt (fun X Y Z => Shape.Equiv (.type1 X Y Z) S)
      (fun X X' Y Z h h' => (Shape.Equiv.type1 h.symm (Shape.equiv_refl Y) (Shape.equiv_refl Z)).trans h')
      (fun X Y Y' Z h h' => (Shape.Equiv.type1 (Shape.equiv_refl X) h.symm (Shape.equiv_refl Z)).trans h')
      (fun X Y Z Z' h h' => (Shape.Equiv.type1 (Shape.equiv_refl X) (Shape.equiv_refl Y) h.symm).trans h')
      (fun X Y Z h => by
        have := h.zcount_eq
        simp only [Shape.zcount] at this
        omega) hA hB hC 2]
    refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ =>
      Finset.sum_congr rfl fun e₃ _ => ?_
    by_cases hc : Shape.Equiv (Shape.type1 e₁.shape e₂.shape e₃.shape) S
    · simp only [hw, ECpl.shape, ECpl.sw, hc, ↓reduceIte]
      push_cast; ring
    · simp only [hw, ECpl.shape, hc, ↓reduceIte, zero_mul]
  -- the type 2 parts: the two chains
  have h2 : ∀ m : MiniTreeCode, ∑ I : Bool, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
      (w (prepP m I er eg e') * ((∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u : ℝ) : ℂ) +
        w (prepM m I er eg e') * ((∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u : ℝ) : ℂ)) =
      0 := by
    intro m
    have hpm : ∀ I er eg e', (Shape.Equiv (prepM m I er eg e').shape S ↔
        Shape.Equiv (consShape I m.c er.shape eg.shape e'.shape) S) := fun I er eg e' =>
      ⟨fun h => (shape_prepM_equiv m I er eg e').symm.trans h,
        fun h => (shape_prepM_equiv m I er eg e').trans h⟩
    have hsum : ∀ I er eg e', w (prepP m I er eg e') * ((∫ u in r..t, er.JB r u u * eg.JB r u u *
        e'.JB r u u : ℝ) : ℂ) + w (prepM m I er eg e') * ((∫ u in r..t, er.JB r u u * eg.JB r u u *
        e'.JB r u u : ℝ) : ℂ) =
        if Shape.Equiv (consShape I m.c er.shape eg.shape e'.shape) S then
          (wt 1 I + wt (-1) I) * er.sw * eg.sw * e'.sw *
            ((∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u : ℝ) : ℂ) else 0 := by
      intro I er eg e'
      simp only [hw, shape_prepP, hpm, sw_prepP, sw_prepM]
      split_ifs
      · ring
      · simp
    simp only [hsum, wt_add, Fintype.sum_bool, ↓reduceIte, zero_mul, ite_self, Finset.sum_const_zero,
      zero_add, Bool.false_eq_true]
    exact triple_vanish r hrt (fun X Y Z => Shape.Equiv (consShape false m.c X Y Z) S)
      (fun X X' Y Z h h' => (consShape_congr false m.c h.symm (Shape.equiv_refl Y)
        (Shape.equiv_refl Z)).trans h')
      (fun X Y Y' Z h h' => (consShape_congr false m.c (Shape.equiv_refl X) h.symm
        (Shape.equiv_refl Z)).trans h')
      (fun X Y Z Z' h h' => (consShape_congr false m.c (Shape.equiv_refl X) (Shape.equiv_refl Y)
        h.symm).trans h')
      (fun X Y Z h => by
        have := h.zcount_eq
        rw [zcount_consShape] at this
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at this
        omega) hA hB hC 2
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_const_zero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← h2 m]
  simp only [Finset.sum_add_distrib]

/-! ### DH21 Prop 7.8 for B2's codes -/

/-- **DH21 Prop 7.8** (`nonemptyZ`, L1838, with the F61-corrected weight): for every class `S` of enhanced
dominant couples with `|Z| ≠ 0` and `t ≥ r`,
`∑_{(𝒬,Z) ∼ S} ∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1} 𝒥ℬ*_𝒬(t,t) = 0` (sum over the well-formed dominant couple codes of
order `2n` and their special subsets). -/
theorem prop78 {t : ℝ} (hrt : r ≤ t) (n : ℕ) (S : Shape) (hS : S.zcount ≠ 0) :
    ∑ Q ∈ domCodes n, ∑ Z ∈ specialSets Q.links,
      (if Shape.Equiv (cplShape Z Q rt₀ rt₁) S then specialWeight ![1, -1] Z * (Q.JB r t t : ℂ)
        else 0) = 0 := by
  refine Eq.trans ?_ (classSum_eq_zero r n S hS t hrt)
  rw [classSum, ← sum_domCodes_specialSets]
  refine Finset.sum_congr rfl fun Q hQ => Finset.sum_congr rfl fun Z hZ => ?_
  have hd := (mem_domCodes.1 hQ).2.1
  rw [shape_enh, specialWeight_eq_sw hd hZ, ECpl.JB, code_enh Z Q hd]

/-- **DH21 Prop 7.8 with the momentum factor**: the leading terms
`∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1} 𝒥ℬ*_𝒬(t,t) ℳ*_{(𝒬,Z)}(k)` sum to zero over a class with `|Z| ≠ 0` (`ℳ*` is
constant on the class, Prop 7.7). -/
theorem prop78_mstar {d : ℕ} (F : Mom d → ℝ) {t : ℝ} (hrt : r ≤ t) (n : ℕ) (S : Shape)
    (hS : S.zcount ≠ 0) (k : Mom d) :
    ∑ Q ∈ domCodes n, ∑ Z ∈ specialSets Q.links,
      (if Shape.Equiv (cplShape Z Q rt₀ rt₁) S then
        specialWeight ![1, -1] Z * (Q.JB r t t : ℂ) * (Q.Mstar F Z rt₀ rt₁ k : ℂ) else 0) = 0 := by
  have h := prop78 r hrt n S hS
  calc _ = ∑ Q ∈ domCodes n, ∑ Z ∈ specialSets Q.links,
        (if Shape.Equiv (cplShape Z Q rt₀ rt₁) S then
          specialWeight ![1, -1] Z * (Q.JB r t t : ℂ) else 0) * (Mshape F S k : ℂ) := by
        refine Finset.sum_congr rfl fun Q hQ => Finset.sum_congr rfl fun Z _ => ?_
        have hd := (mem_domCodes.1 hQ).2.1
        split_ifs with hc
        · rw [mstar_eq_mshape F Z Q hd, mshape_congr F hc]
        · simp
    _ = 0 := by
        simp only [← Finset.sum_mul, h, zero_mul]

end WaveTurbulence.Mexp
