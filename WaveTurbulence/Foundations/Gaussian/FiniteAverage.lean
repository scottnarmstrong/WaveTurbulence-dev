/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Logic.Equiv.Fintype

/-!
# Uniform averages and kernel operators on finite types

This file is the finite, purely algebraic part of the proof of Gaussian hypercontractivity
(DH21 Lemma A.3). On a finite type `α` we use the uniform average `favg`, and operators
`kapply k f x = ∑ y, k x y * f y` given by a kernel `k`. A kernel is `(2,q)`-hypercontractive
(`IsHypercontractive q k`) if `favg ((k f)^q) ≤ (favg (f^2))^(q/2)` for every nonnegative `f`.

## Main results

* `IsHypercontractive.ktensor`: `(2,q)` hypercontractivity tensorizes (for `q ≥ 2`), by
  Minkowski's inequality in `L^{q/2}`.
* `isHypercontractive_of_dual`: for a symmetric nonnegative kernel, the `(p,2)` bound implies
  the `(2,q)` bound for the conjugate exponent `q` (Hölder duality).
* `IsHypercontractive.of_equiv`: transport along an equivalence of finite types.
-/

public section

open Finset

namespace WaveTurbulence.Gaussian

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The uniform average of a real function on a finite type. -/
@[expose] noncomputable def favg (f : α → ℝ) : ℝ := (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

theorem favg_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ favg f :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sum_nonneg fun x _ => hf x)

theorem favg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : favg f ≤ favg g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => h x) (inv_nonneg.2 (Nat.cast_nonneg _))

theorem favg_const [Nonempty α] (c : ℝ) : favg (fun _ : α => c) = c := by
  have h : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [favg, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem favg_mul_left (c : ℝ) (f : α → ℝ) : favg (fun x => c * f x) = c * favg f := by
  simp only [favg, ← mul_sum]
  ring

theorem favg_add (f g : α → ℝ) : favg (fun x => f x + g x) = favg f + favg g := by
  simp only [favg, sum_add_distrib]
  ring

theorem favg_prod (f : α × β → ℝ) : favg f = favg (fun x => favg (fun y => f (x, y))) := by
  simp only [favg, Fintype.card_prod, Nat.cast_mul, ← mul_sum, Fintype.sum_prod_type]
  ring

theorem favg_prod_swap (f : α × β → ℝ) :
    favg f = favg (fun y => favg (fun x => f (x, y))) := by
  simp only [favg, Fintype.card_prod, Nat.cast_mul, ← mul_sum, Fintype.sum_prod_type_right]
  ring

theorem favg_equiv (e : α ≃ β) (f : β → ℝ) : favg (fun x => f (e x)) = favg f := by
  simp only [favg, Fintype.card_congr e, Equiv.sum_comp e f]

/-- Cauchy–Schwarz for uniform averages. -/
theorem favg_mul_sq_le (f g : α → ℝ) :
    favg (fun x => f x * g x) ^ 2 ≤ favg (fun x => f x ^ 2) * favg (fun x => g x ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ f g
  simp only [favg]
  have hc : 0 ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((Fintype.card α : ℝ)⁻¹ * ∑ x, f x * g x) ^ 2
      = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ x, f x * g x) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 * ((∑ x, f x ^ 2) * ∑ x, g x ^ 2) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by ring

omit [Fintype β] in
/-- **Minkowski's inequality** for a finite sum of nonnegative functions on a finite type. -/
theorem rpow_sum_sum_le {r : ℝ} (hr : 1 ≤ r) (T : Finset β) (G : β → α → ℝ)
    (hG : ∀ y x, 0 ≤ G y x) :
    (∑ x, (∑ y ∈ T, G y x) ^ r) ^ (1 / r) ≤ ∑ y ∈ T, (∑ x, G y x ^ r) ^ (1 / r) := by
  classical
  have hr0 : r ≠ 0 := by positivity
  induction T using Finset.induction_on with
  | empty =>
    simp [Real.zero_rpow hr0, Real.zero_rpow (inv_ne_zero hr0)]
  | insert y T hy ih =>
    simp only [sum_insert hy]
    calc (∑ x, (G y x + ∑ y' ∈ T, G y' x) ^ r) ^ (1 / r)
        ≤ (∑ x, G y x ^ r) ^ (1 / r) + (∑ x, (∑ y' ∈ T, G y' x) ^ r) ^ (1 / r) :=
          Real.Lp_add_le_of_nonneg univ hr (fun x _ => hG y x)
            (fun x _ => sum_nonneg fun _ _ => hG _ x)
      _ ≤ _ := by gcongr

/-- **Minkowski's inequality** for uniform averages: the `L^r` norm of an average is at most the
average of the `L^r` norms. -/
theorem favg_minkowski {r : ℝ} (hr : 1 ≤ r) (G : β → α → ℝ) (hG : ∀ y x, 0 ≤ G y x) :
    favg (fun x => favg (fun y => G y x) ^ r) ^ (1 / r) ≤
      favg (fun y => favg (fun x => G y x ^ r) ^ (1 / r)) := by
  have hr0 : 0 < r := by linarith
  set a : ℝ := (Fintype.card α : ℝ)⁻¹ with ha
  set b : ℝ := (Fintype.card β : ℝ)⁻¹ with hb
  have ha0 : 0 ≤ a := inv_nonneg.2 (Nat.cast_nonneg _)
  have hb0 : 0 ≤ b := inv_nonneg.2 (Nat.cast_nonneg _)
  have hS : ∀ x, 0 ≤ ∑ y, G y x := fun x => sum_nonneg fun y _ => hG y x
  have hmink := rpow_sum_sum_le hr univ G hG
  have lhs : favg (fun x => favg (fun y => G y x) ^ r) ^ (1 / r) =
      a ^ (1 / r) * b * (∑ x, (∑ y, G y x) ^ r) ^ (1 / r) := by
    simp only [favg, ← ha, ← hb]
    have h1 : ∀ x, (b * ∑ y, G y x) ^ r = b ^ r * (∑ y, G y x) ^ r := fun x =>
      Real.mul_rpow hb0 (hS x)
    simp only [h1, ← mul_sum]
    rw [← mul_assoc, Real.mul_rpow (mul_nonneg ha0 (Real.rpow_nonneg hb0 _))
      (sum_nonneg fun x _ => Real.rpow_nonneg (hS x) _),
      Real.mul_rpow ha0 (Real.rpow_nonneg hb0 _), one_div, Real.rpow_rpow_inv hb0 hr0.ne']
  have rhs : favg (fun y => favg (fun x => G y x ^ r) ^ (1 / r)) =
      a ^ (1 / r) * b * ∑ y, (∑ x, G y x ^ r) ^ (1 / r) := by
    simp only [favg, ← ha, ← hb]
    have h1 : ∀ y, (a * ∑ x, G y x ^ r) ^ (1 / r) = a ^ (1 / r) * (∑ x, G y x ^ r) ^ (1 / r) :=
      fun y => Real.mul_rpow ha0 (sum_nonneg fun x _ => Real.rpow_nonneg (hG y x) _)
    simp only [h1, ← mul_sum]
    ring
  rw [lhs, rhs]
  exact mul_le_mul_of_nonneg_left hmink (mul_nonneg (Real.rpow_nonneg ha0 _) hb0)

/-! ### Kernel operators -/

/-- The operator with kernel `k` on a finite type: `kapply k f x = ∑ y, k x y * f y`. -/
@[expose] noncomputable def kapply (k : α → α → ℝ) (f : α → ℝ) (x : α) : ℝ := ∑ y, k x y * f y

theorem kapply_nonneg {k : α → α → ℝ} (hk : ∀ x y, 0 ≤ k x y) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : α) : 0 ≤ kapply k f x :=
  sum_nonneg fun y _ => mul_nonneg (hk x y) (hf y)

/-- A kernel is `(2,q)`-hypercontractive if `‖k f‖_q ≤ ‖f‖_2` for all nonnegative `f`, the
norms taken with respect to the uniform probability measure. -/
@[expose] def IsHypercontractive (q : ℝ) (k : α → α → ℝ) : Prop :=
  ∀ f : α → ℝ, (∀ x, 0 ≤ f x) →
    favg (fun x => kapply k f x ^ q) ≤ favg (fun x => f x ^ 2) ^ (q / 2)

/-- The tensor product of two kernels. -/
@[expose] def ktensor (k₁ : α → α → ℝ) (k₂ : β → β → ℝ) (x y : α × β) : ℝ := k₁ x.1 y.1 * k₂ x.2 y.2

theorem kapply_ktensor (k₁ : α → α → ℝ) (k₂ : β → β → ℝ) (f : α × β → ℝ) (x : α × β) :
    kapply (ktensor k₁ k₂) f x =
      kapply k₁ (fun y₁ => kapply k₂ (fun y₂ => f (y₁, y₂)) x.2) x.1 := by
  simp only [kapply, ktensor, Fintype.sum_prod_type, mul_sum]
  exact sum_congr rfl fun y₁ _ => sum_congr rfl fun y₂ _ => by ring

/-- `(2,q)` hypercontractivity tensorizes, for `q ≥ 2`. -/
theorem IsHypercontractive.ktensor {q : ℝ} (hq : 2 ≤ q) {k₁ : α → α → ℝ} {k₂ : β → β → ℝ}
    (hk₂ : ∀ x y, 0 ≤ k₂ x y) (h₁ : IsHypercontractive q k₁) (h₂ : IsHypercontractive q k₂) :
    IsHypercontractive q (Gaussian.ktensor k₁ k₂) := by
  intro f hf
  set g : α → β → ℝ := fun y₁ x₂ => kapply k₂ (fun y₂ => f (y₁, y₂)) x₂ with hgdef
  have hg : ∀ y₁ x₂, 0 ≤ g y₁ x₂ := fun y₁ x₂ => kapply_nonneg hk₂ (fun _ => hf _) _
  set r : ℝ := q / 2 with hrdef
  have hr : 1 ≤ r := by rw [hrdef]; linarith
  have hr0 : 0 < r := by linarith
  have step1 : favg (fun x => kapply (Gaussian.ktensor k₁ k₂) f x ^ q) ≤
      favg (fun x₂ => favg (fun y₁ => g y₁ x₂ ^ 2) ^ r) := by
    rw [favg_prod_swap]
    refine favg_mono fun x₂ => ?_
    simp only [kapply_ktensor]
    exact h₁ (fun y₁ => g y₁ x₂) (fun y₁ => hg y₁ x₂)
  have step2 := favg_minkowski hr (fun y₁ x₂ => g y₁ x₂ ^ 2) (fun _ _ => sq_nonneg _)
  have step3 : ∀ y₁, favg (fun x₂ => (g y₁ x₂ ^ 2) ^ r) ^ (1 / r) ≤
      favg (fun y₂ => f (y₁, y₂) ^ 2) := by
    intro y₁
    have h := h₂ (fun y₂ => f (y₁, y₂)) (fun _ => hf _)
    have hgq : ∀ x₂, (g y₁ x₂ ^ 2) ^ r = g y₁ x₂ ^ q := by
      intro x₂
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hg _ _), hrdef]
      congr 1
      push_cast
      ring
    simp only [hgq]
    have hF : 0 ≤ favg (fun y₂ => f (y₁, y₂) ^ 2) := favg_nonneg fun _ => sq_nonneg _
    calc favg (fun x₂ => g y₁ x₂ ^ q) ^ (1 / r)
        ≤ (favg (fun y₂ => f (y₁, y₂) ^ 2) ^ r) ^ (1 / r) :=
          Real.rpow_le_rpow (favg_nonneg fun _ => Real.rpow_nonneg (hg _ _) _) h (by positivity)
      _ = favg (fun y₂ => f (y₁, y₂) ^ 2) := by rw [one_div, Real.rpow_rpow_inv hF hr0.ne']
  have hA : 0 ≤ favg (fun x₂ => favg (fun y₁ => g y₁ x₂ ^ 2) ^ r) :=
    favg_nonneg fun _ => Real.rpow_nonneg (favg_nonneg fun _ => sq_nonneg _) _
  calc favg (fun x => kapply (Gaussian.ktensor k₁ k₂) f x ^ q)
      ≤ favg (fun x₂ => favg (fun y₁ => g y₁ x₂ ^ 2) ^ r) := step1
    _ = (favg (fun x₂ => favg (fun y₁ => g y₁ x₂ ^ 2) ^ r) ^ (1 / r)) ^ r := by
        rw [one_div, Real.rpow_inv_rpow hA hr0.ne']
    _ ≤ favg (fun y₁ => favg (fun y₂ => f (y₁, y₂) ^ 2)) ^ r := by
        refine Real.rpow_le_rpow (Real.rpow_nonneg hA _) (step2.trans (favg_mono step3)) hr0.le
    _ = favg (fun x => f x ^ 2) ^ (q / 2) := by rw [favg_prod (fun x : α × β => f x ^ 2)]

/-- Hypercontractivity transported along an equivalence of finite types. -/
theorem IsHypercontractive.of_equiv {q : ℝ} (e : α ≃ β) {k : α → α → ℝ} {k' : β → β → ℝ}
    (hkk' : ∀ x y, k' (e x) (e y) = k x y) (h : IsHypercontractive q k) :
    IsHypercontractive q k' := by
  intro f hf
  have hka : ∀ x, kapply k' f (e x) = kapply k (fun y => f (e y)) x := by
    intro x
    simp only [kapply]
    rw [← Equiv.sum_comp e]
    simp only [hkk']
  have h1 := h (fun y => f (e y)) (fun _ => hf _)
  rw [← favg_equiv e, ← favg_equiv e (fun x => f x ^ 2)]
  simpa only [hka] using h1

/-- **Hölder duality**: for a symmetric nonnegative kernel, a `(p,2)` bound on nonnegative
functions implies the `(2,q)` bound for the conjugate exponent `q = p/(p-1)`. -/
theorem isHypercontractive_of_dual {p q : ℝ} (hpq : p.HolderConjugate q) {k : α → α → ℝ}
    (hk : ∀ x y, 0 ≤ k x y) (hsymm : ∀ x y, k x y = k y x)
    (hdual : ∀ g : α → ℝ, (∀ x, 0 ≤ g x) →
      favg (fun x => kapply k g x ^ 2) ≤ favg (fun x => g x ^ p) ^ (2 / p)) :
    IsHypercontractive q k := by
  intro f hf
  have hp1 : 1 < p := hpq.lt
  have hq1 : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set h : α → ℝ := kapply k f with hhdef
  have hh : ∀ x, 0 ≤ h x := kapply_nonneg hk hf
  set g : α → ℝ := fun x => h x ^ (q - 1) with hgdef
  have hg : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (hh x) _
  set A : ℝ := favg (fun x => h x ^ q) with hAdef
  set F : ℝ := favg (fun x => f x ^ 2) with hFdef
  have hA0 : 0 ≤ A := favg_nonneg fun x => Real.rpow_nonneg (hh x) _
  have hF0 : 0 ≤ F := favg_nonneg fun x => sq_nonneg _
  -- `A = favg (f * k g)` by symmetry of the kernel.
  have hAeq : A = favg (fun x => f x * kapply k g x) := by
    have h1 : ∀ x, h x ^ q = h x * g x := by
      intro x
      have := Real.rpow_add' (hh x) (show (1 : ℝ) + (q - 1) ≠ 0 by linarith)
      rw [show (1 : ℝ) + (q - 1) = q by ring, Real.rpow_one] at this
      exact this
    simp only [hAdef, h1, favg]
    congr 1
    simp only [hhdef, kapply, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by rw [hsymm]; ring
  -- `g ^ p = h ^ q`.
  have hgp : favg (fun x => g x ^ p) = A := by
    simp only [hgdef, hAdef]
    congr 1
    funext x
    rw [← Real.rpow_mul (hh x)]
    congr 1
    have := hpq.inv_add_inv_eq_one
    field_simp at this ⊢
    linarith
  have hCS := favg_mul_sq_le f (kapply k g)
  have hdg := hdual g hg
  rw [hgp] at hdg
  have key : A ^ 2 ≤ F * A ^ (2 / p) := by
    calc A ^ 2 = favg (fun x => f x * kapply k g x) ^ 2 := by rw [← hAeq]
      _ ≤ F * favg (fun x => kapply k g x ^ 2) := hCS
      _ ≤ F * A ^ (2 / p) := mul_le_mul_of_nonneg_left hdg hF0
  rcases hA0.eq_or_lt with hA | hA
  · rw [← hA]
    exact Real.rpow_nonneg hF0 _
  · -- `A ^ (2/q) ≤ F`
    have h2q : A ^ (2 / q) ≤ F := by
      have hsplit : A ^ (2 : ℝ) = A ^ (2 / q) * A ^ (2 / p) := by
        rw [← Real.rpow_add hA]
        congr 1
        have := hpq.inv_add_inv_eq_one
        field_simp at this ⊢
        linarith
      have hApos : 0 < A ^ (2 / p) := Real.rpow_pos_of_pos hA _
      have : A ^ (2 / q) * A ^ (2 / p) ≤ F * A ^ (2 / p) := by
        rw [← hsplit, Real.rpow_two]
        exact key
      exact le_of_mul_le_mul_right this hApos
    calc A = (A ^ (2 / q)) ^ (q / 2) := by
          rw [← Real.rpow_mul hA.le]
          field_simp
          simp
      _ ≤ F ^ (q / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) h2q (by positivity)

end WaveTurbulence.Gaussian
