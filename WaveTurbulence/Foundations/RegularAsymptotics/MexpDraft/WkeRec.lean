/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.MSchwartz

/-!
# The `Z = ∅` leading terms satisfy the WKE Taylor recursion

`U n t = ∑_{e ∈ ED n, |Z| = 0} 2^{-2n} δ^n ζ*(e) 𝒥ℬ*_e(t, t) ℳ*_e`, a Schwartz function of `k`. DH21 Props 7.9 and 7.10
match it with the WKE Taylor term through encoded trees and the class sums `𝒢_X = 2^{2n} ∑ g_𝒯`. Here
`U` is shown to satisfy the defining recursion of the Taylor terms directly (`U_succ`):

  `U_{n+1}(t) = δ ∑_{n₁+n₂+n₃=n} ∫_p^t 𝒦(U_{n₁}(u), U_{n₂}(u), U_{n₃}(u)) du`     (`t ≥ p`).

Peeling the latest time (`weighted_JB_decomp_real`):

* the type 1 root gives `𝒦₀` (factor `2` of (recurtype1) times the two mini-couple codes = `2²`);
* a top chain pair with first digit `𝚌` gives `±𝒦_𝚌` (two chains times the two second digits = `2²`;
  sign `codeSign = (−1)^{𝚌}`), the remaining couple in the slot `𝚌` evaluated at `k`;
* the bits `𝙸 = 1` do not occur since `|Z| = 0`.

On the other side `𝒦 = 𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃` is expanded trilinearly (`collisionTerm_sum₃`).
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset
open scoped SchwartzMap

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel WaveTurbulence.WKE

variable {d : ℕ}

/-- The real form of `weighted_JB_decomp`. -/
theorem weighted_JB_decomp_real (r : ℝ) (w : ECpl → ℝ) {e : ECpl} (hw : e.wf = true)
    (hn : e.hsize ≠ 0) {t : ℝ} (hrt : r ≤ t) :
    w e * e.JB r t t =
      t1Part (fun c e₁ e₂ e₃ => w (.type1 c e₁ e₂ e₃) *
        (2 * ∫ u in r..t, e₁.JB r u u * e₂.JB r u u * e₃.JB r u u)) e +
      plusPart (fun m I er eg e' => w (prepP m I er eg e') *
        ∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u) e +
      minusPart (fun m I er eg e' => w (prepM m I er eg e') *
        ∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u u) e := by
  cases e with
  | triv => simp [ECpl.hsize] at hn
  | type1 c e₁ e₂ e₃ =>
    simp only [t1Part, plusPart, minusPart, add_zero]
    congr 1
    simp [ECpl.JB, ECpl.code, RegCpl.JB]
  | type2 X Y L =>
    have hL : L.isType2 = false := by
      simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
      exact hw.1.2
    rw [JB_diag r X Y L hw hrt, mul_add]
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

/-! ### Definitions -/

variable (δ p : ℝ)

/-- `2^{-2n} δ^n`. -/
noncomputable def cn (n : ℕ) : ℝ := (2⁻¹ : ℝ) ^ (2 * n) * δ ^ n

theorem cn_add3 (a b c : ℕ) : cn δ (a + b + c) = cn δ a * cn δ b * cn δ c := by
  simp only [cn, mul_add, pow_add]; ring

theorem cn_succ (n : ℕ) : cn δ (n + 1) * 4 = δ * cn δ n := by
  simp only [cn, mul_add, pow_add, mul_one, pow_one]; norm_num; ring

/-- The time coefficient `β_e(u) = [|Z| = 0] 2^{-2n} δ^n ζ*(e) 𝒥ℬ*_e(u, u)`. -/
noncomputable def beta (e : ECpl) (u : ℝ) : ℝ :=
  if e.shape.zcount = 0 then cn δ e.hsize * (e.shape.netSign : ℝ) * e.JB p u u else 0

theorem beta_continuous (e : ECpl) : Continuous (beta δ p e) := by
  unfold beta
  split_ifs
  · exact continuous_const.mul (JB_diag_continuous p _)
  · exact continuous_const

/-- **The `Z = ∅` leading terms** `U_n(t) = ∑_{e ∈ ED n} β_e(t) ℳ*_e` (a Schwartz function). -/
noncomputable def U (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) (n : ℕ) (t : ℝ) : 𝓢(Mom d, ℝ) :=
  ∑ e ∈ ED n, beta δ p e t • MS hd F e.shape

theorem U_apply (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ)) (n : ℕ) (t : ℝ) (k : Mom d) :
    U δ p hd F n t k = ∑ e ∈ ED n, beta δ p e t * MS hd F e.shape k := by
  simp [U, _root_.sum_apply, smul_apply]

/-! ### Permuting the antidiagonal -/

theorem sum_antidiag_rot {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → ℕ → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, g (x 0) (x 1) (x 2) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, g (x 1) (x 2) (x 0) := by
  refine Finset.sum_nbij' (fun x => ![x 2, x 0, x 1]) (fun y => ![y 1, y 2, y 0]) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_antidiag3] at hx ⊢; simp; omega
  · intro x hx; simp only [mem_antidiag3] at hx ⊢; simp; omega
  · intro x _; funext i; fin_cases i <;> rfl
  · intro x _; funext i; fin_cases i <;> rfl
  · intro x _; rfl

theorem sum_antidiag_swap {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → ℕ → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, g (x 0) (x 1) (x 2) =
      ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, g (x 0) (x 2) (x 1) := by
  refine Finset.sum_nbij' (fun x => ![x 0, x 2, x 1]) (fun y => ![y 0, y 2, y 1]) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_antidiag3] at hx ⊢; simp; omega
  · intro x hx; simp only [mem_antidiag3] at hx ⊢; simp; omega
  · intro x _; funext i; fin_cases i <;> rfl
  · intro x _; funext i; fin_cases i <;> rfl
  · intro x _; rfl

/-! ### The right side: the collision operator on `U` -/

variable (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ))

/-- `𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃` on the momentum factors of three codes. -/
noncomputable def Ksum (e₁ e₂ e₃ : ECpl) (k : Mom d) : ℝ :=
  collisionTerm 0 (MS hd F e₁.shape) (MS hd F e₂.shape) (MS hd F e₃.shape) k
    - collisionTerm 1 (MS hd F e₁.shape) (MS hd F e₂.shape) (MS hd F e₃.shape) k
    + collisionTerm 2 (MS hd F e₁.shape) (MS hd F e₂.shape) (MS hd F e₃.shape) k
    - collisionTerm 3 (MS hd F e₁.shape) (MS hd F e₂.shape) (MS hd F e₃.shape) k

/-- `∫_p^t β₁ β₂ β₃`. -/
noncomputable def I3 (e₁ e₂ e₃ : ECpl) (t : ℝ) : ℝ :=
  ∫ u in p..t, beta δ p e₁ u * beta δ p e₂ u * beta δ p e₃ u

theorem collisionOp_U (a b c : ℕ) (u : ℝ) (k : Mom d) :
    collisionOp (U δ p hd F a u) (U δ p hd F b u) (U δ p hd F c u) k =
      ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c,
        beta δ p e₁ u * beta δ p e₂ u * beta δ p e₃ u * Ksum hd F e₁ e₂ e₃ k := by
  rw [collisionOp_eq_sum_schwartz hd]
  simp only [U, collisionTerm_sum₃ hd, Ksum]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ =>
    Finset.sum_congr rfl fun e₃ _ => ?_
  ring

/-- **The right side of the recursion**, expanded. -/
theorem integral_collisionOp_U (a b c : ℕ) (t : ℝ) (k : Mom d) :
    ∫ u in p..t, collisionOp (U δ p hd F a u) (U δ p hd F b u) (U δ p hd F c u) k =
      ∑ e₁ ∈ ED a, ∑ e₂ ∈ ED b, ∑ e₃ ∈ ED c, I3 δ p e₁ e₂ e₃ t * Ksum hd F e₁ e₂ e₃ k := by
  simp only [collisionOp_U]
  have hc : ∀ e₁ e₂ e₃ : ECpl, Continuous fun u =>
      beta δ p e₁ u * beta δ p e₂ u * beta δ p e₃ u * Ksum hd F e₁ e₂ e₃ k := fun e₁ e₂ e₃ =>
    (((beta_continuous δ p e₁).mul (beta_continuous δ p e₂)).mul (beta_continuous δ p e₃)).mul
      continuous_const
  rw [intervalIntegral.integral_finsetSum fun e₁ _ => ?_]
  · refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum fun e₂ _ => ?_]
    · refine Finset.sum_congr rfl fun e₂ _ => ?_
      rw [intervalIntegral.integral_finsetSum fun e₃ _ => (hc e₁ e₂ e₃).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun e₃ _ => ?_
      rw [intervalIntegral.integral_mul_const]
      rfl
    · exact (continuous_finsetSum _ fun e₃ _ => hc e₁ e₂ e₃).intervalIntegrable _ _
  · exact (continuous_finsetSum _ fun e₂ _ => continuous_finsetSum _ fun e₃ _ =>
      hc e₁ e₂ e₃).intervalIntegrable _ _

end WaveTurbulence.Mexp
