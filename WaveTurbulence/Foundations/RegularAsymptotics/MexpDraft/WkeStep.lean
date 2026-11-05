/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeRec

/-!
# The recursion step `U_{n+1} = δ ∑ ∫ 𝒦(U, U, U)`

`U_succ`: for `t ≥ p`,
`U_{n+1}(t, k) = δ ∑_{n₁+n₂+n₃=n} ∑_{e₁,e₂,e₃} ∫_p^t β₁β₂β₃ · (𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃)(ℳ*_{e₁}, ℳ*_{e₂}, ℳ*_{e₃})(k)`,
which by `integral_collisionOp_U` is `δ ∑ ∫_p^t 𝒦(U_{n₁}, U_{n₂}, U_{n₃})`.
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset
open scoped SchwartzMap

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel WaveTurbulence.WKE

variable {d : ℕ} (δ p : ℝ) (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ))

/-- The weight `[|Z| = 0] 2^{-2N} δ^N ζ*(e) ℳ*_e(k)`. -/
noncomputable def wN (N : ℕ) (k : Mom d) (e : ECpl) : ℝ :=
  if e.shape.zcount = 0 then cn δ N * (e.shape.netSign : ℝ) * Mshape F e.shape k else 0

theorem wN_congr (N : ℕ) (k : Mom d) {e e' : ECpl} (h : Shape.Equiv e.shape e'.shape) :
    wN δ F N k e = wN δ F N k e' := by
  simp only [wN, h.zcount_eq, h.netSign_eq, mshape_congr F h]

theorem I3_eval (e₁ e₂ e₃ : ECpl) (t : ℝ) :
    I3 δ p e₁ e₂ e₃ t = if e₁.shape.zcount = 0 ∧ e₂.shape.zcount = 0 ∧ e₃.shape.zcount = 0 then
      cn δ e₁.hsize * cn δ e₂.hsize * cn δ e₃.hsize *
        ((e₁.shape.netSign : ℝ) * e₂.shape.netSign * e₃.shape.netSign) *
        ∫ u in p..t, e₁.JB p u u * e₂.JB p u u * e₃.JB p u u else 0 := by
  unfold I3 beta
  split_ifs with h h₁ h₂ h₃ h₃ h₂ h₃ h₃ <;> simp_all
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext u; ring

theorem I3_comm₁ (e₁ e₂ e₃ : ECpl) (t : ℝ) : I3 δ p e₁ e₂ e₃ t = I3 δ p e₂ e₃ e₁ t := by
  unfold I3; congr 1; funext u; ring

theorem I3_comm₂ (e₁ e₂ e₃ : ECpl) (t : ℝ) : I3 δ p e₁ e₂ e₃ t = I3 δ p e₁ e₃ e₂ t := by
  unfold I3; congr 1; funext u; ring

/-! ### Reordering nested sums -/

theorem sum4_comm {α β γ ε M : Type*} [AddCommMonoid M] (A : Finset α) (B : Finset β) (C : Finset γ)
    (E : Finset ε) (f : α → β → γ → ε → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ E, f a b c e = ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ E, ∑ a ∈ A, f a b c e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem sum5_comm {α α' β γ ε M : Type*} [AddCommMonoid M] (A : Finset α) (A' : Finset α')
    (B : Finset β) (C : Finset γ) (E : Finset ε) (f : α → α' → β → γ → ε → M) :
    ∑ a ∈ A, ∑ a' ∈ A', ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ E, f a a' b c e =
      ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ E, ∑ a ∈ A, ∑ a' ∈ A', f a a' b c e := by
  rw [← Finset.sum_product']
  rw [sum4_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun e _ => ?_
  exact Finset.sum_product' (s := A) (t := A') (f := fun a a' => f a a' b c e)

theorem sum_miniTreeCode {M : Type*} [AddCommMonoid M] (f : MiniTreeCode → M) :
    ∑ m : MiniTreeCode, f m = ∑ c : Fin 3, (f ⟨c, 0⟩ + f ⟨c, 1⟩) := by
  rw [← Fintype.sum_equiv MiniTreeCode.equiv.symm (fun q : Fin 3 × Fin 2 => f ⟨q.1, q.2⟩) _ fun q => rfl,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.sum_univ_two]

/-! ### The type 1 terms -/

theorem t1_term {n : ℕ} {x : Fin 3 → ℕ} (hx : x 0 + x 1 + x 2 = n) {e₁ e₂ e₃ : ECpl}
    (h₁ : e₁ ∈ ED (x 0)) (h₂ : e₂ ∈ ED (x 1)) (h₃ : e₃ ∈ ED (x 2)) (t : ℝ) (k : Mom d) :
    ∑ c : MiniCplCode, wN δ F (n + 1) k (.type1 c e₁ e₂ e₃) *
        (2 * ∫ u in p..t, e₁.JB p u u * e₂.JB p u u * e₃.JB p u u) =
      δ * (I3 δ p e₁ e₂ e₃ t * collisionTerm 0 (MS hd F e₁.shape) (MS hd F e₂.shape)
        (MS hd F e₃.shape) k) := by
  rw [mem_ED] at h₁ h₂ h₃
  rw [Fin.sum_univ_two, I3_eval, h₁.2, h₂.2, h₃.2]
  simp only [wN, ECpl.shape, Shape.zcount, Nat.add_eq_zero_iff, Shape.netSign, and_assoc]
  split_ifs with h
  · rw [MS_eq hd F _ h.1, MS_eq hd F _ h.2.1, MS_eq hd F _ h.2.2]
    have hc : cn δ (n + 1) * 4 = δ * (cn δ (x 0) * cn δ (x 1) * cn δ (x 2)) := by
      rw [cn_succ, ← hx, cn_add3]
    have hK : collisionKernel 0 (Mshape F e₁.shape) (Mshape F e₂.shape) (Mshape F e₃.shape) k =
        fun ℓ x => Mshape F e₁.shape (k + ℓ) * Mshape F e₂.shape (k + ℓ + x) *
          Mshape F e₃.shape (k + x) := rfl
    simp only [Mshape, collisionTerm, resIntegral_eq_deltaInt, hK]
    push_cast
    linear_combination (∫ u in p..t, e₁.JB p u u * e₂.JB p u u * e₃.JB p u u) *
      ((e₁.shape.netSign : ℝ) * e₂.shape.netSign * e₃.shape.netSign) *
      deltaInt (fun ℓ x => Mshape F e₁.shape (k + ℓ) * Mshape F e₂.shape (k + ℓ + x) *
        Mshape F e₃.shape (k + x)) * hc
  · simp

/-! ### The chain terms -/

theorem wN_prepP_false (N : ℕ) (k : Mom d) (m : MiniTreeCode) (er eg e' : ECpl) :
    wN δ F N k (prepP m false er eg e') =
      if er.shape.zcount = 0 ∧ eg.shape.zcount = 0 ∧ e'.shape.zcount = 0 then
        cn δ N * ((codeSign m.c : ℝ) * er.shape.netSign * eg.shape.netSign * e'.shape.netSign) *
          CT hd m.c (MS hd F er.shape) (MS hd F eg.shape) (MS hd F e'.shape) k
      else 0 := by
  simp only [wN, shape_prepP, zcount_consShape, netSign_consShape, mshape_consShape,
    Bool.false_eq_true, ↓reduceIte, zero_add, Nat.add_eq_zero_iff, and_assoc]
  split_ifs with h
  · rw [← npair_mul hd, MS_eq hd F _ h.1, MS_eq hd F _ h.2.1, MS_eq hd F _ h.2.2]
    push_cast; ring
  · rfl

theorem wN_prepP_true (N : ℕ) (k : Mom d) (m : MiniTreeCode) (er eg e' : ECpl) :
    wN δ F N k (prepP m true er eg e') = 0 := by
  simp only [wN, shape_prepP, zcount_consShape, ↓reduceIte]
  split_ifs with h
  · omega
  · rfl

theorem chain_term {n : ℕ} {x : Fin 3 → ℕ} (hx : x 0 + x 1 + x 2 = n) {er eg e' : ECpl}
    (h₁ : er ∈ ED (x 0)) (h₂ : eg ∈ ED (x 1)) (h₃ : e' ∈ ED (x 2)) (t : ℝ) (k : Mom d) :
    ∑ m : MiniTreeCode, ∑ I : Bool,
      ((wN δ F (n + 1) k (prepP m I er eg e') * ∫ u in p..t, er.JB p u u * eg.JB p u u * e'.JB p u u) +
        (wN δ F (n + 1) k (prepM m I er eg e') * ∫ u in p..t, er.JB p u u * eg.JB p u u * e'.JB p u u)) =
      δ * ∑ c : Fin 3, (codeSign c : ℝ) * I3 δ p er eg e' t *
        CT hd c (MS hd F er.shape) (MS hd F eg.shape) (MS hd F e'.shape) k := by
  have hM : ∀ m I, wN δ F (n + 1) k (prepM m I er eg e') = wN δ F (n + 1) k (prepP m I er eg e') :=
    fun m I => wN_congr δ F _ k (by rw [shape_prepP]; exact shape_prepM_equiv m I er eg e')
  simp only [hM, Fintype.sum_bool, wN_prepP_true, zero_mul, add_zero, zero_add,
    wN_prepP_false δ hd F]
  rw [sum_miniTreeCode, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mem_ED] at h₁ h₂ h₃
  rw [I3_eval, h₁.2, h₂.2, h₃.2]
  have hc : cn δ (n + 1) * 4 = δ * (cn δ (x 0) * cn δ (x 1) * cn δ (x 2)) := by
    rw [cn_succ, ← hx, cn_add3]
  split_ifs
  · linear_combination ((codeSign c : ℝ) * er.shape.netSign * eg.shape.netSign * e'.shape.netSign) *
      CT hd c (MS hd F er.shape) (MS hd F eg.shape) (MS hd F e'.shape) k *
      (∫ u in p..t, er.JB p u u * eg.JB p u u * e'.JB p u u) * hc
  · simp

end WaveTurbulence.Mexp
