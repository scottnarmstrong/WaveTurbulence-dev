/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.WkeStep

/-!
# `U_n = 𝒰_n`: the `Z = ∅` leading terms are the WKE Taylor terms

* `U_succ`: the peeled form of `U_{n+1}` (type 1 terms give `𝒦₀`; chain terms with `𝚌 = 1, 2, 3` give
  `−𝒦₁, +𝒦₂, −𝒦₃` after permuting the antidiagonal).
* **`U_eq_wkeTaylorTerm`**: `U_n(t) = 𝒰^{(p)}_n(t)` for `t ≥ p` (B1 `wkeTaylorTerm`, T (wketaylor2)).
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral Finset
open scoped SchwartzMap

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel WaveTurbulence.WKE

variable {d : ℕ} (δ p : ℝ) (hd : 2 ≤ d) (F : 𝓢(Mom d, ℝ))

/-- The triple sum of `I3 · 𝒦ⱼ` in normal slot order. -/
noncomputable def Sj (j : Fin 4) (x : Fin 3 → ℕ) (t : ℝ) (k : Mom d) : ℝ :=
  ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2),
    I3 δ p e₁ e₂ e₃ t * collisionTerm j (MS hd F e₁.shape) (MS hd F e₂.shape) (MS hd F e₃.shape) k

theorem sum3_rot {α M : Type*} [AddCommMonoid M] (A B C : Finset α) (f : α → α → α → M) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem chain1_reindex (n : ℕ) (t : ℝ) (k : Mom d) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
      I3 δ p er eg e' t * collisionTerm 1 (MS hd F e'.shape) (MS hd F er.shape) (MS hd F eg.shape) k =
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, Sj δ p hd F 1 x t k := by
  rw [sum_antidiag_rot n (fun a b c => ∑ er ∈ ED a, ∑ eg ∈ ED b, ∑ e' ∈ ED c,
    I3 δ p er eg e' t * collisionTerm 1 (MS hd F e'.shape) (MS hd F er.shape) (MS hd F eg.shape) k)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum3_rot]
  simp only [Sj]
  refine Finset.sum_congr rfl fun e₁ _ => Finset.sum_congr rfl fun e₂ _ =>
    Finset.sum_congr rfl fun e₃ _ => ?_
  rw [I3_comm₁ δ p e₁ e₂ e₃]

theorem chain2_reindex (n : ℕ) (t : ℝ) (k : Mom d) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
      I3 δ p er eg e' t * collisionTerm 2 (MS hd F er.shape) (MS hd F e'.shape) (MS hd F eg.shape) k =
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n, Sj δ p hd F 2 x t k := by
  rw [sum_antidiag_swap n (fun a b c => ∑ er ∈ ED a, ∑ eg ∈ ED b, ∑ e' ∈ ED c,
    I3 δ p er eg e' t * collisionTerm 2 (MS hd F er.shape) (MS hd F e'.shape) (MS hd F eg.shape) k)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Sj]
  refine Finset.sum_congr rfl fun e₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e₂ _ => Finset.sum_congr rfl fun e₃ _ => ?_
  rw [I3_comm₂ δ p e₁ e₂ e₃]

/-- **The peeled form of `U_{n+1}`.** -/
theorem U_succ (n : ℕ) {t : ℝ} (hpt : p ≤ t) (k : Mom d) :
    U δ p hd F (n + 1) t k = δ * ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2), I3 δ p e₁ e₂ e₃ t * Ksum hd F e₁ e₂ e₃ k := by
  rw [U_apply]
  have step1 : ∀ e ∈ ED (n + 1), beta δ p e t * MS hd F e.shape k = wN δ F (n + 1) k e * e.JB p t t := by
    intro e he
    rw [mem_ED] at he
    unfold beta wN
    rw [he.2]
    split_ifs with h
    · rw [MS_eq hd F _ h]; ring
    · simp
  rw [Finset.sum_congr rfl step1, Finset.sum_congr rfl fun e he => weighted_JB_decomp_real p
    (wN δ F (n + 1) k) (mem_ED.1 he).1 (by rw [(mem_ED.1 he).2]; omega) hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_t1Part, sum_plusPart, sum_minusPart,
    add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- the per-`x` identity
  have key : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 n,
      (∑ c : MiniCplCode, ∑ e₁ ∈ ED (x 0), ∑ e₂ ∈ ED (x 1), ∑ e₃ ∈ ED (x 2),
        wN δ F (n + 1) k (.type1 c e₁ e₂ e₃) *
          (2 * ∫ u in p..t, e₁.JB p u u * e₂.JB p u u * e₃.JB p u u)) +
      ((∑ m : MiniTreeCode, ∑ I : Bool, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
        wN δ F (n + 1) k (prepP m I er eg e') * ∫ u in p..t, er.JB p u u * eg.JB p u u * e'.JB p u u) +
      ∑ m : MiniTreeCode, ∑ I : Bool, ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
        wN δ F (n + 1) k (prepM m I er eg e') * ∫ u in p..t, er.JB p u u * eg.JB p u u * e'.JB p u u) =
      δ * (Sj δ p hd F 0 x t k + ∑ er ∈ ED (x 0), ∑ eg ∈ ED (x 1), ∑ e' ∈ ED (x 2),
        (-(I3 δ p er eg e' t * collisionTerm 1 (MS hd F e'.shape) (MS hd F er.shape) (MS hd F eg.shape) k)
          + I3 δ p er eg e' t * collisionTerm 2 (MS hd F er.shape) (MS hd F e'.shape) (MS hd F eg.shape) k
          - I3 δ p er eg e' t * collisionTerm 3 (MS hd F er.shape) (MS hd F eg.shape) (MS hd F e'.shape) k)) := by
    intro x hx
    rw [mem_antidiag3] at hx
    simp only [← Finset.sum_add_distrib]
    rw [sum4_comm (Finset.univ : Finset MiniCplCode), sum5_comm (Finset.univ : Finset MiniTreeCode),
      mul_add, Sj, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun e₁ h₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₂ h₂ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e₃ h₃ => ?_
      exact t1_term δ p hd F hx h₁ h₂ h₃ t k
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun er h₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun eg h₂ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e' h₃ => ?_
      rw [chain_term δ p hd F hx h₁ h₂ h₃ t k, Fin.sum_univ_three]
      congr 1
      simp only [CT, codeSign, Fin.isValue, ↓reduceIte, coe_collisionTermSchwartz, Fin.reduceEq,
        one_ne_zero, Int.reduceNeg, Int.cast_neg, Int.cast_one]
      ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [chain1_reindex, chain2_reindex]
  simp only [Ksum, Sj, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem ED_zero : ED 0 = {ECpl.triv} := by
  ext e
  rw [mem_ED, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hs⟩; exact ECpl.eq_triv_of_hsize hw hs
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **The `Z = ∅` leading terms are the WKE Taylor terms**: `U_n(t) = 𝒰^{(p)}_n(t)` for `t ≥ p`. -/
theorem U_eq_wkeTaylorTerm (n : ℕ) {t : ℝ} (hpt : p ≤ t) :
    ⇑(U δ p hd F n t) = wkeTaylorTerm F δ p n t := by
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ih =>
  rcases n with _ | n
  · funext k
    rw [U_apply, ED_zero, Finset.sum_singleton, wkeTaylorTerm]
    simp [beta, cn, ECpl.shape, Shape.zcount, Shape.netSign, ECpl.JB, ECpl.code, RegCpl.JB, MS,
      ECpl.hsize]
  · funext k
    rw [U_succ δ p hd F n hpt, wkeTaylorTerm]
    congr 1
    rw [Finset.sum_attach (Finset.Nat.antidiagonalTuple 3 n) (fun x =>
      ∫ t' in p..t, collisionOp (wkeTaylorTerm F δ p (x 0) t') (wkeTaylorTerm F δ p (x 1) t')
        (wkeTaylorTerm F δ p (x 2) t') k)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hle : ∀ i, x i < n + 1 := by
      rw [mem_antidiag3] at hx
      intro i; fin_cases i <;> simp <;> omega
    rw [← integral_collisionOp_U]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hpt] at hu
    simp only [ih _ (hle 0) hu.1, ih _ (hle 1) hu.1, ih _ (hle 2) hu.1]

end WaveTurbulence.Mexp
