/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCTExp
public import WaveTurbulence.Foundations.ClassJR.MCConst

/-!
# DH21 Proposition 5.1 for codes of regular trees (DH21 Proposition 6.10)

A regular tree is a regular chain whose leaf pairs are replaced by regular couples (DH21 Remark 4.15).
Its coefficient `Ã_𝒯(t, s, α[𝒩^ch])` (DH21 (varat), with (deftildeb)) is the chain integral of the
chain code `X` (DH21 (newexp2)) with the lone-leaf condition `t_{2m} > s` as continuation
(`RegChain.At`); the garden form is in the B̃ bridge (`treeAstar_eq_Atilde`).

`RegChain.mcexpT`: `Ã_𝒯` has the expansion (maincoef3) for `t > s` (`MCExpT`, DH21 Proposition 6.10,
L1705–L1708) in the chosen nodes of the tree links, with the exponents `(θ, a, b)`, when the couples of
the pairs are expanded with the exponents `(θ', a', b)` (DH21 Proposition 5.1, `RegChain.mcexp_coef`)
and `δ` is the exponent of the difference loss. `RegChain.NtreeX_le`: for a well-formed code its
constant is at most `C_T^{2n(𝒯)+1}`.
-/

public section

open Finset

namespace WaveTurbulence.ClassJR

/-- **DH21's `Ã_𝒯(t, s, α[𝒩^ch])` for a regular tree code** `X` of root sign `ζ` rooted at `x`: the
chain integral (DH21 (newexp2)) with the lone-leaf condition `t_{2m} > s` (DH21 (varat)) as
continuation. -/
@[expose] noncomputable def RegChain.At (X : RegChain) (ζ : ℤˣ) (x : Addr) :
    (Addr → ℝ) → ℝ → ℝ → ℂ :=
  fun α t s => chainT (X.sigmaAt x 0) (fun j => nodeSgn (X.sigmaAt x 0 j)) X.code 0
    (X.coefAt ζ x 0) α t (fun t' => if s < t' then 1 else 0)

section Main

variable {θ a b A θ' a' δ : ℝ}

/-- **DH21 Proposition 5.1 for a regular tree code** (DH21 Proposition 6.10, "for `t > s`"):
`Ã_𝒯` has the expansion (maincoef3) for `t > s` in the chosen nodes of the tree links. -/
theorem RegChain.mcexpT (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b) (hab1 : a + b < 1)
    (hab : a + b ≤ θ) (hA : A1 ≤ A) (hθ'1 : θ' < 1) (ha' : 0 < a') (hab1' : a' + b < 1)
    (hab' : a' + b ≤ θ') (hδ : 0 < δ) (hδθ : δ + θ ≤ θ') (hδa : δ + a ≤ a') (hδb : δ + b ≤ 1)
    (X : RegChain) (ζ : ℤˣ) (x : Addr) :
    MCExpT θ a b A (NtreeX θ a b a' δ X.code (X.NBAt θ' a' b 0)) nodeSgn
      (chosenSet (X.linksAt ζ x)) (X.At ζ x) := by
  have hX := X.chainFacts ζ x 0
  have hθ'0 : 0 ≤ θ' := by linarith
  have key := MCExpT.chain' hθ0 hθ1 ha hb hab1 hab hA ha' hab' hθ'1.le hδ hδθ hδa hδb
    (ζ := nodeSgn) (σ := X.sigmaAt x 0) (ε := fun j => nodeSgn (X.sigmaAt x 0 j))
    (fun j => nodeSgn_eq _) (c := X.code) (fun j _ => rfl) (by simpa using hX.inj)
    (S := X.varsAt ζ x 0) (N := X.NBAt θ' a' b 0) (F := X.coefAt ζ x 0)
    (fun j hj => RegChain.mcexp_coef hθ'0 hθ'1 ha' hb hab1' hab' hA X ζ x 0 j (by simpa using hj))
    (fun j hj k hk hjk => hX.disj j (by simpa using hj) k (by simpa using hk) hjk)
    (fun j hj k hk => hX.sig_notMem j (by simpa using hj) k (by simpa using hk))
  rw [hX.chosen, zero_add]
  exact key

end Main

section Const

variable (θ a b θ' a' δ : ℝ)

/-- The constant of a tree chain step. -/
@[expose] noncomputable def KT : ℝ :=
  max (max 1 (N1 θ)) (64 * N1 θ * KH θ a b) * max 1 (32 * (1 + KPT a' b δ) * C510 θ)

/-- **The constant `C_T` of DH21 Proposition 5.1 for regular trees.** -/
@[expose] noncomputable def CT : ℝ := max (4 * KT θ a b a' δ) (C0 θ' a' b)

theorem one_le_KT : 1 ≤ KT θ a b a' δ :=
  one_le_mul_of_one_le_of_one_le ((le_max_left _ _).trans (le_max_left _ _)) (le_max_left _ _)

theorem one_le_CT : 1 ≤ CT θ a b θ' a' δ :=
  (one_le_C0 θ' a' b).trans (le_max_right _ _)

variable {θ a b θ' a' δ}

/-- **The constant of a tree chain**: `NtreeX ≤ K_T^{m+1} ∏_j max(1, N_j)`. -/
theorem NtreeX_le (c : LegalCode) {N : ℕ → ℝ} (hN : ∀ j, 0 ≤ N j) :
    NtreeX θ a b a' δ c N ≤ KT θ a b a' δ ^ (c.size + 1) * ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
  have hK1 := one_le_KT θ a b a' δ
  have hP1 : 1 ≤ ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) :=
    Finset.one_le_prod₀ fun j _ => le_max_left _ _
  have hKH := KH_nonneg θ a b
  have hKP := KPT_nonneg a' b δ
  have hC5 := one_le_C510 θ
  have hN1 : 0 ≤ N1 θ := by unfold N1; positivity
  have hKa : 1 ≤ max (max 1 (N1 θ)) (64 * N1 θ * KH θ a b) := (le_max_left _ _).trans (le_max_left _ _)
  have hKb : 1 ≤ max 1 (32 * (1 + KPT a' b δ) * C510 θ) := le_max_left _ _
  refine max_le ?_ ?_
  · calc N1 θ = N1 θ * 1 * 1 := by ring
      _ ≤ KT θ a b a' δ * KT θ a b a' δ ^ c.size * ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
          gcongr
          · exact ((le_max_right _ _).trans (le_max_left _ _)).trans
              (le_mul_of_one_le_right (by positivity) hKb)
          · exact one_le_pow₀ hK1
      _ = _ := by rw [pow_succ]; ring
  · have hPN : ∏ j ∈ Finset.Ico 0 c.size, (1 + KPT a' b δ) * N j ≤
        (1 + KPT a' b δ) ^ c.size * ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.sub_zero]
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => hN j) fun j _ =>
        le_max_right _ _) (by positivity)
    have hk1 : 64 * N1 θ * KH θ a b ≤ KT θ a b a' δ :=
      (le_max_right _ _).trans (le_mul_of_one_le_right (by positivity) hKb)
    have hk2 : 32 * (1 + KPT a' b δ) * C510 θ ≤ KT θ a b a' δ :=
      (le_max_right _ _).trans (le_mul_of_one_le_left (by positivity) hKa)
    unfold Ntree
    rw [NT_eq, zero_add]
    calc 2 ^ (c.size + 1) * (2 * (4 * (4 * (16 ^ c.size *
          ∏ j ∈ Finset.Ico 0 c.size, (1 + KPT a' b δ) * N j) * N1 θ) * (KH θ a b * C510 θ ^ c.size)))
        ≤ 2 ^ (c.size + 1) * (2 * (4 * (4 * (16 ^ c.size * ((1 + KPT a' b δ) ^ c.size *
            ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j))) * N1 θ) * (KH θ a b * C510 θ ^ c.size))) := by
          gcongr
      _ = (64 * N1 θ * KH θ a b) * (32 * (1 + KPT a' b δ) * C510 θ) ^ c.size *
            ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
          rw [mul_pow, mul_pow, pow_succ, show (32 : ℝ) ^ c.size = 2 ^ c.size * 16 ^ c.size by
            rw [← mul_pow]; norm_num]
          ring
      _ ≤ KT θ a b a' δ * KT θ a b a' δ ^ c.size * ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
          gcongr
      _ = _ := by rw [pow_succ]; ring

/-- A chain has at most `n(𝒯)/2` pairs. -/
theorem RegChain.two_mul_code_size_le : ∀ X : RegChain, 2 * X.code.size ≤ X.size
  | .nil => by simp [RegChain.code, LegalCode.size, RegChain.size]
  | .pair _ Qr Qg inner rest => by
    have hi := RegChain.two_mul_code_size_le inner
    have hr := RegChain.two_mul_code_size_le rest
    simp only [RegChain.code, LegalCode.size, RegChain.size]
    omega

/-- **The constant of DH21 Proposition 5.1 for a regular tree**: `NtreeX ≤ C_T^{2n(𝒯)+1}` for a
well-formed code. -/
theorem RegChain.NtreeX_le_CT (X : RegChain) (hX : X.wf = true) :
    NtreeX θ a b a' δ X.code (X.NBAt θ' a' b 0) ≤ CT θ a b θ' a' δ ^ (2 * X.size + 1) := by
  obtain ⟨hN, hP⟩ := RegChain.NBAt_le (θ := θ') (a := a') (b := b) X 0 hX
  set m := X.code.size with hm
  set n := X.size with hn
  have hmn : 2 * m ≤ n := RegChain.two_mul_code_size_le X
  have hC0 := one_le_C0 θ' a' b
  have hCT := one_le_CT θ a b θ' a' δ
  have hK1 := one_le_KT θ a b a' δ
  have hP0 : 0 ≤ ∏ j ∈ Finset.Ico 0 m, max 1 (X.NBAt θ' a' b 0 j) :=
    Finset.prod_nonneg fun j _ => zero_le_one.trans (le_max_left _ _)
  -- the product of the pair constants
  have hP' : ∏ j ∈ Finset.Ico 0 m, max 1 (X.NBAt θ' a' b 0 j) ≤ 4 ^ m * C0 θ' a' b ^ (2 * n - 2 * m) := by
    have hP2 : (∏ j ∈ Finset.Ico 0 m, max 1 (X.NBAt θ' a' b 0 j)) * C0 θ' a' b ^ (2 * m) ≤
        (4 ^ m * C0 θ' a' b ^ (2 * n - 2 * m)) * C0 θ' a' b ^ (2 * m) := by
      have e : C0 θ' a' b ^ (2 * n) = C0 θ' a' b ^ (2 * n - 2 * m) * C0 θ' a' b ^ (2 * m) := by
        rw [← pow_add]; congr 1; omega
      simpa [zero_add, e, mul_assoc] using hP
    exact le_of_mul_le_mul_right hP2 (pow_pos (by linarith) _)
  calc NtreeX θ a b a' δ X.code (X.NBAt θ' a' b 0)
      ≤ KT θ a b a' δ ^ (m + 1) * ∏ j ∈ Finset.Ico 0 m, max 1 (X.NBAt θ' a' b 0 j) :=
        NtreeX_le X.code hN
    _ ≤ KT θ a b a' δ ^ (m + 1) * (4 ^ m * C0 θ' a' b ^ (2 * n - 2 * m)) := by gcongr
    _ ≤ (4 * KT θ a b a' δ) ^ (m + 1) * C0 θ' a' b ^ (2 * n - 2 * m) := by
        rw [mul_pow, pow_succ (4 : ℝ)]
        have : (0 : ℝ) ≤ KT θ a b a' δ ^ (m + 1) * 4 ^ m * C0 θ' a' b ^ (2 * n - 2 * m) := by positivity
        nlinarith
    _ ≤ CT θ a b θ' a' δ ^ (m + 1) * CT θ a b θ' a' δ ^ (2 * n - 2 * m) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = CT θ a b θ' a' δ ^ (2 * n - m + 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ CT θ a b θ' a' δ ^ (2 * n + 1) := pow_le_pow_right₀ hCT (by omega)

end Const

end WaveTurbulence.ClassJR
