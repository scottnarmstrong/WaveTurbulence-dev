/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCMain

/-!
# The constant of DH21 Proposition 5.1

The constant `Q.NB θ a b` of the recursion is at most `C₀^{2n(Q)+1}` for a well-formed code
(`RegCpl.NB_le`), where `n(Q)` is the order of `Q` (`RegCpl.size`) and `C₀ = C0 θ a b`. This is DH21's
`C^n` up to the choice of `C` (`n(Q) = 2n` for a couple of scale `2n`; the trivial couple gets `C₀`
instead of `1`, see `MCOne`). Well-formedness is used once: a type 2 code has at least one chain pair,
which pays for the constants of the chains.
-/

public section

open Finset

namespace WaveTurbulence.ClassJR

section NT

/-- **The product of the pair constants**: `NT NP c q = 16^m ∏_{j ∈ [q, q+m)} NP_j`. -/
theorem NT_eq (NP : ℕ → ℝ) : ∀ (c : LegalCode) (q : ℕ),
    NT NP c q = 16 ^ c.size * ∏ j ∈ Finset.Ico q (q + c.size), NP j
  | .nil, q => by simp [NT, LegalCode.size]
  | .node i r, q => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hsplit : Finset.Ico q (q + (LegalCode.node i r).size) =
        insert q (Finset.Ico (q + 1) (q + 1 + i.size) ∪ Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_union, hsz]
      omega
    have hnq : q ∉ Finset.Ico (q + 1) (q + 1 + i.size) ∪ Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size) := by
      simp only [Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.Ico (q + 1) (q + 1 + i.size)) (Finset.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) := by
      rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
    rw [NT, NT_eq NP i (q + 1), NT_eq NP r (q + i.size + 1), hsplit, Finset.prod_insert hnq,
      Finset.prod_union hd, hsz]
    ring

end NT

section Chain

variable (θ a b : ℝ)

/-- The constant of a chain step. -/
@[expose] noncomputable def Kch : ℝ :=
  max 1 (32 * KH θ a b) * max 1 (32 * (1 + KPD a b) * C510 θ)

theorem one_le_Kch : 1 ≤ Kch θ a b := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)

variable {θ a b}

/-- **The constant of a chain with a bottom coefficient**:
`Nchain' ≤ K^{m+1} ∏_j max(1, N_j) N_b`. -/
theorem Nchain'_le (c : LegalCode) {N : ℕ → ℝ} (hN : ∀ j, 0 ≤ N j) {Nb : ℝ} (hNb : 0 ≤ Nb) :
    Nchain' θ a b c N Nb ≤
      Kch θ a b ^ (c.size + 1) * (∏ j ∈ Finset.Ico 0 c.size, max 1 (N j)) * Nb := by
  have hK1 := one_le_Kch θ a b
  have hP1 : 1 ≤ ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) :=
    Finset.one_le_prod₀ fun j _ => le_max_left _ _
  have hKH := KH_nonneg θ a b
  have hKPD := KPD_nonneg a b
  have hC5 := one_le_C510 θ
  have hPN : ∏ j ∈ Finset.Ico 0 c.size, (1 + KPD a b) * N j ≤
      (1 + KPD a b) ^ c.size * ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.sub_zero]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => hN j) fun j _ =>
      le_max_right _ _) (by positivity)
  refine max_le ?_ ?_
  · calc Nb = 1 * 1 * Nb := by ring
      _ ≤ Kch θ a b ^ (c.size + 1) * (∏ j ∈ Finset.Ico 0 c.size, max 1 (N j)) * Nb := by
        gcongr
        · exact one_le_pow₀ hK1
  · unfold Nchain
    rw [NT_eq, zero_add]
    have hk1 : 32 * KH θ a b ≤ Kch θ a b :=
      (le_max_right _ _).trans (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
    have hk2 : 32 * (1 + KPD a b) * C510 θ ≤ Kch θ a b :=
      (le_max_right _ _).trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
    calc 2 ^ (c.size + 1) * (4 * (4 * (16 ^ c.size *
          ∏ j ∈ Finset.Ico 0 c.size, (1 + KPD a b) * N j) * Nb) * (KH θ a b * C510 θ ^ c.size))
        ≤ 2 ^ (c.size + 1) * (4 * (4 * (16 ^ c.size * ((1 + KPD a b) ^ c.size *
            ∏ j ∈ Finset.Ico 0 c.size, max 1 (N j))) * Nb) * (KH θ a b * C510 θ ^ c.size)) := by
          gcongr
      _ = (32 * KH θ a b) * (32 * (1 + KPD a b) * C510 θ) ^ c.size *
            (∏ j ∈ Finset.Ico 0 c.size, max 1 (N j)) * Nb := by
          rw [mul_pow, mul_pow, pow_succ, show (32 : ℝ) ^ c.size = 2 ^ c.size * 16 ^ c.size by
            rw [← mul_pow]; norm_num]
          ring
      _ ≤ Kch θ a b * Kch θ a b ^ c.size * (∏ j ∈ Finset.Ico 0 c.size, max 1 (N j)) * Nb := by
          gcongr
      _ = _ := by rw [pow_succ]; ring

end Chain

section Bound

variable (θ a b : ℝ)

/-- **The constant `C₀` of DH21 Proposition 5.1.** -/
@[expose] noncomputable def C0 : ℝ := max (max 1 (N1 θ)) (max (KC1 θ a b) (4 * Kch θ a b ^ 3))

theorem one_le_C0 : 1 ≤ C0 θ a b := (le_max_left _ _).trans (le_max_left _ _)

theorem N1_le_C0 : N1 θ ≤ C0 θ a b := (le_max_right _ _).trans (le_max_left _ _)

theorem KC1_le_C0 : KC1 θ a b ≤ C0 θ a b := (le_max_left _ _).trans (le_max_right _ _)

theorem Kch_le_C0 : 4 * Kch θ a b ^ 3 ≤ C0 θ a b := (le_max_right _ _).trans (le_max_right _ _)

variable {θ a b}

/-- `K^{M+2} 4^M ≤ C₀^{2M}` for `M ≥ 1`. -/
theorem Kch_pow_le {M : ℕ} (hM : 1 ≤ M) :
    Kch θ a b ^ (M + 2) * 4 ^ M ≤ C0 θ a b ^ (2 * M) := by
  have hK := one_le_Kch θ a b
  have hC := one_le_C0 θ a b
  calc Kch θ a b ^ (M + 2) * 4 ^ M ≤ Kch θ a b ^ (3 * M) * 4 ^ M :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by omega)) (by positivity)
    _ = (4 * Kch θ a b ^ 3) ^ M := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ C0 θ a b ^ M := by gcongr; exact Kch_le_C0 θ a b
    _ ≤ C0 θ a b ^ (2 * M) := pow_le_pow_right₀ hC (by omega)

theorem RegChain.code_size_pos {X : RegChain} (hX : X.isNil = false) : 1 ≤ X.code.size := by
  cases X with
  | nil => simp [RegChain.isNil] at hX
  | pair m Qr Qg inner rest => simp [RegChain.code, LegalCode.size]

mutual
/-- **DH21 Proposition 5.1, the constant**: `NB Q ≤ C₀^{2n(Q)+1}` for a well-formed code. -/
theorem RegCpl.NB_le : ∀ Q : RegCpl, Q.wf = true →
    0 ≤ Q.NB θ a b ∧ Q.NB θ a b ≤ C0 θ a b ^ (2 * Q.size + 1)
  | .triv, _ => by
    simp only [RegCpl.NB, RegCpl.size, mul_zero, zero_add, pow_one]
    exact ⟨N1_nonneg θ, N1_le_C0 θ a b⟩
  | .type1 c Q₁ Q₂ Q₃, hw => by
    simp only [RegCpl.wf, Bool.and_eq_true] at hw
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hw
    obtain ⟨n₁, b₁⟩ := RegCpl.NB_le Q₁ h₁
    obtain ⟨n₂, b₂⟩ := RegCpl.NB_le Q₂ h₂
    obtain ⟨n₃, b₃⟩ := RegCpl.NB_le Q₃ h₃
    have hC := one_le_C0 θ a b
    have hK := KC1_nonneg θ a b
    simp only [RegCpl.NB, RegCpl.size]
    refine ⟨by positivity, ?_⟩
    calc KC1 θ a b * (Q₁.NB θ a b * Q₂.NB θ a b * Q₃.NB θ a b)
        ≤ C0 θ a b * (C0 θ a b ^ (2 * Q₁.size + 1) * C0 θ a b ^ (2 * Q₂.size + 1) *
            C0 θ a b ^ (2 * Q₃.size + 1)) := by
          gcongr
          · exact KC1_le_C0 θ a b
      _ = C0 θ a b ^ (2 * (Q₁.size + Q₂.size + Q₃.size) + 4) := by ring
      _ ≤ C0 θ a b ^ (2 * (Q₁.size + Q₂.size + Q₃.size + 2) + 1) :=
          pow_le_pow_right₀ hC (by omega)
  | .type2 Xp Xm Qlp, hw => by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hw
    obtain ⟨⟨⟨⟨hp, hm⟩, hl⟩, -⟩, hnil⟩ := hw
    obtain ⟨nl, bl⟩ := RegCpl.NB_le Qlp hl
    obtain ⟨np, bp⟩ := RegChain.NBAt_le Xp 0 hp
    obtain ⟨nm, bm⟩ := RegChain.NBAt_le Xm 0 hm
    have hC := one_le_C0 θ a b
    have hK := one_le_Kch θ a b
    simp only [zero_add] at bp bm
    set Nm' := Nchain' θ a b Xm.code (Xm.NBAt θ a b 0) (Qlp.NB θ a b) with hNm'
    have hNm'0 : 0 ≤ Nm' := nl.trans (le_max_left _ _)
    have h1 := Nchain'_le (θ := θ) (a := a) (b := b) Xm.code nm nl
    have h2 := Nchain'_le (θ := θ) (a := a) (b := b) Xp.code np hNm'0
    set Pp := ∏ j ∈ Finset.Ico 0 Xp.code.size, max 1 (Xp.NBAt θ a b 0 j)
    set Pm := ∏ j ∈ Finset.Ico 0 Xm.code.size, max 1 (Xm.NBAt θ a b 0 j)
    have hPp : 0 ≤ Pp := Finset.prod_nonneg fun j _ => zero_le_one.trans (le_max_left _ _)
    have hPm : 0 ≤ Pm := Finset.prod_nonneg fun j _ => zero_le_one.trans (le_max_left _ _)
    have hM : 1 ≤ Xp.code.size + Xm.code.size := by
      rcases hnil with h | h
      · have := RegChain.code_size_pos h; omega
      · have := RegChain.code_size_pos h; omega
    simp only [RegCpl.NB, RegCpl.size]
    refine ⟨hNm'0.trans (le_max_left _ _), ?_⟩
    have hpos : 0 < C0 θ a b ^ (2 * (Xp.code.size + Xm.code.size)) := by positivity
    refine le_of_mul_le_mul_left ?_ hpos
    calc C0 θ a b ^ (2 * (Xp.code.size + Xm.code.size)) * Nchain' θ a b Xp.code (Xp.NBAt θ a b 0) Nm'
        ≤ C0 θ a b ^ (2 * (Xp.code.size + Xm.code.size)) *
            (Kch θ a b ^ (Xp.code.size + 1) * Pp *
              (Kch θ a b ^ (Xm.code.size + 1) * Pm * Qlp.NB θ a b)) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
            (by positivity)
      _ = Kch θ a b ^ (Xp.code.size + Xm.code.size + 2) *
            ((Pp * C0 θ a b ^ (2 * Xp.code.size)) * (Pm * C0 θ a b ^ (2 * Xm.code.size))) *
            Qlp.NB θ a b := by ring
      _ ≤ Kch θ a b ^ (Xp.code.size + Xm.code.size + 2) *
            ((4 ^ Xp.code.size * C0 θ a b ^ (2 * Xp.size)) *
              (4 ^ Xm.code.size * C0 θ a b ^ (2 * Xm.size))) *
            C0 θ a b ^ (2 * Qlp.size + 1) := by
          gcongr
      _ = (Kch θ a b ^ (Xp.code.size + Xm.code.size + 2) * 4 ^ (Xp.code.size + Xm.code.size)) *
            C0 θ a b ^ (2 * (Xp.size + Xm.size + Qlp.size) + 1) := by ring
      _ ≤ C0 θ a b ^ (2 * (Xp.code.size + Xm.code.size)) *
            C0 θ a b ^ (2 * (Xp.size + Xm.size + Qlp.size) + 1) := by
          gcongr
          exact Kch_pow_le hM

/-- The pair constants of a chain: `∏_j max(1, N_j) · C₀^{2m} ≤ 4^m C₀^{2n(X)}`. -/
theorem RegChain.NBAt_le : ∀ (X : RegChain) (q : ℕ), X.wf = true →
    (∀ j, 0 ≤ X.NBAt θ a b q j) ∧
      (∏ j ∈ Finset.Ico q (q + X.code.size), max 1 (X.NBAt θ a b q j)) *
        C0 θ a b ^ (2 * X.code.size) ≤ 4 ^ X.code.size * C0 θ a b ^ (2 * X.size)
  | .nil, q, _ => by simp [RegChain.NBAt, RegChain.code, LegalCode.size, RegChain.size]
  | .pair m Qr Qg inner rest, q, hw => by
    simp only [RegChain.wf, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨hr, hg⟩, hi⟩, hre⟩ := hw
    obtain ⟨nr, br⟩ := RegCpl.NB_le Qr hr
    obtain ⟨ng, bg⟩ := RegCpl.NB_le Qg hg
    obtain ⟨ni, bi⟩ := RegChain.NBAt_le inner (q + 1) hi
    obtain ⟨nre, bre⟩ := RegChain.NBAt_le rest (q + inner.code.size + 1) hre
    have hC := one_le_C0 θ a b
    have hsz := code_size_pair m Qr Qg inner rest
    refine ⟨fun j => ?_, ?_⟩
    · simp only [RegChain.NBAt]
      split_ifs
      · positivity
      · exact ni j
      · exact nre j
    have hsplit : Finset.Ico q (q + (RegChain.pair m Qr Qg inner rest).code.size) =
        insert q (Finset.Ico (q + 1) (q + 1 + inner.code.size) ∪
          Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_union, hsz]
      omega
    have hnq : q ∉ Finset.Ico (q + 1) (q + 1 + inner.code.size) ∪
        Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size) := by
      simp only [Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.Ico (q + 1) (q + 1 + inner.code.size))
        (Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size)) := by
      rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
    have ei : ∏ j ∈ Finset.Ico (q + 1) (q + 1 + inner.code.size),
        max 1 ((RegChain.pair m Qr Qg inner rest).NBAt θ a b q j) =
        ∏ j ∈ Finset.Ico (q + 1) (q + 1 + inner.code.size), max 1 (inner.NBAt θ a b (q + 1) j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [NBAt_pair_inner _ _ _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)]
    have er : ∏ j ∈ Finset.Ico (q + inner.code.size + 1)
        (q + inner.code.size + 1 + rest.code.size),
        max 1 ((RegChain.pair m Qr Qg inner rest).NBAt θ a b q j) =
        ∏ j ∈ Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size),
          max 1 (rest.NBAt θ a b (q + inner.code.size + 1) j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [NBAt_pair_rest _ _ _ _ _ _ _ _ _ (by simpa [Finset.mem_Ico] using hj)]
    have hq : max 1 ((RegChain.pair m Qr Qg inner rest).NBAt θ a b q q) ≤
        4 * C0 θ a b ^ (2 * (Qr.size + Qg.size) + 2) := by
      rw [NBAt_pair_self]
      refine max_le ?_ ?_
      · have : 1 ≤ C0 θ a b ^ (2 * (Qr.size + Qg.size) + 2) := one_le_pow₀ hC
        linarith
      · calc 4 * Qr.NB θ a b * Qg.NB θ a b ≤ 4 * C0 θ a b ^ (2 * Qr.size + 1) *
              C0 θ a b ^ (2 * Qg.size + 1) := by gcongr
          _ = 4 * C0 θ a b ^ (2 * (Qr.size + Qg.size) + 2) := by ring
    have hPi : 0 ≤ ∏ j ∈ Finset.Ico (q + 1) (q + 1 + inner.code.size),
        max 1 (inner.NBAt θ a b (q + 1) j) :=
      Finset.prod_nonneg fun j _ => zero_le_one.trans (le_max_left _ _)
    have hPr : 0 ≤ ∏ j ∈ Finset.Ico (q + inner.code.size + 1)
        (q + inner.code.size + 1 + rest.code.size), max 1 (rest.NBAt θ a b (q + inner.code.size + 1) j) :=
      Finset.prod_nonneg fun j _ => zero_le_one.trans (le_max_left _ _)
    rw [hsplit, Finset.prod_insert hnq, Finset.prod_union hd, ei, er, hsz]
    simp only [RegChain.size]
    calc max 1 ((RegChain.pair m Qr Qg inner rest).NBAt θ a b q q) *
          ((∏ j ∈ Finset.Ico (q + 1) (q + 1 + inner.code.size), max 1 (inner.NBAt θ a b (q + 1) j)) *
            ∏ j ∈ Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size),
              max 1 (rest.NBAt θ a b (q + inner.code.size + 1) j)) *
          C0 θ a b ^ (2 * (inner.code.size + rest.code.size + 1))
        = (max 1 ((RegChain.pair m Qr Qg inner rest).NBAt θ a b q q) * C0 θ a b ^ 2) *
          ((∏ j ∈ Finset.Ico (q + 1) (q + 1 + inner.code.size), max 1 (inner.NBAt θ a b (q + 1) j)) *
            C0 θ a b ^ (2 * inner.code.size)) *
          ((∏ j ∈ Finset.Ico (q + inner.code.size + 1) (q + inner.code.size + 1 + rest.code.size),
              max 1 (rest.NBAt θ a b (q + inner.code.size + 1) j)) *
            C0 θ a b ^ (2 * rest.code.size)) := by ring
      _ ≤ (4 * C0 θ a b ^ (2 * (Qr.size + Qg.size) + 2) * C0 θ a b ^ 2) *
          (4 ^ inner.code.size * C0 θ a b ^ (2 * inner.size)) *
          (4 ^ rest.code.size * C0 θ a b ^ (2 * rest.size)) := by
          gcongr
      _ = 4 ^ (inner.code.size + rest.code.size + 1) *
          C0 θ a b ^ (2 * (Qr.size + Qg.size + inner.size + rest.size + 2)) := by ring
end

end Bound

end WaveTurbulence.ClassJR
