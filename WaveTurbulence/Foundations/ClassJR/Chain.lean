/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Masked2

/-!
# DH21 Lemma 5.9: regular chain operators

A legal partition of `{1, …, 2m}` (DH21 Def 4.4) is coded in **Catalan form** (DH21 Prop 4.5(2)):
`node inner rest` pairs the first point `a` with the point `b` right after the block `inner`, and
`rest` codes the points after `b`. The pairs are listed in preorder, which is the increasing order of
their smaller elements used in DH21 §5.2; `LegalCode.toPartition` (in `ChainPartition.lean`)
identifies the codes with the legal partitions.

For data `X a` (positions `a = 0, …, 2m`; `none` is the identity), signs `ε j`, variables `σ j`
and parameters `μ_j = μf j p` of the pairs `j`, the operator
`X₀ I_{β₁+λ₁} X₁ ⋯ I_{β_{2m}+λ_{2m}} X_{2m}` with `β_a = ε_jα_j`, `β_b = -ε_jα_j`, `λ_a = 0`,
`λ_b = μ_j` is `chainX`, defined by the Catalan recursion
`V(node i r) = X_o (I_{ε_qα_q} V(i) I_{μ_q-ε_qα_q}) V(r)`. `chainX_MJR` is DH21 Lemma 5.9.
-/

public section

open MeasureTheory Filter Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

/-- **A legal partition in Catalan form** (DH21 Prop 4.5(2)). -/
inductive LegalCode : Type
  | nil
  | node (inner rest : LegalCode)
  deriving DecidableEq

namespace LegalCode

/-- The number `m` of pairs. -/
@[expose] def size : LegalCode → ℕ
  | nil => 0
  | node i r => i.size + r.size + 1

end LegalCode

section Ops

variable {P : Type*} {V : Type}

/-- Composition of possibly-identity operators (`none` is the identity). -/
@[expose] noncomputable def ocomp :
    Option (P → (V → ℝ) → ℝ → ℝ → ℂ) → Option (P → (V → ℝ) → ℝ → ℝ → ℂ) →
      Option (P → (V → ℝ) → ℝ → ℝ → ℂ)
  | none, y => y
  | some x, none => some x
  | some x, some y => some fun p α => kcomp (x p α) (y p α)

/-- `I_{εα_v} Y I_{μ-εα_v}` for `Y` possibly the identity. -/
@[expose] noncomputable def swO (ε : ℤ) (v : V) (μf : P → ℝ) :
    Option (P → (V → ℝ) → ℝ → ℝ → ℂ) → P → (V → ℝ) → ℝ → ℝ → ℂ
  | none => fun p α => kcomp (iker (ε * α v)) (iker (μf p - ε * α v))
  | some T => sandw ε v μf T

variable (X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)) (σ : ℕ → V) (ε : ℕ → ℤ) (μf : ℕ → P → ℝ)

/-- **The regular chain operator** `X_o I X_{o+1} I ⋯ X_{o+2m}` of a Catalan code with first
position `o` and first pair `q` (DH21 Lemma 5.9). -/
@[expose] noncomputable def chainX : LegalCode → ℕ → ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)
  | .nil, o, _ => X o
  | .node i r, o, q => ocomp (X o) (ocomp (some (swO (ε q) (σ q) (μf q) (chainX i (o + 1) (q + 1))))
      (chainX r (o + 2 * i.size + 2) (q + i.size + 1)))

/-- DH21's condition `X_a ≠ Id` whenever `{a, a+1} ∈ 𝒫`. -/
@[expose] def AdjOK : LegalCode → ℕ → Prop
  | .nil, _ => True
  | .node i r, o => (i = .nil → X (o + 1) ≠ none) ∧ AdjOK i (o + 1) ∧ AdjOK r (o + 2 * i.size + 2)

variable (Aset : ℕ → Set V)

/-- The variables of the chain: those of the `X a` and the `α_j` of the pairs. -/
@[expose] def chainVars : LegalCode → ℕ → ℕ → Set V
  | .nil, o, _ => Aset o
  | .node i r, o, q => Aset o ∪ (insert (σ q) (chainVars i (o + 1) (q + 1)) ∪
      chainVars r (o + 2 * i.size + 2) (q + i.size + 1))

/-- The disjointness of the variables of the different factors. -/
@[expose] def ChainDisj : LegalCode → ℕ → ℕ → Prop
  | .nil, _, _ => True
  | .node i r, o, q => σ q ∉ chainVars σ Aset i (o + 1) (q + 1) ∧
      Disjoint (insert (σ q) (chainVars σ Aset i (o + 1) (q + 1)))
        (chainVars σ Aset r (o + 2 * i.size + 2) (q + i.size + 1)) ∧
      Disjoint (Aset o) (insert (σ q) (chainVars σ Aset i (o + 1) (q + 1)) ∪
        chainVars σ Aset r (o + 2 * i.size + 2) (q + i.size + 1)) ∧
      ChainDisj i (o + 1) (q + 1) ∧ ChainDisj r (o + 2 * i.size + 2) (q + i.size + 1)

variable (Nb : ℕ → ℝ)

/-- `∏_a ‖X_a‖` with `‖Id‖ = 1`. -/
@[expose] noncomputable def chainNorm : LegalCode → ℕ → ℝ
  | .nil, o => if X o = none then 1 else Nb o
  | .node i r, o => (if X o = none then 1 else Nb o) * chainNorm i (o + 1) *
      chainNorm r (o + 2 * i.size + 2)

end Ops

/-- The constant of DH21 Lemma 5.9: `‖I‖ ≤ Cch θ ^ m ∏ ‖X_a‖`. -/
@[expose] noncomputable def Cch (θ : ℝ) : ℝ := max 1 (Ccp θ) * max 1 (Ccp θ) * max 1 (Csw θ)

theorem one_le_Cch (θ : ℝ) : 1 ≤ Cch θ := by
  unfold Cch
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _)
    (le_max_left _ _)) (le_max_left _ _)

section Lemma59

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A : ℝ}
variable {X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}
variable {Aset : ℕ → Set V} {Nb : ℕ → ℝ}

omit [MeasurableSpace P] in
theorem chainNorm_nonneg (hNb : ∀ a, X a ≠ none → 0 ≤ Nb a) :
    ∀ (c : LegalCode) (o : ℕ), 0 ≤ chainNorm X Nb c o
  | .nil, o => by
    unfold chainNorm; split_ifs with h
    · exact zero_le_one
    · exact hNb o h
  | .node i r, o => by
    unfold chainNorm
    refine mul_nonneg (mul_nonneg ?_ (chainNorm_nonneg hNb i _)) (chainNorm_nonneg hNb r _)
    split_ifs with h
    · exact zero_le_one
    · exact hNb o h

theorem MJR.ocomp_left (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {N N' : ℝ} {S S' : Set V}
    {x : Option (P → (V → ℝ) → ℝ → ℝ → ℂ)} {y : P → (V → ℝ) → ℝ → ℝ → ℂ}
    (hx : x = none ∧ S = ∅ ∨ ∃ T, x = some T ∧ MJR θ A N S T) (hy : MJR θ A N' S' y)
    (hd : Disjoint S S') :
    ∃ T, ocomp x (some y) = some T ∧
      MJR θ A (max 1 (Ccp θ) * (if x = none then 1 else N) * N') (S ∪ S') T := by
  have hN' := hy.nonneg
  rcases hx with ⟨rfl, rfl⟩ | ⟨T, rfl, hT⟩
  · refine ⟨y, rfl, ?_⟩
    rw [Set.empty_union]
    exact hy.mono (by simp only [ite_true, mul_one]; exact le_mul_of_one_le_left hN' (le_max_left _ _))
  · refine ⟨_, rfl, ?_⟩
    have hN := hT.nonneg
    refine MJR.of_MJ ((MJR.comp h0 h1 hA hT hy hd).mono ?_)
    simp only [reduceCtorEq, ite_false]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hN) hN'

theorem Cch_ge (θ : ℝ) : max 1 (Ccp θ) * max 1 (Csw θ) ≤ Cch θ := by
  unfold Cch
  have h1 : (1 : ℝ) ≤ max 1 (Ccp θ) := le_max_left _ _
  have h2 : (0 : ℝ) ≤ max 1 (Csw θ) := zero_le_one.trans (le_max_left _ _)
  rw [mul_assoc]
  exact le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans h1) h2) h1

/-- **DH21 Lemma 5.9** (L1078–L1083), in Catalan form: for a legal code `c ≠ nil`, the regular chain
operator `X₀ I_{β₁+λ₁} X₁ ⋯ I_{β_{2m}+λ_{2m}} X_{2m}` is class `J` plus class `R` in its variables,
with norm `≤ Cch θ ^ m ∏_a ‖X_a‖`, provided the `X_a` are class `J` plus class `R` (or the
identity) in disjoint sets of variables and `X_a ≠ Id` whenever `{a, a+1}` is a pair. The case
`c = nil` is the identity `X₀ = Id` or `X₀` itself. -/
theorem chainX_spec (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ : ∀ j, Measurable (μf j)) (hX : ∀ a T, X a = some T → MJR θ A (Nb a) (Aset a) T)
    (hXn : ∀ a, X a = none → Aset a = ∅) :
    ∀ (c : LegalCode) (o q : ℕ), AdjOK X c o → ChainDisj σ Aset c o q →
      (c = .nil ∧ chainX X σ ε μf c o q = none ∧ chainVars σ Aset c o q = ∅) ∨
      ∃ T, chainX X σ ε μf c o q = some T ∧
        MJR θ A (Cch θ ^ c.size * chainNorm X Nb c o) (chainVars σ Aset c o q) T
  | .nil, o, q, _, _ => by
    simp only [chainX, chainVars, chainNorm, LegalCode.size, pow_zero, one_mul, true_and]
    rcases h : X o with _ | T
    · exact Or.inl ⟨rfl, hXn o h⟩
    · exact Or.inr ⟨T, rfl, by simpa [h] using hX o T h⟩
  | .node i r, o, q, hadj, hdisj => by
    obtain ⟨hadji, hadj1, hadj2⟩ := hadj
    obtain ⟨hvq, hdir, hdo, hd1, hd2⟩ := hdisj
    have hNb : ∀ a, X a ≠ none → 0 ≤ Nb a := fun a ha => by
      obtain ⟨T, hT⟩ := Option.ne_none_iff_exists'.1 ha
      exact (hX a T hT).nonneg
    have hni := chainNorm_nonneg hNb i (o + 1)
    have hnr := chainNorm_nonneg hNb r (o + 2 * i.size + 2)
    have hCch := one_le_Cch θ
    have hCsw := Csw_nonneg h0 h1
    have hCcp : 0 ≤ Ccp θ := by
      have := CJJ_nonneg; have := CJR_nonneg h0 h1; have := CRR_nonneg θ; unfold Ccp; positivity
    -- the inner chain is a genuine operator
    obtain ⟨Ti, hTi, hMi⟩ : ∃ Ti, chainX X σ ε μf i (o + 1) (q + 1) = some Ti ∧
        MJR θ A (Cch θ ^ i.size * chainNorm X Nb i (o + 1)) (chainVars σ Aset i (o + 1) (q + 1))
          Ti := by
      rcases chainX_spec h0 h1 hA hε hμ hX hXn i (o + 1) (q + 1) hadj1 hd1 with
        ⟨rfl, hnone, -⟩ | h
      · exact absurd (by simpa [chainX] using hnone) (hadji rfl)
      · exact h
    have hSW := MJR.sandwich h0 h1 hA (hε q) hMi hvq (hμ q)
    -- the middle factor
    obtain ⟨M, hM, hMM⟩ : ∃ M, ocomp (some (swO (ε q) (σ q) (μf q) (chainX X σ ε μf i (o + 1) (q + 1))))
        (chainX X σ ε μf r (o + 2 * i.size + 2) (q + i.size + 1)) = some M ∧
        MJR θ A (Csw θ * (Cch θ ^ i.size * chainNorm X Nb i (o + 1)) *
          (max 1 (Ccp θ) * (Cch θ ^ r.size * chainNorm X Nb r (o + 2 * i.size + 2))))
          (insert (σ q) (chainVars σ Aset i (o + 1) (q + 1)) ∪
            chainVars σ Aset r (o + 2 * i.size + 2) (q + i.size + 1)) M := by
      rw [hTi]
      rcases chainX_spec h0 h1 hA hε hμ hX hXn r (o + 2 * i.size + 2) (q + i.size + 1) hadj2 hd2 with
        ⟨rfl, hnone, hvars⟩ | ⟨Tr, hTr, hMr⟩
      · refine ⟨_, by rw [hnone]; rfl, ?_⟩
        rw [hvars, Set.union_empty]
        refine hSW.mono ?_
        have hXr : X (o + 2 * i.size + 2) = none := by simpa [chainX] using hnone
        have hn1 : chainNorm X Nb LegalCode.nil (o + 2 * i.size + 2) = 1 := by
          simp [chainNorm, hXr]
        rw [hn1, LegalCode.size, pow_zero, one_mul, mul_one]
        exact le_mul_of_one_le_right (mul_nonneg hCsw (mul_nonneg (pow_nonneg
          (zero_le_one.trans hCch) _) hni)) (le_max_left _ _)
      · refine ⟨_, by rw [hTr]; rfl, ?_⟩
        refine MJR.of_MJ ((MJR.comp h0 h1 hA hSW hMr hdir).mono ?_)
        have hx := mul_nonneg hCsw (mul_nonneg (pow_nonneg (zero_le_one.trans hCch) i.size) hni)
        have hy := mul_nonneg (pow_nonneg (zero_le_one.trans hCch) r.size) hnr
        calc Ccp θ * (Csw θ * (Cch θ ^ i.size * chainNorm X Nb i (o + 1))) *
              (Cch θ ^ r.size * chainNorm X Nb r (o + 2 * i.size + 2))
            ≤ max 1 (Ccp θ) * (Csw θ * (Cch θ ^ i.size * chainNorm X Nb i (o + 1))) *
              (Cch θ ^ r.size * chainNorm X Nb r (o + 2 * i.size + 2)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hx) hy
          _ = _ := by ring
    have hx : X o = none ∧ Aset o = ∅ ∨ ∃ T, X o = some T ∧ MJR θ A (Nb o) (Aset o) T := by
      rcases h : X o with _ | T
      · exact Or.inl ⟨rfl, hXn o h⟩
      · exact Or.inr ⟨T, rfl, hX o T h⟩
    obtain ⟨T, hT, hMT⟩ := MJR.ocomp_left h0 h1 hA hx hMM hdo
    refine Or.inr ⟨T, ?_, ?_⟩
    · simp only [chainX]
      rw [hM]
      exact hT
    · refine hMT.mono ?_
      simp only [chainNorm, LegalCode.size]
      have hb : 0 ≤ (if X o = none then 1 else Nb o) := by
        split_ifs with h
        · exact zero_le_one
        · exact hNb o h
      have hC2 : Csw θ ≤ max 1 (Csw θ) := le_max_right _ _
      have hC3 : (1 : ℝ) ≤ max 1 (Ccp θ) := le_max_left _ _
      have hpi := pow_nonneg (zero_le_one.trans hCch) i.size
      have hpr := pow_nonneg (zero_le_one.trans hCch) r.size
      have key : max 1 (Ccp θ) * (Csw θ * max 1 (Ccp θ)) ≤ Cch θ := by
        calc max 1 (Ccp θ) * (Csw θ * max 1 (Ccp θ)) ≤
              max 1 (Ccp θ) * (max 1 (Csw θ) * max 1 (Ccp θ)) := by gcongr
          _ = Cch θ := by unfold Cch; ring
      calc max 1 (Ccp θ) * (if X o = none then 1 else Nb o) *
            (Csw θ * (Cch θ ^ i.size * chainNorm X Nb i (o + 1)) *
              (max 1 (Ccp θ) * (Cch θ ^ r.size * chainNorm X Nb r (o + 2 * i.size + 2))))
          = (max 1 (Ccp θ) * (Csw θ * max 1 (Ccp θ))) * (Cch θ ^ i.size * Cch θ ^ r.size) *
              ((if X o = none then 1 else Nb o) * chainNorm X Nb i (o + 1) *
                chainNorm X Nb r (o + 2 * i.size + 2)) := by ring
        _ ≤ Cch θ * (Cch θ ^ i.size * Cch θ ^ r.size) *
              ((if X o = none then 1 else Nb o) * chainNorm X Nb i (o + 1) *
                chainNorm X Nb r (o + 2 * i.size + 2)) := by gcongr
        _ = _ := by rw [pow_succ, pow_add]; ring

end Lemma59

end WaveTurbulence.ClassJR
