/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The replaced factor of TARGET Step 4: the algebraic decomposition (replaceterm1)

TARGET L1892-L1907 (`vineest` Step 4).  For the sum over `(Q,T) ∈ Bs` of
`1_{t0<t1} Qbar_app(t0,s1,y) T_app(t1,t0,x) - 1_{t0<s1} Q_app(t1,t0,x) Tbar_app(s1,t0,y)`
we prove the exact pointwise decomposition into the pieces (a) (indicators `s1 ≤ t0 < t1` / `t1 ≤ t0 < s1`),
(b) (momentum differences `x ↔ y`), (c) (time differences `s1 ↔ t1`), the conjugation defects, and the leading
term, which cancels by (layerregest10) (realness of `∑ Q conj T`).  The generality (`Bs₁`, `Bs₂`, `Bs₀`) covers
both `L_{u3} = L_{u4}` (`Bs₁ = Bs₂ = Bs₀`) and `L_{u3} > L_{u4}` (Bs, Bs', Bs'').  The conjugation `Qbar = conj Q`
(layerregest9 for the approximants) is taken with an explicit defect `eQ`, `eT` (zero if the app halves hold; of
remainder size otherwise, see PROGRESS.md).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineEstS4c
open Finset

variable {β κ : Type*} [DecidableEq β]

/-- The `Bs`-sum of (replaceterm1) (Vines II-a / II-b), with index sets `Bs₁` (the set for Vine II-a) and `Bs₂`
(for II-b); `Qb, Tb` are the approximants of the conjugate objects. -/
def replSum (Bs₁ Bs₂ : Finset β) (Q Qb T Tb : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  (if t0 < t1 then ∑ b ∈ Bs₁, Qb b t0 s1 y * T b t1 t0 x else 0) -
    (if t0 < s1 then ∑ b ∈ Bs₂, Q b t1 t0 x * Tb b s1 t0 y else 0)

/-- Clause (a), first piece: `s1 ≤ t0 < t1`. -/
def pieceA1 (Bs₁ : Finset β) (T Qb : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  if s1 ≤ t0 ∧ t0 < t1 then ∑ b ∈ Bs₁, Qb b t0 s1 y * T b t1 t0 x else 0

/-- Clause (a), second piece: `t1 ≤ t0 < s1`. -/
def pieceA2 (Bs₂ : Finset β) (Q Tb : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  if t1 ≤ t0 ∧ t0 < s1 then ∑ b ∈ Bs₂, Q b t1 t0 x * Tb b s1 t0 y else 0

/-- Clause (b), couple: momentum difference of `Q` at the time `s1`. -/
def pieceKQ (Bs₁ : Finset β) (Q T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₁, (starRingEnd ℂ) (Q b s1 t0 y - Q b s1 t0 x) * T b t1 t0 x

/-- Clause (c), couple: time difference of `Q` (`s1 → t1`) at the momentum `x`. -/
def pieceTQ (Bs₁ : Finset β) (Q T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x : κ) : ℂ :=
  ∑ b ∈ Bs₁, (starRingEnd ℂ) (Q b s1 t0 x - Q b t1 t0 x) * T b t1 t0 x

/-- Clause (b), tree: momentum difference of `T` at the time `s1`. -/
def pieceKT (Bs₂ : Finset β) (Q T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₂, Q b t1 t0 x * (starRingEnd ℂ) (T b s1 t0 x - T b s1 t0 y)

/-- Clause (c), tree: time difference of `T` (`s1 → t1`) at the momentum `x`. -/
def pieceTT (Bs₂ : Finset β) (Q T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x : κ) : ℂ :=
  ∑ b ∈ Bs₂, Q b t1 t0 x * (starRingEnd ℂ) (T b t1 t0 x - T b s1 t0 x)

/-- Conjugation defects (clause (d): they have the size of a remainder). -/
def pieceDef (Bs₁ Bs₂ : Finset β) (Q T eQ eT : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₁, eQ b t0 s1 y * T b t1 t0 x - ∑ b ∈ Bs₂, Q b t1 t0 x * eT b s1 t0 y

/-- **Replacement decomposition (TARGET L1899-L1923).**  Pointwise identity.  Hypotheses:
`hQb`, `hTb` (layerregest9 for the approximants, with defects `eQ`, `eT`), `h0 : Bs₀ ⊆ Bs₁ ∩ Bs₂`,
`hvan` (the products at `(t1,t0,x)` vanish outside `Bs₀`: trivial for `Bs₀ = Bs₁ = Bs₂`, and the `Bs''` argument
of L1921-L1923 otherwise), `hreal` (layerregest10: `∑_{Bs₀} Q conj T` is real). -/
theorem replSum_decomp_at (Bs₁ Bs₂ Bs₀ : Finset β) (Q Qb T Tb eQ eT : β → ℝ → ℝ → κ → ℂ)
    (hQb : ∀ b t s k, Qb b t s k = (starRingEnd ℂ) (Q b s t k) + eQ b t s k)
    (hTb : ∀ b t s k, Tb b t s k = (starRingEnd ℂ) (T b t s k) + eT b t s k)
    (h01 : Bs₀ ⊆ Bs₁) (h02 : Bs₀ ⊆ Bs₂) (t0 s1 t1 : ℝ) (x y : κ)
    (hvan : ∀ b ∈ Bs₁ ∪ Bs₂, b ∉ Bs₀ → t0 < t1 → Q b t1 t0 x * (starRingEnd ℂ) (T b t1 t0 x) = 0)
    (hreal : t0 < t1 → (∑ b ∈ Bs₀, Q b t1 t0 x * (starRingEnd ℂ) (T b t1 t0 x)).im = 0) :
    replSum Bs₁ Bs₂ Q Qb T Tb t0 s1 t1 x y =
      pieceA1 Bs₁ T Qb t0 s1 t1 x y - pieceA2 Bs₂ Q Tb t0 s1 t1 x y +
      (if t0 < t1 ∧ t0 < s1 then
        pieceKQ Bs₁ Q T t0 s1 t1 x y + pieceTQ Bs₁ Q T t0 s1 t1 x +
          pieceKT Bs₂ Q T t0 s1 t1 x y + pieceTT Bs₂ Q T t0 s1 t1 x +
          pieceDef Bs₁ Bs₂ Q T eQ eT t0 s1 t1 x y else 0) := by
  unfold replSum pieceA1 pieceA2
  by_cases h1 : t0 < t1 <;> by_cases h2 : t0 < s1
  · -- both indicators
    have hc : ¬ (s1 ≤ t0 ∧ t0 < t1) := fun h => absurd h.1 (not_le.mpr h2)
    have hc2 : ¬ (t1 ≤ t0 ∧ t0 < s1) := fun h => absurd h.1 (not_le.mpr h1)
    rw [if_pos h1, if_pos h2, if_neg hc, if_neg hc2, if_pos ⟨h1, h2⟩]
    set c := starRingEnd ℂ with hcdef
    have e1 : ∑ b ∈ Bs₁, Qb b t0 s1 y * T b t1 t0 x =
        pieceKQ Bs₁ Q T t0 s1 t1 x y + pieceTQ Bs₁ Q T t0 s1 t1 x +
          ∑ b ∈ Bs₁, c (Q b t1 t0 x) * T b t1 t0 x + ∑ b ∈ Bs₁, eQ b t0 s1 y * T b t1 t0 x := by
      unfold pieceKQ pieceTQ
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hQb]; simp only [hcdef, map_sub]; ring
    have e2 : ∑ b ∈ Bs₂, Q b t1 t0 x * Tb b s1 t0 y =
        ∑ b ∈ Bs₂, Q b t1 t0 x * c (T b t1 t0 x) - pieceKT Bs₂ Q T t0 s1 t1 x y -
          pieceTT Bs₂ Q T t0 s1 t1 x + ∑ b ∈ Bs₂, Q b t1 t0 x * eT b s1 t0 y := by
      unfold pieceKT pieceTT
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hTb]; simp only [hcdef, map_sub]; ring
    have l1 : ∑ b ∈ Bs₁, c (Q b t1 t0 x) * T b t1 t0 x = ∑ b ∈ Bs₀, c (Q b t1 t0 x) * T b t1 t0 x := by
      symm
      refine Finset.sum_subset h01 fun b hb hb0 => ?_
      have := hvan b (Finset.mem_union_left _ hb) hb0 h1
      have h' := congrArg c this
      simpa [hcdef, mul_comm] using h'
    have l2 : ∑ b ∈ Bs₂, Q b t1 t0 x * c (T b t1 t0 x) = ∑ b ∈ Bs₀, Q b t1 t0 x * c (T b t1 t0 x) := by
      symm
      refine Finset.sum_subset h02 fun b hb hb0 => ?_
      exact hvan b (Finset.mem_union_right _ hb) hb0 h1
    have l3 : ∑ b ∈ Bs₀, c (Q b t1 t0 x) * T b t1 t0 x = ∑ b ∈ Bs₀, Q b t1 t0 x * c (T b t1 t0 x) := by
      have hz := hreal h1
      have hr : c (∑ b ∈ Bs₀, Q b t1 t0 x * c (T b t1 t0 x)) = ∑ b ∈ Bs₀, Q b t1 t0 x * c (T b t1 t0 x) :=
        Complex.conj_eq_iff_im.mpr hz
      rw [← hr, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hcdef]
    rw [e1, e2, l1, l2, l3]
    unfold pieceDef; ring
  · have hc : (s1 ≤ t0 ∧ t0 < t1) := ⟨not_lt.mp h2, h1⟩
    have hc2 : ¬ (t1 ≤ t0 ∧ t0 < s1) := fun h => absurd h.2 h2
    simp [h1, h2, hc, hc2]
  · have hc : ¬ (s1 ≤ t0 ∧ t0 < t1) := fun h => absurd h.2 h1
    have hc2 : (t1 ≤ t0 ∧ t0 < s1) := ⟨not_lt.mp h1, h2⟩
    simp [h1, h2, hc, hc2]
  · have hc : ¬ (s1 ≤ t0 ∧ t0 < t1) := fun h => absurd h.2 h1
    have hc2 : ¬ (t1 ≤ t0 ∧ t0 < s1) := fun h => absurd h.2 h2
    simp [h1, h2, hc, hc2]

end WaveTurbulence.VineEstS4c
end
