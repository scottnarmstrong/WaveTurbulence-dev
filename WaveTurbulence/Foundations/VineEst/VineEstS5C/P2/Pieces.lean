/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Space

/-! # P2: the pointwise identities of the pieces (V5 Step 4d part C, packet P2, step 2)

One separated term of a couple is `cq · Jq(t,s) · Mq(k)` and of a tree `ct · Jt(t,s) · Mt(k)` (`sepTerm`; `Mq, Mt` real,
`cq, ct` real constants, `Jq, Jt` time factors).  For every one of the piece types (a)-(c) of `zpPieces` (TARGET L1925-L1951)
the summand equals `‖a‖^e · W_K · W_L` where `W_K` is the weight of the vine's 𝒦 row (at `k₁ = k`, the clocks of the
row) and `W_L` the ℒ row (at `ℓ₁ = k + a`, `a = ε r`, `ε = ±1`), with the spatial weights of `Space` (cut off to `‖r‖ ≤ 1`).
`e = 1` for the clause (b) pieces (KQ, KT), `e = 0` otherwise.  Clause (c) (TQ, TT): the kind-2 phase factor
`|c₀ - c₁|^{1-3η}` times the singular joint row is the summand (`kind2_cancel`, `c₀ ≠ c₁`, i.e. a.e.). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS4c
open scoped ComplexConjugate

variable {d : ℕ}

/-- One separated term `c · J(t,s) · M(k)` (`M` real). -/
def sepTerm (c : ℝ) (J : (Fin 2 → ℝ) → ℂ) (M : Mom d → ℝ) (t s : ℝ) (k : Mom d) : ℂ :=
  (c : ℂ) * J ![t, s] * (M k : ℂ)

/-- The conjugate time factor. -/
def cJ (J : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ := fun ts => conj (J ts)

theorem conj_sepTerm (c : ℝ) (J : (Fin 2 → ℝ) → ℂ) (M : Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    conj (sepTerm c J M t s k) = (c : ℂ) * cJ J ![t, s] * (M k : ℂ) := by
  simp [sepTerm, cJ]

variable (cq ct : ℝ) (Jq Jt : (Fin 2 → ℝ) → ℂ) (Mq Mt : Mom d → ℝ) (t0 s1 t1 : ℝ) (r : Mom d)

/-- Piece A1: `conj Q(s₁,t₀,y) T(t₁,t₀,x)`; 𝒦 at `y`, ℒ at `x`. -/
theorem pieceA1_term (x y : Mom d) :
    conj (sepTerm cq Jq Mq s1 t0 y) * sepTerm ct Jt Mt t1 t0 x =
      (cJ Jq ![s1, t0] * spPlain cq Mq r y) * (Jt ![t1, t0] * spPlain ct Mt r x) := by
  rw [conj_sepTerm]; simp only [sepTerm, spPlain]; ring

/-- Piece A2: `Q(t₁,t₀,x) conj T(s₁,t₀,y)`; 𝒦 at `x`, ℒ at `y`. -/
theorem pieceA2_term (x y : Mom d) :
    sepTerm cq Jq Mq t1 t0 x * conj (sepTerm ct Jt Mt s1 t0 y) =
      (Jq ![t1, t0] * spPlain cq Mq r x) * (cJ Jt ![s1, t0] * spPlain ct Mt r y) := by
  rw [conj_sepTerm]; simp only [sepTerm, spPlain]; ring

variable {ε : ℝ}

/-- Piece KQ (clause (b), couple, Vine II-a: `y = k`, `x = k + εr`):
`conj(Q(s₁,t₀,y) - Q(s₁,t₀,x)) T(t₁,t₀,x) = ‖r‖ · W_K · W_L`. -/
theorem pieceKQ_term (hε : |ε| = 1) (hr : ‖r‖ ≤ 1) (k : Mom d) :
    conj (sepTerm cq Jq Mq s1 t0 k - sepTerm cq Jq Mq s1 t0 (k + ε • r)) *
        sepTerm ct Jt Mt t1 t0 (k + ε • r) =
      ((‖r‖ : ℝ) : ℂ) * ((cJ Jq ![s1, t0] * spDiff (-cq) Mq ε r k) *
        (Jt ![t1, t0] * spPlain ct Mt r (k + ε • r))) := by
  have hn : ‖ε • r‖ = ‖r‖ := by rw [norm_smul, Real.norm_eq_abs, hε, one_mul]
  have h := rowB_couple_IIa (MQ := cm Mq) (MT := cm Mt) (fun k => by simp [cm]) (ε • r) k
  have e : conj (sepTerm cq Jq Mq s1 t0 k - sepTerm cq Jq Mq s1 t0 (k + ε • r)) =
      (cq : ℂ) * cJ Jq ![s1, t0] * conj (cm Mq k - cm Mq (k + ε • r)) := by
    simp [sepTerm, cJ, cm, ← mul_sub]
  have hs : spDiff (-cq) Mq ε r k = ((-cq : ℝ) : ℂ) * diffQuot (ε • r) (cm Mq) k := by
    simp [spDiff, cutW_of_le hr]
  rw [e, hs, mul_assoc, mul_assoc]
  have h2 : conj (cm Mq k - cm Mq (k + ε • r)) * (cm Mt (k + ε • r)) =
      -(((‖ε • r‖ : ℝ) : ℂ) * (diffQuot (ε • r) (cm Mq) k * cm Mt (k + ε • r))) := h
  rw [hn] at h2
  simp only [sepTerm, spPlain, cm] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination ((cq : ℂ) * cJ Jq ![s1, t0] * (ct : ℂ) * Jt ![t1, t0]) * h2

/-- Piece KT (clause (b), tree, Vine II-b: `x = k`, `y = k + εr`):
`Q(t₁,t₀,x) conj(T(s₁,t₀,x) - T(s₁,t₀,y)) = ‖r‖ · W_K · W_L`. -/
theorem pieceKT_term (hε : |ε| = 1) (hr : ‖r‖ ≤ 1) (k : Mom d) :
    sepTerm cq Jq Mq t1 t0 k *
        conj (sepTerm ct Jt Mt s1 t0 k - sepTerm ct Jt Mt s1 t0 (k + ε • r)) =
      ((‖r‖ : ℝ) : ℂ) * ((Jq ![t1, t0] * spProdDiff (-(cq * ct)) Mq Mt ε r k) *
        (cJ Jt ![s1, t0] * spOne r (k + ε • r))) := by
  have hn : ‖ε • r‖ = ‖r‖ := by rw [norm_smul, Real.norm_eq_abs, hε, one_mul]
  have h := rowB_tree_IIb (MQ := cm Mq) (MT := cm Mt) (fun k => by simp [cm]) (ε • r) k
  have h2 : cm Mq k * conj (cm Mt k - cm Mt (k + ε • r)) =
      -(((‖r‖ : ℝ) : ℂ) * (diffQuot (ε • r) (cm Mt) k * cm Mq k)) := by rw [← hn]; exact h
  have hs : spProdDiff (-(cq * ct)) Mq Mt ε r k =
      ((-(cq * ct) : ℝ) : ℂ) * (diffQuot (ε • r) (cm Mt) k * (Mq k : ℂ)) := by
    simp [spProdDiff, cutW_of_le hr]
  have e : conj (sepTerm ct Jt Mt s1 t0 k - sepTerm ct Jt Mt s1 t0 (k + ε • r)) =
      (ct : ℂ) * cJ Jt ![s1, t0] * conj (cm Mt k - cm Mt (k + ε • r)) := by
    simp [sepTerm, cJ, cm, ← mul_sub]
  rw [e, hs]
  simp only [sepTerm, spOne]
  have hcm : ∀ (M : Mom d → ℝ) k, cm M k = (M k : ℂ) := fun _ _ => rfl
  simp only [hcm] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination ((cq : ℂ) * (ct : ℂ) * Jq ![t1, t0] * cJ Jt ![s1, t0]) * h2

/-- The kind-2 cancellation of clause (c): `|a|^{1-3η} · (|a|^{-(1-3η)} Δ) = Δ` for `a ≠ 0`. -/
theorem kind2_cancel (η a : ℝ) (ha : a ≠ 0) (Δ : ℂ) :
    (((|a| ^ (1 - 3 * η) : ℝ) : ℂ)) * ((((|a| ^ (-(1 - 3 * η)) : ℝ) : ℂ)) * Δ) = Δ := by
  have hpos : 0 < |a| := abs_pos.mpr ha
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
  simp

/-- Piece TQ (clause (c), couple, Vine II-a, `x = k + εr`): the joint row at the clocks `(s₁, t₁, t₀)`. -/
theorem pieceTQ_term (hε : |ε| = 1) (hr : ‖r‖ ≤ 1) (η : ℝ) (hne : s1 ≠ t1) (k : Mom d) :
    conj (sepTerm cq Jq Mq s1 t0 (k + ε • r) - sepTerm cq Jq Mq t1 t0 (k + ε • r)) *
        sepTerm ct Jt Mt t1 t0 (k + ε • r) =
      (((|s1 - t1| ^ (1 - 3 * η) : ℝ) : ℂ)) *
        ((((((|s1 - t1| ^ (-(1 - 3 * η)) : ℝ) : ℂ)) *
            (cJ Jq ![s1, t0] - cJ Jq ![t1, t0])) * spShift cq Mq ε r k) *
          (Jt ![t1, t0] * spPlain ct Mt r (k + ε • r))) := by
  have hs : spShift cq Mq ε r k = (cq : ℂ) * (Mq (k + ε • r) : ℂ) := by simp [spShift, cutW_of_le hr]
  have hk := kind2_cancel η (s1 - t1) (sub_ne_zero.mpr hne) ((cJ Jq ![s1, t0] - cJ Jq ![t1, t0]))
  have e : conj (sepTerm cq Jq Mq s1 t0 (k + ε • r) - sepTerm cq Jq Mq t1 t0 (k + ε • r)) =
      (cJ Jq ![s1, t0] - cJ Jq ![t1, t0]) * ((cq : ℂ) * (Mq (k + ε • r) : ℂ)) := by
    simp [sepTerm, cJ, ← mul_sub]; ring
  rw [e, hs]
  simp only [spPlain, sepTerm]
  push_cast
  linear_combination (-((cq : ℂ) * (Mq (k + ε • r) : ℂ) * (Jt ![t1, t0] * ((ct : ℂ) * (Mt (k + ε • r) : ℂ))))) * hk

/-- Piece TT (clause (c), tree, Vine II-b, `x = k`): the joint row at the clocks `(t₁, s₁, t₀)`. -/
theorem pieceTT_term (η : ℝ) (hne : t1 ≠ s1) (k : Mom d) :
    sepTerm cq Jq Mq t1 t0 k * conj (sepTerm ct Jt Mt t1 t0 k - sepTerm ct Jt Mt s1 t0 k) =
      (((|t1 - s1| ^ (1 - 3 * η) : ℝ) : ℂ)) *
        ((((((|t1 - s1| ^ (-(1 - 3 * η)) : ℝ) : ℂ)) *
            (cJ Jt ![t1, t0] - cJ Jt ![s1, t0])) * spProd (cq * ct) Mq Mt r k) *
          (Jq ![t1, t0] * spOne r k)) := by
  have hk := kind2_cancel η (t1 - s1) (sub_ne_zero.mpr hne) ((cJ Jt ![t1, t0] - cJ Jt ![s1, t0]))
  have e : conj (sepTerm ct Jt Mt t1 t0 k - sepTerm ct Jt Mt s1 t0 k) =
      (cJ Jt ![t1, t0] - cJ Jt ![s1, t0]) * ((ct : ℂ) * (Mt k : ℂ)) := by
    simp [sepTerm, cJ, ← mul_sub]; ring
  rw [e]
  simp only [spProd, spOne, sepTerm]
  push_cast
  linear_combination (-((cq : ℂ) * (Mq k : ℂ) * (Jq ![t1, t0]) * ((ct : ℂ) * (Mt k : ℂ)))) * hk

end WaveTurbulence.VineEstS5C.P2
