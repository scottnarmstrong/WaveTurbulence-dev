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

variable {ε : ℝ}

/-- The kind-2 cancellation of clause (c): `|a|^{1-3η} · (|a|^{-(1-3η)} Δ) = Δ` for `a ≠ 0`. -/
theorem kind2_cancel (η a : ℝ) (ha : a ≠ 0) (Δ : ℂ) :
    (((|a| ^ (1 - 3 * η) : ℝ) : ℂ)) * ((((|a| ^ (-(1 - 3 * η)) : ℝ) : ℂ)) * Δ) = Δ := by
  have hpos : 0 < |a| := abs_pos.mpr ha
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
  simp

end WaveTurbulence.VineEstS5C.P2
