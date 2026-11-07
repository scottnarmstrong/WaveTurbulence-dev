/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.ReplaceAlgebra
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BundleAlg

/-! # The remainder expansion of the exact bundle (V5 Step 4d part C, WP-B step 2)

Abstract algebra, no states.  The exact II-a rows at an index `b` are `Q̄ b + conj ℛ_Q(s,t)` and `T b + ℛ_T`; the exact II-b rows are
`Q b + ℛ_Q` and `T̄ b + conj ℛ_T`, where `Q̄ b t s k = conj (Q b s t k)`, `T̄ b = conj (T b)` are DEFINED as conjugate-swaps
(so the conjugation defects `eQ = eT = 0` and no approximant-conjugation theorem is needed).  `exact_eq_repl_add_rem`: the
exact signed bundle is `replSum` of the approximants plus the remainder rows `remRowA`, `remRowB`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.VineEstS5C
open Finset WaveTurbulence.VineEstS4c

variable {β : Type*} {d : ℕ}

/-- The conjugate-swap `Q̄ b t s k = conj (Q b s t k)`. -/
def cswap (Q : β → ℝ → ℝ → Mom d → ℂ) : β → ℝ → ℝ → Mom d → ℂ := fun b t s k => (starRingEnd ℂ) (Q b s t k)

/-- The conjugate `T̄ b t s k = conj (T b t s k)`. -/
def cconj (T : β → ℝ → ℝ → Mom d → ℂ) : β → ℝ → ℝ → Mom d → ℂ := fun b t s k => (starRingEnd ℂ) (T b t s k)

/-- The remainder part of the II-a term at index `b`: exact `(Q̄ + conj ℛ_Q)(T + ℛ_T)` minus `Q̄ T`. -/
def remA (Q T RQ RT : β → ℝ → ℝ → Mom d → ℂ) (b : β) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  open Classical in (if t0 < t1 then 1 else 0) *
    (cswap Q b t0 s1 y * RT b t1 t0 x + (starRingEnd ℂ) (RQ b s1 t0 y) * (T b t1 t0 x + RT b t1 t0 x))

/-- The remainder part of the II-b term at index `b`. -/
def remB (Q T RQ RT : β → ℝ → ℝ → Mom d → ℂ) (b : β) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  open Classical in (if t0 < s1 then 1 else 0) *
    (Q b t1 t0 x * (starRingEnd ℂ) (RT b s1 t0 y) + RQ b t1 t0 x * (cconj T b s1 t0 y + (starRingEnd ℂ) (RT b s1 t0 y)))

theorem exact_eq_repl_add_rem [DecidableEq β] (Bs₁ Bs₂ : Finset β) (Q T RQ RT : β → ℝ → ℝ → Mom d → ℂ)
    (t0 s1 t1 : ℝ) (x y : Mom d) :
    (∑ b ∈ Bs₁, termA (fun t s k => cswap Q b t s k + (starRingEnd ℂ) (RQ b s t k))
        (fun t s k => T b t s k + RT b t s k) t0 s1 t1 x y) -
      ∑ b ∈ Bs₂, termB (fun t s k => Q b t s k + RQ b t s k)
        (fun t s k => cconj T b t s k + (starRingEnd ℂ) (RT b t s k)) t0 s1 t1 x y =
    replSum Bs₁ Bs₂ Q (cswap Q) T (cconj T) t0 s1 t1 x y +
      (∑ b ∈ Bs₁, remA Q T RQ RT b t0 s1 t1 x y - ∑ b ∈ Bs₂, remB Q T RQ RT b t0 s1 t1 x y) := by
  classical
  unfold replSum termA termB remA remB
  by_cases h1 : t0 < t1 <;> by_cases h2 : t0 < s1 <;> simp [h1, h2, Finset.sum_add_distrib, mul_add, add_mul] <;>
    ring_nf

end WaveTurbulence.VineEstS5C
end
