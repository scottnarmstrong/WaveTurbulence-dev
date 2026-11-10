/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.ReplaceAlgebra
public import WaveTurbulence.Foundations.VineEst.NormSwapConj
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (d): the conjugation defects are remainders

TARGET `vineest` Step 4, (layerregest9) is exact for the kernels `𝒦*` (proved, `CoherentRealityGate`
kernel halves) and open for the approximants (RULINGS R1, `PL4.appConj`). Writing `𝒦 = app + ℛ`
(Prop 6.1, `layerregest2`–`3`) the defects of `replSum_decomp` are

* `eQ b t s k = conj (ℛ_Q b s t k) - ℛ_{Q̄} b t s k`, `eT b t s k = conj (ℛ_T b t s k) - ℛ_{T̄} b t s k`,

so `pieceDef` is a signed sum of four rows, each containing exactly one remainder factor (of size
`regBound n 1 = (C₁δ)ⁿ L^{-(γ₁-√η)}` in `𝔛^{η,30d,30d}` / `𝔛^{η,30d,0}`) times an approximant: these are
the rows with `g ≥ 1` of `sumint` (d). The `𝔛`-norm of the remainder factors in the rows is that of `ℛ`
itself, by `XNormRestr_swapConj` (the swap `(t,s) ↦ (s,t)` with conjugation, for couples; conjugation only,
for trees).
-/

@[expose] public section
set_option autoImplicit false

open Finset
open scoped ComplexConjugate ENNReal

namespace WaveTurbulence.VineEstS4c

variable {β κ : Type*}

end WaveTurbulence.VineEstS4c

namespace WaveTurbulence.VineEstS4c

open WaveTurbulence ConjCoh

variable {d : ℕ}

/-- The remainder factor of a tree row: conjugation only. -/
theorem XNormRestr_conj (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) (K : Set (Mom d))
    (R : (Fin 2 → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B K (fun ts k => conj (R ts k)) = XNormRestr θ Λ₁ Λ₂ B K R := by
  have hπ : ∀ i, (1 : Equiv.Perm (Fin 2)) ((1 : Equiv.Perm (Fin 2)) i) = i := fun i => rfl
  have := XNormRestr_swapConj hπ θ Λ₁ Λ₂ B K R
  have e : swapConj (1 : Equiv.Perm (Fin 2)) R = fun ts k => conj (R ts k) := by
    funext ts k; rfl
  have e2 : permT (1 : Equiv.Perm (Fin 2)) ⁻¹' B = B := by
    ext ts; rfl
  rw [e, e2] at this
  exact this

end WaveTurbulence.VineEstS4c
