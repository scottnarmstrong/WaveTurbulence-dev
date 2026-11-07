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

/-- The couple conjugation defect, as remainders. -/
@[expose] def defQ (RQ RQb : β → ℝ → ℝ → κ → ℂ) (b : β) (t s : ℝ) (k : κ) : ℂ :=
  conj (RQ b s t k) - RQb b t s k

/-- The tree conjugation defect, as remainders. -/
@[expose] def defT (RT RTb : β → ℝ → ℝ → κ → ℂ) (b : β) (t s : ℝ) (k : κ) : ℂ :=
  conj (RT b t s k) - RTb b t s k

/-- (layerregest9) for the couple approximants, up to `defQ`: from the exact kernel halves. -/
theorem hQb_of_halves {KQ KQb Q Qb RQ RQb : β → ℝ → ℝ → κ → ℂ}
    (hK : ∀ b t s k, KQ b t s k = Q b t s k + RQ b t s k)
    (hKb : ∀ b t s k, KQb b t s k = Qb b t s k + RQb b t s k)
    (hhalf : ∀ b t s k, KQb b t s k = conj (KQ b s t k)) (b : β) (t s : ℝ) (k : κ) :
    Qb b t s k = conj (Q b s t k) + defQ RQ RQb b t s k := by
  have h1 := hhalf b t s k
  rw [hKb, hK, map_add] at h1
  unfold defQ
  linear_combination h1

/-- (layerregest9) for the tree approximants, up to `defT`. -/
theorem hTb_of_halves {KT KTb T Tb RT RTb : β → ℝ → ℝ → κ → ℂ}
    (hK : ∀ b t s k, KT b t s k = T b t s k + RT b t s k)
    (hKb : ∀ b t s k, KTb b t s k = Tb b t s k + RTb b t s k)
    (hhalf : ∀ b t s k, KTb b t s k = conj (KT b t s k)) (b : β) (t s : ℝ) (k : κ) :
    Tb b t s k = conj (T b t s k) + defT RT RTb b t s k := by
  have h1 := hhalf b t s k
  rw [hKb, hK, map_add] at h1
  unfold defT
  linear_combination h1

/-- The four defect rows. -/
@[expose] def defRowQ1 (Bs₁ : Finset β) (RQ T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₁, conj (RQ b s1 t0 y) * T b t1 t0 x

@[expose] def defRowQ2 (Bs₁ : Finset β) (RQb T : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₁, RQb b t0 s1 y * T b t1 t0 x

@[expose] def defRowT1 (Bs₂ : Finset β) (Q RT : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₂, Q b t1 t0 x * conj (RT b s1 t0 y)

@[expose] def defRowT2 (Bs₂ : Finset β) (Q RTb : β → ℝ → ℝ → κ → ℂ) (t0 s1 t1 : ℝ) (x y : κ) : ℂ :=
  ∑ b ∈ Bs₂, Q b t1 t0 x * RTb b s1 t0 y

/-- **Clause (d)**: `pieceDef` is `(row Q1 - row Q2) - (row T1 - row T2)`, each row containing one
remainder factor. -/
theorem pieceDef_eq_rows (Bs₁ Bs₂ : Finset β) (Q T RQ RQb RT RTb : β → ℝ → ℝ → κ → ℂ)
    (t0 s1 t1 : ℝ) (x y : κ) :
    pieceDef Bs₁ Bs₂ Q T (defQ RQ RQb) (defT RT RTb) t0 s1 t1 x y =
      (defRowQ1 Bs₁ RQ T t0 s1 t1 x y - defRowQ2 Bs₁ RQb T t0 s1 t1 x y) -
        (defRowT1 Bs₂ Q RT t0 s1 t1 x y - defRowT2 Bs₂ Q RTb t0 s1 t1 x y) := by
  unfold pieceDef defRowQ1 defRowQ2 defRowT1 defRowT2 defQ defT
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]

end WaveTurbulence.VineEstS4c

namespace WaveTurbulence.VineEstS4c

open WaveTurbulence ConjCoh

variable {d : ℕ}

/-- The remainder factor of a couple row: `(t,s) ↦ conj ℛ(s,t)` has the `𝔛`-restriction norm of `ℛ`
over the swapped box. -/
theorem XNormRestr_conjSwap (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) (K : Set (Mom d))
    (R : (Fin 2 → ℝ) → Mom d → ℂ) :
    XNormRestr θ Λ₁ Λ₂ B K (fun ts k => conj (R ![ts 1, ts 0] k)) =
      XNormRestr θ Λ₁ Λ₂ {ts | ![ts 1, ts 0] ∈ B} K R := by
  have hπ : ∀ i, (Equiv.swap (0 : Fin 2) 1) ((Equiv.swap (0 : Fin 2) 1) i) = i := by
    intro i; simp
  have hp : ∀ ts : Fin 2 → ℝ, permT (Equiv.swap (0 : Fin 2) 1) ts = ![ts 1, ts 0] := by
    intro ts; funext i; fin_cases i <;> simp [permT]
  have := XNormRestr_swapConj hπ θ Λ₁ Λ₂ B K R
  have e : swapConj (Equiv.swap (0 : Fin 2) 1) R = fun ts k => conj (R ![ts 1, ts 0] k) := by
    funext ts k; simp only [swapConj, hp]
  have e2 : permT (Equiv.swap (0 : Fin 2) 1) ⁻¹' B = {ts | ![ts 1, ts 0] ∈ B} := by
    ext ts; simp only [Set.mem_preimage, hp, Set.mem_setOf_eq]
  rw [e, e2] at this
  exact this

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
