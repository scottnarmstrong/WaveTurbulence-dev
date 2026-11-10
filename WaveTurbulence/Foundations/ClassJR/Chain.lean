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

variable (X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)) (σ : ℕ → V) (ε : ℕ → ℤ) (μf : ℕ → P → ℝ)

variable (Aset : ℕ → Set V)

variable (Nb : ℕ → ℝ)

end Ops

section Lemma59

variable {P : Type*} [MeasurableSpace P] {V : Type} {θ A : ℝ}
variable {X : ℕ → Option (P → (V → ℝ) → ℝ → ℝ → ℂ)} {σ : ℕ → V} {ε : ℕ → ℤ} {μf : ℕ → P → ℝ}
variable {Aset : ℕ → Set V} {Nb : ℕ → ℝ}

end Lemma59

end WaveTurbulence.ClassJR
