/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.IsUnitCoeff
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

/-!
# SumintDatum

Wave B tier B1 (WaveB1-Sumint.lean), source: T L1595–L1625. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- **The datum of `sumint`** (T L1595–L1625). The affine maps `k = T₁x + h₁`, `ℓ = T₂x + h₂` have
integer matrices and shifts that are integer combinations of `(e,f,g,h)` (WAVE-B v2: "affine maps
`h₁, h₂` of `(e,f,g,h)`"). -/
structure SumintDatum (d : ℕ) where
  S : SumintShape
  /-- `T₁`, its inverse, and `T₂`, with entries in `{0, ±1}` -/
  T₁ : Matrix S.VIdx S.VIdx ℤ
  T₁inv : Matrix S.VIdx S.VIdx ℤ
  T₂ : Matrix S.VIdx S.VIdx ℤ
  T₁_mul : T₁ * T₁inv = 1
  T₁inv_mul : T₁inv * T₁ = 1
  T_unit : ∀ v v', IsUnitCoeff (T₁ v v') ∧ IsUnitCoeff (T₁inv v v') ∧ IsUnitCoeff (T₂ v v')
  /-- the shifts `h₁, h₂` as coefficients of `(e, f, g, h)` -/
  H₁ : S.VIdx → Fin 4 → ℤ
  H₂ : S.VIdx → Fin 4 → ℤ
  /-- all of `k, ℓ, e, f, g, h` lie in `w̲ + ℤ_L^d` -/
  H_coset : ∀ v, ∑ c, H₁ v c = 1 ∧ ∑ c, H₂ v c = 1
  /-- hypothesis (ii): the predecessors and the numbers `Λ_jⁱ`. Reading (stage-3 O3):
  `prev v = none` means that `ℓ_v` itself is a signed sum (otherwise (ii) would be impossible for the
  lex-first index). -/
  Λ : S.VIdx → ℕ
  prev : S.VIdx → Option S.VIdx
  /-- the signed sums of (ii): coefficients of `k` and of `(e,f,g,h)` -/
  σk : S.VIdx → S.VIdx → ℤ
  σe : S.VIdx → Fin 4 → ℤ
  /-- weights `𝒦_jⁱ, ℒ_jⁱ` and the integers `g_{ij}, g'_{ij}` -/
  wK : S.VIdx → Mom d → ℂ
  wL : S.VIdx → Mom d → ℂ
  g : S.VIdx → ℕ
  g' : S.VIdx → ℕ
  /-- `ζ_jⁱ = a x_j + b y_j + c r` (`j ≥ 1`) -/
  ζc : (i : Fin S.I) → Fin (S.m i) → Fin 3 → ℤ
  /-- `Λ_i` choice (`true`: `⟨u₁,u₃⟩`, `false`: `⟨u₃, u₁+u₂-u₃⟩`) and `ξ_i = a u₁ + b u₂ + c u₃ + d r` -/
  Λsel : Fin S.I → Bool
  ξc : Fin S.I → Fin 4 → ℤ
  /-- parameters `λ_jⁱ` (on `t`), `μ_jⁱ` (on `s`), `σ_jⁱ` (on `τ`) -/
  param : S.TVar → ℝ
  /-- unit intervals `[q_v, q_v+1]` of the input times and the order constraints `v < w` -/
  q : S.TVar → ℕ
  constraints : Finset (S.TVar × S.TVar)
  /-- for `i ∈ Bad`, which of (a)–(d) holds (`0`–`3`) -/
  badKind : Fin S.I → Fin 4
  /-- output unit intervals for `(t, t', t'')`, unit-ball centres for `(e,f,g,h)`, and `w̲` -/
  qOut : Fin 3 → ℕ
  centre : Fin 4 → Mom d
  wBar : Mom d

end WaveTurbulence
