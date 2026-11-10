/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Kernel
public import WaveTurbulence.Foundations.ClassJR.Symbol

/-!
# Class `J` and class `R` operators (DH21 Definition 5.2)

DH21 Definition 5.2 (L955–L964). An operator `𝒥 = 𝒥_{α[A], μ[E]}` has class `J` with norm `1` if
`𝒥 = ∫ m(α[A], μ[E], γ₁, γ₂) J_{ℓ; γ₁, γ₂} dγ₁ dγ₂` with `ℓ` a bundle of `α[A]` and
`∫ (1 + Σ_{j ∈ A} |α_j| + |γ₁|)^{1/4} |∂_α^ρ m| dα[A] dγ₁ dγ₂ ≤ (2|ρ|)!` for every `μ[E]` and every
multi-index `ρ`; class `R` is the analogue with
`R_{ℓ₁ + ε α₁, ℓ₂ + ε α₁; γ₁, γ₂, γ₃}`, a symbol independent of the special variable `α₁`, and
weight `(1 + Σ_{j ∈ A \ {1}} |α_j| + |γ₁| + |γ₃|)^{1/4}`. A general class `J` (or `R`) operator is a
finite linear combination, and its norm is the infimum of the sums of the absolute coefficients.

## Formalization

* Operators on functions on `[0, 1]` are represented by Volterra kernels compared on the triangle
  `0 ≤ s ≤ t ≤ 1` (`KEqOn`, `Kernel.lean`). The variables `α[A]` are `α : ι → ℝ` for a finite type
  `ι`; for class `R` they are `α : Option ι → ℝ`, the special variable being `α none`. The
  parameters `μ[E]` are not modelled: a statement "for all `μ`" is a universally quantified family
  of statements with a common constant.
* A general operator of class `J` with norm at most `N` (`ClassJ θ A N`) is a finite sum of basic
  operators (`JSym.kernel`) whose bounds `N_i` satisfy `Σ N_i ≤ N`. Writing `c · J_ℓ` with
  `‖J_ℓ‖ = 1` as the basic operator with symbol `c m_ℓ` and bound `|c|`, this is DH21's
  definition with "`‖𝒥‖ ≤ N`" meaning that some representation has `Σ |c_ℓ| ≤ N`.

## Deviations from DH21 (reported in the JR-OPS handoff)

1. **Gevrey radius.** The bound is `N · A^k · (2k)!` for derivatives of order `k` (`gev N A k`),
   not `(2|ρ|)!`. The composition lemmas multiply by symbols built from the cutoff `χ₀`, whose
   derivatives cannot be bounded by `(2k)!` (the issue of FINDINGS F41), so DH21's literal
   normalization is not closed under composition. The radius `A ≥ A₀` is fixed and preserved.
2. **Weight exponent.** `θ` replaces DH21's `1/4`: DH21 uses `θ = 1/4`, DH23 (L955–L969) needs
   `θ = 1 - η/8`. The composition lemmas are proved for `0 ≤ θ < 1` with constants depending on
   `θ`, which serves both routes.
3. **Derivative norm.** `‖∂_α^k m‖` is the operator norm of the `k`-th derivative on `ℓ¹(ι)`
   (`dnorm`); it dominates `|∂_α^ρ m|` for every `|ρ| = k`, so the bound implies DH21's per-`ρ`
   bound. The `L¹` norm of the maximum over `ρ` is controlled, which is stronger.
4. **Qualitative regularity.** Symbols satisfy `SymReg` (smooth in `α`, jointly measurable, every
   derivative dominated uniformly in `α` by an integrable function of `γ`). DH21 leaves this
   implicit; it is what makes the composed symbols differentiable under the integral sign.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

variable {ι : Type*} [Fintype ι]

/-- The class `J` weight `(1 + Σ_j |α_j| + |γ₁|)^θ` of DH21 (typeJ2) (`θ = 1/4` there). -/
@[expose] noncomputable def wJ (θ : ℝ) (α : ι → ℝ) (γ₁ : ℝ) : ℝ≥0∞ :=
  (1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ) ^ θ

/-- The class `R` weight `(1 + Σ_j |α_j| + |γ₁| + |γ₃|)^θ` of DH21 (typeR2). -/
@[expose] noncomputable def wR (θ : ℝ) (α : ι → ℝ) (γ₁ γ₃ : ℝ) : ℝ≥0∞ :=
  (1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ

/-- The left side of DH21 (typeJ2) for derivatives of order `k`. -/
@[expose] noncomputable def jNorm (θ : ℝ) (k : ℕ) (m : (ι → ℝ) → ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ α, ∫⁻ γ, wJ θ α γ.1 * dnorm k m α γ

/-- The left side of DH21 (typeR2) for derivatives of order `k`. -/
@[expose] noncomputable def rNorm (θ : ℝ) (k : ℕ) (m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ α, ∫⁻ γ, wR θ α γ.1 γ.2.2 * dnorm k m α γ

/-- The datum of a basic class `J` operator: a bundle and a symbol. -/
structure JSym (ι : Type*) where
  /-- The coefficients of the bundle `ℓ = Σ_j y_j α_j`. -/
  y : ι → ℤ
  /-- The symbol `m(α, γ₁, γ₂)`. -/
  m : (ι → ℝ) → ℝ × ℝ → ℂ

/-- DH21 (typeJ0)–(typeJ2) with bound `N · A^k · (2k)!`. -/
structure JSym.Bound (R : JSym ι) (θ A N : ℝ) : Prop where
  nonneg : 0 ≤ N
  bundle : IsBundle R.y
  reg : SymReg R.m
  norm : ∀ k, jNorm θ k R.m ≤ gev N A k

/-- The kernel of the basic class `J` operator `∫ m(α, γ) J_{ℓ(α); γ₁, γ₂} dγ` (DH21 (typeJ0)). -/
@[expose] noncomputable def JSym.kernel (R : JSym ι) (α : ι → ℝ) (t s : ℝ) : ℂ :=
  ∫ γ : ℝ × ℝ, R.m α γ * jker (bundle R.y α) γ.1 γ.2 t s

/-- The datum of a basic class `R` operator: a sign, two bundles of the non-special variables,
and a symbol independent of the special variable. -/
structure RSym (ι : Type*) where
  /-- The sign `ε ∈ {±1}` of the special variable. -/
  ε : ℤ
  /-- The coefficients of the bundle `ℓ₁`. -/
  y₁ : ι → ℤ
  /-- The coefficients of the bundle `ℓ₂`. -/
  y₂ : ι → ℤ
  /-- The symbol `m(α[A \ {1}], γ₁, γ₂, γ₃)`. -/
  m : (ι → ℝ) → ℝ × ℝ × ℝ → ℂ

/-- DH21 (typeR0)–(typeR2) with bound `N · A^k · (2k)!`. -/
structure RSym.Bound (R : RSym ι) (θ A N : ℝ) : Prop where
  nonneg : 0 ≤ N
  sign : R.ε = 1 ∨ R.ε = -1
  bundle₁ : IsBundle R.y₁
  bundle₂ : IsBundle R.y₂
  reg : SymReg R.m
  norm : ∀ k, rNorm θ k R.m ≤ gev N A k

/-- The non-special variables `α[A \ {1}]` of `α : Option ι → ℝ`. -/
@[expose] def nsp (α : Option ι → ℝ) : ι → ℝ := fun i => α (some i)

/-- The kernel of the basic class `R` operator
`∫ m(α[A \ {1}], γ) R_{ℓ₁ + ε α₁, ℓ₂ + ε α₁; γ₁, γ₂, γ₃} dγ` (DH21 (typeR0)); the special
variable is `α₁ = α none`. -/
@[expose] noncomputable def RSym.kernel (R : RSym ι) (α : Option ι → ℝ) (t s : ℝ) : ℂ :=
  ∫ γ : ℝ × ℝ × ℝ, R.m (nsp α) γ *
    rker (bundle R.y₁ (nsp α) + R.ε * α none) (bundle R.y₂ (nsp α) + R.ε * α none)
      γ.1 γ.2.1 γ.2.2 t s

end WaveTurbulence.ClassJR
