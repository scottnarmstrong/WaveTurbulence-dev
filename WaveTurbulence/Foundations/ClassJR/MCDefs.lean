/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCG
public import WaveTurbulence.Foundations.ClassJR.Chain2

/-!
# Definitions for DH21 Proposition 5.1 (the main coefficient estimate)

DH21 Proposition 5.1 (L936–L944), with the weights of DH23 (L955–L969), concerns functions
`ℬ̃(t, s, α)` of two times and of variables `α = α[𝒩^ch]`. It asserts that `ℬ̃` is a sum over `Z ⊆ 𝒩^ch` of
terms `∏_{𝔫∈Z} χ_∞(α_𝔫)/(ζ_𝔫πiα_𝔫) · ∫ 𝒞(λ₁, λ₂, α[𝒩^ch \ Z]) e^{πi(λ₁t + λ₂s)} dλ` with
* (maincoef2) `∫ ⟨max(λ₁,λ₂)⟩^{1-η/8} |∂_α^ρ 𝒞| ≤ C^n (2|ρ|)!`;
* (maincoef2.5) `∫ ⟨max(λ₁,λ₂)⟩^{η/4} max_𝔫 ⟨α_𝔫⟩^{1-η/2} |𝒞| ≤ C^n`.

Variables are points of a global type `V`, with signs `ζ : V → ℤ`. A function of finitely many of them
is `F : (V → ℝ) → ℝ → ℝ → ℂ`.

* `e2 λ t s = e^{πi(λ₁t + λ₂s)}`, `wL a λ = (1 + |λ₁| + |λ₂|)^a` (DH23's `⟨max(λ₁,λ₂)⟩^a` up to a factor
  `2^a`: the stronger reading of `⟨max⟩`, see the design notes).
* `MCRep θ a b A N S F`: on `[0,1]²`, `F α t s = ∫ 𝒞(α|_S, λ) e2 λ t s dλ` for a regular symbol `𝒞`
  (`SymReg`, the regularity that lets the induction re-enter: audit W3) on an index type `ι ≃ S`, with
  - (maincoef2) `∫∫ wL θ |∂^k 𝒞| ≤ gev N A k`;
  - (maincoef2.5) per variable, `∫∫ wL a (1 + |α_i|)^b |𝒞| ≤ N`.
* `PhiZ ζ z x = Φ(ζ_z x) = χ_∞(x)/(ζ_z π i x)` (`phiR_sign`).
* `MCExp θ a b A N ζ S F`: the expansion (maincoef3) `F = Σ_{Z⊆S} ∏_{z∈Z} PhiZ ζ z (α z) · G_Z` on `[0,1]²`,
  with `MCRep θ a b A N (S \ Z) G_Z`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Defs

variable {V : Type} [DecidableEq V]

/-- `e^{πi(λ₁ t + λ₂ s)}`. -/
@[expose] noncomputable def e2 (lam : ℝ × ℝ) (t s : ℝ) : ℂ := cexp (π * I * (lam.1 * t + lam.2 * s))

/-- The weight `(1 + |λ₁| + |λ₂|)^a` (DH23 `⟨max(λ₁, λ₂)⟩^a`). -/
@[expose] noncomputable def wL (a : ℝ) (lam : ℝ × ℝ) : ℝ≥0∞ := (1 + ‖lam.1‖ₑ + ‖lam.2‖ₑ) ^ a

/-- **A coefficient representation** (DH21 (maincoef1)–(maincoef2.5) with DH23 weights): on
`[0,1]²`, `F α t s = ∫ 𝒞(α ∘ f, λ) e^{πi(λ₁t+λ₂s)} dλ` for an injection `f : ι → V` with range `S`. -/
@[expose] def MCRep (θ a b A N : ℝ) (S : Set V) (F : (V → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → V) (C : (ι → ℝ) → ℝ × ℝ → ℂ),
    Function.Injective f ∧ Set.range f = S ∧ 0 ≤ N ∧ SymReg C ∧
    (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam * dnorm k C α lam ≤ gev N A k) ∧
    (∀ i : ι, ∫⁻ α, ∫⁻ lam, wL a lam * (1 + ‖α i‖ₑ) ^ b * ‖C α lam‖ₑ ≤ ENNReal.ofReal N) ∧
    ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F α t s = ∫ lam, C (α ∘ f) lam * e2 lam t s

/-- `Φ(ζ_z x) = χ_∞(x)/(ζ_z π i x)` (`phiR_sign`), the factor of a variable `z ∈ Z`. -/
@[expose] noncomputable def PhiZ (ζ : V → ℤ) (z : V) (x : ℝ) : ℂ := phiR (ζ z * x)

/-- **The expansion of DH21 (maincoef3)**: on `[0,1]²`,
`F = Σ_{Z ⊆ S} ∏_{z ∈ Z} Φ(ζ_z α_z) · G_Z` with `MCRep θ a b A N (S \ Z) G_Z`. -/
@[expose] def MCExp (θ a b A N : ℝ) (ζ : V → ℤ) (S : Finset V) (F : (V → ℝ) → ℝ → ℝ → ℂ) :
    Prop :=
  ∃ G : Finset V → (V → ℝ) → ℝ → ℝ → ℂ,
    (∀ Z ⊆ S, MCRep θ a b A N (↑(S \ Z)) (G Z)) ∧
    ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      F α t s = ∑ Z ∈ S.powerset, (∏ z ∈ Z, PhiZ ζ z (α z)) * G Z α t s

/-- A coefficient with its time arguments swapped when `b` holds (DH21: "the variables `(t₁, s₁)` may
be replaced by `(s₁, t₁)`, depending on the signs of the leaves", L924). -/
@[expose] def swapT (b : Bool) (F : (V → ℝ) → ℝ → ℝ → ℂ) : (V → ℝ) → ℝ → ℝ → ℂ :=
  if b then fun α t s => F α s t else F

/-- **The type 1 recursion** (DH21 (newexp1), L923): `∫_0^t ∫_0^s e^{πi α_v (t₁ - s₁)}
∏_{j=1}^3 F_j(t₁, s₁) ds₁ dt₁`, with time arguments swapped by `sw j`. -/
@[expose] noncomputable def type1F (v : V) (sw : Fin 3 → Bool)
    (F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ) : (V → ℝ) → ℝ → ℝ → ℂ :=
  fun α t s => ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s,
    cexp (π * I * (α v * (t₁ - s₁))) * ∏ j, swapT (sw j) (F j) α t₁ s₁

end Defs

end WaveTurbulence.ClassJR
