/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volterra kernels and the elementary operators of DH21 §5.2

DH21 (L946–L954) works with operators on functions on `[0, 1]` of the form
`f ↦ ∫_0^t K(t, s) f(s) ds`. We represent such an operator by its kernel `K : ℝ → ℝ → ℂ`, of
which only the values on the triangle `0 ≤ s ≤ t ≤ 1` matter (`KEqOn`). Composition of operators
corresponds to the kernel composition `(K ∘ L)(t, s) = ∫_s^t K(t, z) L(z, s) dz` (`kcomp`).

* `iker β`: the kernel `e^{πiβs}` of `I_β f(t) = ∫_0^t e^{πiβs} f(s) ds`;
* `jker ℓ γ₁ γ₂`: the kernel `e^{πiℓ(t-s)} e^{πi(γ₁t+γ₂s)}` of `J_{ℓ;γ₁,γ₂}`;
* `rker a b γ₁ γ₂ γ₃`: the kernel `χ_∞(a+γ₃)/(a+γ₃) · e^{πib(t-s)} e^{πi(γ₁t+γ₂s)}` of
  `R_{a,b;γ₁,γ₂,γ₃}`;
* `eInt x v = ∫_0^v e^{πixu} du`.

The basic identity (`kcomp_jker`, the first display in the proof of DH21 Lemma 5.3, L971–L975):
`J_{ℓ₁;γ₁,γ₂} J_{ℓ₂;γ₃,γ₄}` has kernel
`e^{πiℓ₁(t-s) + πiγ₁t + πi(γ₂+γ₃+γ₄)s} · ∫_0^{t-s} e^{πi(ℓ₂-ℓ₁+γ₂+γ₃)u} du`.
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real

namespace WaveTurbulence.ClassJR

/-- The Volterra operator with kernel `K`: `f ↦ (t ↦ ∫_0^t K(t,s) f(s) ds)`. -/
@[expose] noncomputable def volterra (K : ℝ → ℝ → ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, K t s * f s

/-- Composition of Volterra kernels: `(K ∘ L)(t, s) = ∫_s^t K(t, z) L(z, s) dz`. -/
@[expose] noncomputable def kcomp (K L : ℝ → ℝ → ℂ) (t s : ℝ) : ℂ :=
  ∫ z in s..t, K t z * L z s

/-- Two kernels agree on the triangle `0 ≤ s ≤ t ≤ 1`. -/
@[expose] def KEqOn (K L : ℝ → ℝ → ℂ) : Prop :=
  ∀ t s : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → K t s = L t s

/-- The kernel `e^{πiβs}` of `I_β`. -/
@[expose] noncomputable def iker (β : ℝ) (_t s : ℝ) : ℂ := cexp (π * I * (β * s))

/-- The kernel of `J_{ℓ;γ₁,γ₂}`: `e^{πiℓ(t-s)} e^{πi(γ₁t+γ₂s)}`. -/
@[expose] noncomputable def jker (ℓ γ₁ γ₂ : ℝ) (t s : ℝ) : ℂ :=
  cexp (π * I * (ℓ * (t - s) + γ₁ * t + γ₂ * s))

/-- The factor `χ_∞(x)/x` of the class `R` operators (DH21 L953). -/
@[expose] noncomputable def chiInvR (x : ℝ) : ℝ := Fourier.chiInfinity x / x

/-- The kernel of `R_{a,b;γ₁,γ₂,γ₃}`: `χ_∞(a+γ₃)/(a+γ₃) · e^{πib(t-s)} e^{πi(γ₁t+γ₂s)}`. -/
@[expose] noncomputable def rker (a b γ₁ γ₂ γ₃ : ℝ) (t s : ℝ) : ℂ :=
  (chiInvR (a + γ₃) : ℂ) * jker b γ₁ γ₂ t s

/-- `E(x, v) = ∫_0^v e^{πixu} du`. -/
@[expose] noncomputable def eInt (x v : ℝ) : ℂ := ∫ u in (0 : ℝ)..v, cexp (π * I * (x * u))

theorem KEqOn.refl (K : ℝ → ℝ → ℂ) : KEqOn K K := fun _ _ _ _ _ => rfl

theorem KEqOn.symm {K L : ℝ → ℝ → ℂ} (h : KEqOn K L) : KEqOn L K :=
  fun t s h1 h2 h3 => (h t s h1 h2 h3).symm

theorem KEqOn.trans {K L N : ℝ → ℝ → ℂ} (h : KEqOn K L) (h' : KEqOn L N) : KEqOn K N :=
  fun t s h1 h2 h3 => (h t s h1 h2 h3).trans (h' t s h1 h2 h3)

/-- `jker` is a product of exponentials. -/
theorem jker_eq (ℓ γ₁ γ₂ t s : ℝ) :
    jker ℓ γ₁ γ₂ t s = cexp (π * I * (ℓ * (t - s))) * cexp (π * I * (γ₁ * t + γ₂ * s)) := by
  rw [jker, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `E(x, v) = (e^{πixv} - 1)/(πix)` for `x ≠ 0`. -/
theorem eInt_eq_of_ne {x : ℝ} (hx : x ≠ 0) (v : ℝ) :
    eInt x v = (cexp (π * I * (x * v)) - 1) / (π * I * x) := by
  have hc : (π * I * x : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hx, Complex.I_ne_zero]
  have h := integral_exp_mul_complex (a := 0) (b := v) hc
  simp only [eInt]
  rw [show (fun u : ℝ => cexp (π * I * (x * u))) = fun u : ℝ => cexp (π * I * x * u) by
    funext u; ring_nf]
  rw [h]; push_cast
  simp only [mul_zero, Complex.exp_zero]
  rw [show (π : ℂ) * I * x * v = π * I * (x * v) by ring]

/-- **The composition `J_{ℓ₁;γ₁,γ₂} J_{ℓ₂;γ₃,γ₄}`** (DH21 L971–L975). -/
theorem kcomp_jker (ℓ₁ γ₁ γ₂ ℓ₂ γ₃ γ₄ t s : ℝ) :
    kcomp (jker ℓ₁ γ₁ γ₂) (jker ℓ₂ γ₃ γ₄) t s =
      jker ℓ₁ γ₁ (γ₂ + γ₃ + γ₄) t s * eInt (ℓ₂ - ℓ₁ + γ₂ + γ₃) (t - s) := by
  simp only [kcomp, eInt]
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_add_left (a := 0) (b := t - s)
    (fun z => jker ℓ₁ γ₁ γ₂ t z * jker ℓ₂ γ₃ γ₄ z s) s
  simp only [add_zero, add_sub_cancel] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [jker, ← Complex.exp_add]
  congr 1; push_cast; ring

end WaveTurbulence.ClassJR
