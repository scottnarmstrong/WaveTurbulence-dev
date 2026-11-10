/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Marginal
public import WaveTurbulence.Foundations.Cancel.Pieces
public import WaveTurbulence.Foundations.ClassJR.CompJJSetup
public import WaveTurbulence.Foundations.ClassJR.IRI3

/-!
# Class `J` and class `R` operators applied to an exponential are integrable (DH21 §7.1)

DH21 Lemmas 7.1–7.3 assert that `K = I(e^{πiλs})(t)` is in `L¹` of its variables `α[W]` when `I` is a class `J`
plus class `R` operator (DH21 L1720: "by repeating the proof of Proposition 5.1, we know that `K ∈ L¹`"). The
reason is plain:
* a basic class `J` kernel `∫ m(α, γ) J_{ℓ;γ₁,γ₂} dγ` is bounded by `∫ |m(α, γ)| dγ`, integrable in `α`;
* a basic class `R` kernel applied to `e^{πiλs}` is
  `∫ m(α', γ) χ_∞(a + γ₃)/(a + γ₃) e^{πi(b+γ₁)t} E(γ₂ + λ - b, t) dγ` with `a, b` affine in the special
  variable `α₁` (coefficient `ε = ±1`), and `|χ_∞(y)/y| ≲ ⟨y⟩⁻¹`, `|E(x, t)| ≲ ⟨x⟩⁻¹` give an integrable
  majorant in `α₁` (`lintegral_decay_pair`).

Main result: `mJR_mInt_volterra` (class `J` plus class `R` in the variables `W`, applied to an exponential,
is integrable over `α[W]`).
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology ENNReal

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR WaveTurbulence.Fourier

/-! ### Scalar bounds -/

/-! ### Basic class `J` kernels -/

section Basic

variable {ι : Type*} [Fintype ι]

/-! ### Basic class `R` kernels -/

end Basic

/-! ### Masked operators -/

section Masked

variable {V : Type} [DecidableEq V]

/-- The equivalence `ι ≃ W` of an injection with range `W`. -/
@[expose] noncomputable def eqvOfRange {ι : Type*} {W : Finset V} (f : ι → V)
    (hf : Function.Injective f) (hr : Set.range f = ↑W) : ι ≃ ↥W :=
  Equiv.ofBijective (fun i => ⟨f i, by rw [← Finset.mem_coe, ← hr]; exact ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf (congrArg Subtype.val h), fun w => by
      obtain ⟨i, hi⟩ : w.1 ∈ Set.range f := by rw [hr]; exact w.2
      exact ⟨i, Subtype.ext hi⟩⟩

/-- **Transport of integrability to `α[W]`** along an injection with range `W`. -/
theorem mInt_of_integrable_comp {ι : Type} [Fintype ι] {W : Finset V} {f : ι → V}
    (hf : Function.Injective f) (hr : Set.range f = ↑W) {G : (ι → ℝ) → ℂ} (hG : Integrable G)
    (α₀ : V → ℝ) : MInt W (fun α => G (α ∘ f)) α₀ := by
  set e := eqvOfRange f hf hr
  have hp := measurePreserving_piCongrLeft (fun _ : ↥W => (volume : Measure ℝ)) e
  have h2 := (hp.symm (MeasurableEquiv.piCongrLeft (fun _ : ↥W => ℝ) e)).integrable_comp_emb
    (MeasurableEquiv.piCongrLeft (fun _ : ↥W => ℝ) e).symm.measurableEmbedding (g := G)
  unfold MInt
  refine (h2.2 hG).congr (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  congr 1
  funext i
  have hi : f i ∈ W := by rw [← Finset.mem_coe, ← hr]; exact ⟨i, rfl⟩
  rw [Function.comp_apply, Function.updateFinset_def]
  simp only [hi, dite_true]
  have : (⟨f i, hi⟩ : ↥W) = e i := rfl
  rw [this]
  rw [MeasurableEquiv.coe_piCongrLeft] at *
  rfl

variable {P : Type*} [MeasurableSpace P] {θ A N : ℝ}

end Masked

end WaveTurbulence.Cancel
