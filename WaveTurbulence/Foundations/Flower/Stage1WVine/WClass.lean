/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WHinge1

/-! # STAGE1W-VINE (T4 consumed): the weighted class sum in mode form

* `weightedClassFactorization_dep`: V5W-0's T4 `weightedClassFactorization` (one mode type `Ξ` for all type indices) in
  the form with mode types `Ξ i` depending on the type index (as main's `sum_tauClass_vineD_api_dep`): T4 is applied on the
  common mode type `Σ i, Ξ i` with the weights `sigWt` supported on the fiber of each `i` (the cross terms carry weight
  `0`; their integrability/summability is part of the hypotheses).
* `class_sum_modesW` (main's `class_sum_modes`, RepVD10, with the frontier weight): the sum of the weighted values over
  the unit class of the representative is the outer mode sum of the representative with the weighted class kernels
  `unitHkFW`, from the member identity `member_hVW` and the integrability data `member_integW`, `member_hsmW`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.VineEstS2

/-! ## Mode families on the common mode type `Σ i, Ξ i` -/

section Sigma
variable {I : Type*} {Ξ : I → Type*}

open scoped Classical in
/-- The weights on `Σ i, Ξ i` supported on the fiber of `i`. -/
def sigWt (Wt : ∀ i, Ξ i → ℂ) (i : I) (x : Σ i', Ξ i') : ℂ := if x.1 = i then Wt x.1 x.2 else 0

theorem sigWt_mk (Wt : ∀ i, Ξ i → ℂ) (i : I) (ξ : Ξ i) : sigWt Wt i ⟨i, ξ⟩ = Wt i ξ := by
  unfold sigWt
  rw [if_pos rfl]

theorem sigWt_ne (Wt : ∀ i, Ξ i → ℂ) (i i' : I) (h : i' ≠ i) (ξ : Ξ i') : sigWt Wt i ⟨i', ξ⟩ = 0 := by
  unfold sigWt
  rw [if_neg h]

theorem sigWt_support (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    ∀ x ∉ Set.range (Sigma.mk i : Ξ i → Σ i', Ξ i'), sigWt Wt i x * Φ x.1 x.2 = 0 := by
  rintro ⟨i', ξ⟩ hx
  by_cases h : i' = i
  · subst h; exact absurd ⟨ξ, rfl⟩ hx
  · rw [sigWt_ne Wt i i' h ξ, zero_mul]

theorem tsum_sigWt_mul (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    ∑' x : (Σ i', Ξ i'), sigWt Wt i x * Φ x.1 x.2 = ∑' ξ : Ξ i, Wt i ξ * Φ i ξ := by
  have hinj : Function.Injective (Sigma.mk i : Ξ i → Σ i', Ξ i') := sigma_mk_injective
  rw [← hinj.tsum_eq (f := fun x : (Σ i', Ξ i') => sigWt Wt i x * Φ x.1 x.2)]
  · exact tsum_congr fun ξ => by rw [sigWt_mk]
  · intro x hx
    by_contra hn
    exact hx (sigWt_support Wt Φ i x hn)

theorem summable_sigWt_mul_iff (Wt : ∀ i, Ξ i → ℂ) (Φ : ∀ i', Ξ i' → ℂ) (i : I) :
    Summable (fun x : (Σ i', Ξ i') => sigWt Wt i x * Φ x.1 x.2) ↔ Summable (fun ξ : Ξ i => Wt i ξ * Φ i ξ) := by
  have hinj : Function.Injective (Sigma.mk i : Ξ i → Σ i', Ξ i') := sigma_mk_injective
  rw [← hinj.summable_iff (sigWt_support Wt Φ i)]
  exact summable_congr fun ξ => by simp only [Function.comp_apply, sigWt_mk]

end Sigma

variable {p : ℕ}

end WaveTurbulence.Flower.Stage1WVine
