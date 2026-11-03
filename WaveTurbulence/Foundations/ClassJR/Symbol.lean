/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ParamDeriv
public import WaveTurbulence.Foundations.Combinatorics.BinomialConvolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Symbols of class `J` and `R` operators: derivatives, regularity, Gevrey arithmetic

A *symbol* is a function `m : (ι → ℝ) → Γ → ℂ` of the variables `α = α[A]` (indexed by a finite
type `ι`) and of auxiliary real variables `γ ∈ Γ`. DH21 Definition 5.2 (L955–L964) bounds the
`L¹(dα dγ)` norms of the `α`-derivatives `∂_α^ρ m` by `(2|ρ|)!`.

We measure the `k`-th `α`-derivative by the operator norm of `iteratedFDeriv` for the `ℓ¹` norm on
the `α` variables (`dnorm`). For a `k`-linear map on `ℓ¹(ι)` this operator norm is the largest
value on `k`-tuples of unit coordinate vectors, so `|∂_α^ρ m| ≤ dnorm |ρ| m` for every multi-index
`ρ`. With this norm a bundle `ℓ = Σ y_j α_j` (`y_j ∈ {-1, 0, 1}`) and a restriction to a subset of
the variables are linear maps of norm at most one, so the chain rule costs nothing.

* `SymReg`: qualitative regularity of a symbol (smooth in `α`, jointly measurable, every
  derivative dominated uniformly in `α` by an integrable function of `γ`); it is what is needed to
  differentiate under the integral sign in the composition formulas.
* `gev N A k = N A^k (2k)!` and `gev_conv_le`: the binary Gevrey-2 convolution (DH21 Lemma A.4,
  via `WaveTurbulence.Combinatorics.sum_choose_factorial_le`).
* `enorm_iteratedFDeriv_mul_le`, `enorm_iteratedFDeriv_comp_le`, `enorm_iteratedFDeriv_scalar_le`:
  Leibniz rule and chain rules in `ℝ≥0∞` form.
* `restrInl`, `restrInr`, `restrSome`, `bundleL`: the restriction and bundle maps on `ℓ¹`.
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

/-- `ι → ℝ` with the `ℓ¹` norm. -/
abbrev L1 (ι : Type*) : Type _ := PiLp 1 (fun _ : ι => ℝ)

section Gevrey

/-- The Gevrey-2 profile `N A^k (2k)!` as an extended real. -/
@[expose] noncomputable def gev (N A : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (N * A ^ k * (Nat.factorial (2 * k) : ℝ))

theorem gev_mono {N N' A A' : ℝ} (hN : N ≤ N') (hA0 : 0 ≤ A) (hA : A ≤ A') (hN' : 0 ≤ N')
    (k : ℕ) : gev N A k ≤ gev N' A' k := by
  unfold gev
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul hN (pow_le_pow_left₀ hA0 hA k) (pow_nonneg hA0 k) hN'

theorem gev_mul_const {N A : ℝ} (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    ENNReal.ofReal c * gev N A k = gev (c * N) A k := by
  unfold gev
  rw [← ENNReal.ofReal_mul hc]
  ring_nf

/-- **Binary Gevrey-2 convolution** (DH21 Lemma A.4 with two groups). -/
theorem gev_conv_le {S₁ S₂ : ℕ → ℝ≥0∞} {N₁ N₂ A : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) (hA : 0 ≤ A)
    (h₁ : ∀ j, S₁ j ≤ gev N₁ A j) (h₂ : ∀ j, S₂ j ≤ gev N₂ A j) (k : ℕ) :
    ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * S₁ j * S₂ (k - j) ≤ gev (4 * N₁ * N₂) A k := by
  calc ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * S₁ j * S₂ (k - j)
      ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * gev N₁ A j * gev N₂ A (k - j) := by
        gcongr with j hj
        · exact h₁ j
        · exact h₂ _
    _ = ENNReal.ofReal (∑ j ∈ range (k + 1), N₁ * N₂ * A ^ k *
          ((k.choose j : ℝ) * (Nat.factorial (2 * j) : ℝ) *
            (Nat.factorial (2 * (k - j)) : ℝ))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        unfold gev
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : A ^ k = A ^ j * A ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
        rw [this]
        ring
    _ ≤ gev (4 * N₁ * N₂) A k := by
        unfold gev
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        calc N₁ * N₂ * A ^ k * ∑ j ∈ range (k + 1), ((k.choose j : ℝ) *
              (Nat.factorial (2 * j) : ℝ) * (Nat.factorial (2 * (k - j)) : ℝ))
            ≤ N₁ * N₂ * A ^ k * (4 * (Nat.factorial (2 * k) : ℝ)) :=
              mul_le_mul_of_nonneg_left (Combinatorics.sum_choose_factorial_le k)
                (by positivity)
          _ = _ := by ring

end Gevrey

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Leibniz rule for `‖D^k (f g)‖ₑ`. -/
theorem enorm_iteratedFDeriv_mul_le {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ₑ ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * ‖iteratedFDeriv ℝ j f x‖ₑ *
        ‖iteratedFDeriv ℝ (k - j) g x‖ₑ := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast le_top)
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ofReal_norm, ofReal_norm]

/-- The chain rule for a continuous linear map of norm at most one. -/
theorem enorm_iteratedFDeriv_comp_le {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (P : E →L[ℝ] F)
    (hP : ‖P‖ ≤ 1) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ P) x‖ₑ ≤ ‖iteratedFDeriv ℝ k f (P x)‖ₑ := by
  rw [P.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    _ _).trans ?_)
  calc ‖iteratedFDeriv ℝ k f (P x)‖ * ∏ _i : Fin k, ‖P‖ ≤ ‖iteratedFDeriv ℝ k f (P x)‖ * 1 := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hP
    _ = _ := mul_one _

/-- The chain rule for `x ↦ f(L x + c)` with `L` a linear form of norm at most one. -/
theorem enorm_iteratedFDeriv_scalar_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] ℝ)
    (hL : ‖L‖ ≤ 1) (c : ℝ) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f (L y + c)) x‖ₑ ≤ ‖iteratedDeriv k f (L x + c)‖ₑ := by
  have hfc : ContDiff ℝ ∞ (fun y => f (y + c)) := hf.comp (contDiff_id.add contDiff_const)
  have := enorm_iteratedFDeriv_comp_le hfc L hL x k
  refine this.trans_eq ?_
  rw [iteratedFDeriv_comp_add_right, ← ofReal_norm, ← ofReal_norm,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]

end Calculus

section Lp

variable {ι : Type*} [Fintype ι] {ι' : Type*} [Fintype ι']

/-- Restriction to the left summand of the variables. -/
@[expose] noncomputable def restrInl : L1 (ι ⊕ ι') →L[ℝ] L1 ι :=
  LinearMap.mkContinuous
    { toFun := fun β => WithLp.toLp 1 (fun i => β (Sum.inl i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
        intro β
        simp only [one_mul, PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _))

/-- Restriction to the right summand of the variables. -/
@[expose] noncomputable def restrInr : L1 (ι ⊕ ι') →L[ℝ] L1 ι' :=
  LinearMap.mkContinuous
    { toFun := fun β => WithLp.toLp 1 (fun i => β (Sum.inr i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
        intro β
        simp only [one_mul, PiLp.norm_eq_of_L1, Fintype.sum_sum_type]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _))

/-- Restriction to the non-special variables `α[A \ {1}]` (`Option ι`, special index `none`). -/
@[expose] noncomputable def restrSome : L1 (Option ι) →L[ℝ] L1 ι :=
  LinearMap.mkContinuous
    { toFun := fun β => WithLp.toLp 1 (fun i => β (some i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
        intro β
        simp only [one_mul, PiLp.norm_eq_of_L1, Fintype.sum_option]
        exact le_add_of_nonneg_left (norm_nonneg _))

theorem norm_restrInl_le : ‖(restrInl : L1 (ι ⊕ ι') →L[ℝ] L1 ι)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_restrInr_le : ‖(restrInr : L1 (ι ⊕ ι') →L[ℝ] L1 ι')‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_restrSome_le : ‖(restrSome : L1 (Option ι) →L[ℝ] L1 ι)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp] theorem restrInl_toLp (α : ι ⊕ ι' → ℝ) :
    restrInl (WithLp.toLp 1 α) = WithLp.toLp 1 (fun i => α (Sum.inl i)) := rfl

@[simp] theorem restrInr_toLp (α : ι ⊕ ι' → ℝ) :
    restrInr (WithLp.toLp 1 α) = WithLp.toLp 1 (fun i => α (Sum.inr i)) := rfl

@[simp] theorem restrSome_toLp (α : Option ι → ℝ) :
    restrSome (WithLp.toLp 1 α) = WithLp.toLp 1 (fun i => α (some i)) := rfl

/-- A bundle `y·α = Σ_j y_j α_j` (DH21 L954, with integer coefficients). -/
@[expose] def bundle (y : ι → ℤ) (α : ι → ℝ) : ℝ := ∑ j, (y j : ℝ) * α j

/-- The coefficients of a bundle lie in `{-1, 0, 1}`. -/
@[expose] def IsBundle (y : ι → ℤ) : Prop := ∀ j, |y j| ≤ 1

/-- A bundle as a linear form on `ℓ¹`. -/
@[expose] noncomputable def bundleL (y : ι → ℤ) : L1 ι →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun β => bundle y (WithLp.ofLp β)
      map_add' := fun x z => by
        simp only [bundle, WithLp.ofLp_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [bundle, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring } (∑ j, |(y j : ℝ)|) (by
        intro β
        simp only [LinearMap.coe_mk, AddHom.coe_mk, bundle, PiLp.norm_eq_of_L1]
        calc ‖∑ j, (y j : ℝ) * β j‖ ≤ ∑ j, ‖(y j : ℝ) * β j‖ := norm_sum_le _ _
          _ = ∑ j, |(y j : ℝ)| * ‖β j‖ := by simp [norm_mul]
          _ ≤ ∑ j, (∑ i, |(y i : ℝ)|) * ‖β j‖ := by
              gcongr with j
              exact Finset.single_le_sum (f := fun i => |(y i : ℝ)|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
          _ = _ := by rw [Finset.mul_sum])

@[simp] theorem bundleL_apply (y : ι → ℤ) (β : L1 ι) : bundleL y β = bundle y (WithLp.ofLp β) :=
  rfl

/-- A bundle has norm at most one on `ℓ¹`. -/
theorem norm_bundleL_le {y : ι → ℤ} (hy : IsBundle y) : ‖bundleL y‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun β => ?_
  simp only [bundleL_apply, bundle, one_mul, PiLp.norm_eq_of_L1]
  calc ‖∑ j, (y j : ℝ) * β j‖ ≤ ∑ j, ‖(y j : ℝ) * β j‖ := norm_sum_le _ _
    _ = ∑ j, |(y j : ℝ)| * ‖β j‖ := by simp [norm_mul]
    _ ≤ ∑ j, 1 * ‖β j‖ := by
        gcongr with j
        exact_mod_cast hy j
    _ = _ := by simp

end Lp

section Symbols

variable {ι : Type*} [Fintype ι] {Γ : Type*}

/-- A symbol `m(α, γ)` viewed, for fixed `γ`, as a function on `ℓ¹(ι)`. -/
@[expose] def lift1 (m : (ι → ℝ) → Γ → ℂ) (γ : Γ) : L1 ι → ℂ := fun β => m (WithLp.ofLp β) γ

/-- `‖∂_α^k m(α, γ)‖`, for the `ℓ¹` norm on the `α` variables. -/
@[expose] noncomputable def dnorm (k : ℕ) (m : (ι → ℝ) → Γ → ℂ) (α : ι → ℝ) (γ : Γ) : ℝ≥0∞ :=
  ‖iteratedFDeriv ℝ k (lift1 m γ) (WithLp.toLp 1 α)‖ₑ

/-- `sup_α ‖∂_α^k m(α, γ)‖`. -/
@[expose] noncomputable def supD (k : ℕ) (m : (ι → ℝ) → Γ → ℂ) (γ : Γ) : ℝ≥0∞ :=
  ⨆ α, dnorm k m α γ

/-- **Qualitative regularity of a symbol**: smooth in `α`, jointly measurable, and every
`α`-derivative dominated uniformly in `α` by an integrable function of `γ`. -/
structure SymReg [MeasureSpace Γ] (m : (ι → ℝ) → Γ → ℂ) : Prop where
  smooth : ∀ γ, ContDiff ℝ ∞ (fun α => m α γ)
  meas : StronglyMeasurable (Function.uncurry m)
  dom : ∀ k, ∫⁻ γ, supD k m γ ≠ ⊤

theorem contDiff_lift1 {m : (ι → ℝ) → Γ → ℂ} {γ : Γ} (h : ContDiff ℝ ∞ (fun α => m α γ)) :
    ContDiff ℝ ∞ (lift1 m γ) :=
  h.comp (PiLp.continuousLinearEquiv 1 ℝ (fun _ : ι => ℝ)).contDiff

theorem continuous_dnorm {m : (ι → ℝ) → Γ → ℂ} {γ : Γ} (h : ContDiff ℝ ∞ (fun α => m α γ))
    (k : ℕ) : Continuous fun α => dnorm k m α γ :=
  continuous_enorm.comp (((contDiff_lift1 h).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).comp (PiLp.continuousLinearEquiv 1 ℝ
      (fun _ : ι => ℝ)).symm.continuous)

theorem dnorm_le_supD (k : ℕ) (m : (ι → ℝ) → Γ → ℂ) (α : ι → ℝ) (γ : Γ) :
    dnorm k m α γ ≤ supD k m γ :=
  le_iSup (fun α => dnorm k m α γ) α

/-- The derivative of order zero is the value. -/
theorem dnorm_zero (m : (ι → ℝ) → Γ → ℂ) (α : ι → ℝ) (γ : Γ) :
    dnorm 0 m α γ = ‖m α γ‖ₑ := by
  rw [dnorm, ← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  rfl

/-- A regular symbol is integrable in `γ` for each `α`. -/
theorem SymReg.integrable {Z : Type*} [MeasureSpace Z] {m : (ι → ℝ) → Z → ℂ} (h : SymReg m)
    (α : ι → ℝ) : Integrable (m α) := by
  refine ⟨(h.meas.comp_measurable measurable_prodMk_left).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun ζ => ?_) (lt_top_iff_ne_top.2 (h.dom 0))
  rw [← dnorm_zero]
  exact dnorm_le_supD 0 m α ζ

variable [MeasurableSpace Γ]

/-- Joint measurability of the `α`-derivatives of a symbol. -/
theorem stronglyMeasurable_iteratedFDeriv_lift1 {m : (ι → ℝ) → Γ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ (fun α => m α γ)) (hm : StronglyMeasurable (Function.uncurry m))
    (k : ℕ) :
    StronglyMeasurable fun p : (ι → ℝ) × Γ =>
      iteratedFDeriv ℝ k (lift1 m p.2) (WithLp.toLp 1 p.1) := by
  have h := stronglyMeasurable_uncurry_iteratedFDeriv_param
    (f := fun (β : L1 ι) (γ : Γ) => m (WithLp.ofLp β) γ) (fun γ => contDiff_lift1 (hs γ))
    (fun β => hm.comp_measurable (measurable_const.prodMk measurable_id)) k
  exact h.comp_measurable
    (((WithLp.measurable_toLp 1 (ι → ℝ)).comp measurable_fst).prodMk measurable_snd)

theorem measurable_dnorm {m : (ι → ℝ) → Γ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ (fun α => m α γ))
    (hm : StronglyMeasurable (Function.uncurry m)) (k : ℕ) :
    Measurable (Function.uncurry (dnorm k m)) :=
  (stronglyMeasurable_iteratedFDeriv_lift1 hs hm k).enorm

/-- The supremum of a continuous function equals its supremum over a dense set. -/
theorem iSup_eq_iSup_dense {X : Type*} [TopologicalSpace X] {D : Set X} (hD : Dense D)
    {f : X → ℝ≥0∞} (hf : Continuous f) : ⨆ x, f x = ⨆ x : D, f x := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => le_iSup f (x : X))
  have hcl : IsClosed {y : X | f y ≤ ⨆ x : D, f x} := isClosed_le hf continuous_const
  have hsub : D ⊆ {y : X | f y ≤ ⨆ x : D, f x} := fun y hy => le_iSup (fun x : D => f x) ⟨y, hy⟩
  have h := hcl.closure_subset_iff.mpr hsub
  rw [hD.closure_eq] at h
  exact h (Set.mem_univ x)

/-- The supremum over `α` of a continuous family is a countable supremum, hence measurable. -/
theorem measurable_supD {m : (ι → ℝ) → Γ → ℂ} (hs : ∀ γ, ContDiff ℝ ∞ (fun α => m α γ))
    (hm : StronglyMeasurable (Function.uncurry m)) (k : ℕ) : Measurable (supD k m) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (ι → ℝ)
  have : Countable D := hDc.to_subtype
  have heq : supD k m = fun γ => ⨆ α : D, dnorm k m α γ :=
    funext fun γ => iSup_eq_iSup_dense hD (continuous_dnorm (hs γ) k)
  rw [heq]
  exact Measurable.iSup fun α => (measurable_dnorm hs hm k).of_uncurry_left

end Symbols

end WaveTurbulence.ClassJR
