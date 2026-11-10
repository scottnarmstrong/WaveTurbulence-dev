/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma53

/-!
# Relabelling the variables of a class `J` operator

DH21 labels the variables `α[A]` by subsets `A` of the node set. Class `J` is invariant under
relabelling: for `e : ι ≃ ι'`, `ClassJ.reindex` transports a class `J` family in `α : ι → ℝ` to the
family `α' ↦ T (α' ∘ e)` with the same norm.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The relabelled basic class `J` datum: `m'(α', γ) = m(α' ∘ e, γ)`, `y' = y ∘ e⁻¹`. -/
@[expose] def JSym.reindex (e : ι ≃ ι') (R : JSym ι) : JSym ι' where
  y := fun j => R.y (e.symm j)
  m := fun α' γ => R.m (fun i => α' (e i)) γ

theorem bundle_reindex (e : ι ≃ ι') (y : ι → ℤ) (α' : ι' → ℝ) :
    bundle (fun j => y (e.symm j)) α' = bundle y fun i => α' (e i) := by
  unfold bundle
  exact (Equiv.sum_comp e fun j => (y (e.symm j) : ℝ) * α' j).symm.trans (by simp)

theorem JSym.reindex_kernel (e : ι ≃ ι') (R : JSym ι) (α' : ι' → ℝ) (t s : ℝ) :
    (R.reindex e).kernel α' t s = R.kernel (fun i => α' (e i)) t s := by
  simp only [JSym.kernel, JSym.reindex, bundle_reindex]

/-- The `ℓ¹` relabelling isometry `β' ↦ β' ∘ e`. -/
@[expose] noncomputable def relabelL (e : ι ≃ ι') : L1 ι' ≃ₗᵢ[ℝ] L1 ι :=
  LinearIsometryEquiv.piLpCongrLeft 1 ℝ ℝ e.symm

theorem relabelL_toLp (e : ι ≃ ι') (α' : ι' → ℝ) :
    relabelL e (WithLp.toLp 1 α') = WithLp.toLp 1 fun i => α' (e i) := by
  ext i
  simp [relabelL, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem ofLp_relabelL (e : ι ≃ ι') (β : L1 ι') :
    WithLp.ofLp (relabelL e β) = fun i => WithLp.ofLp β (e i) := by
  have := relabelL_toLp e (WithLp.ofLp β)
  simp only [WithLp.toLp_ofLp] at this
  rw [this]

theorem dnorm_reindex (e : ι ≃ ι') {Γ : Type*} (m : (ι → ℝ) → Γ → ℂ) (k : ℕ) (α' : ι' → ℝ)
    (γ : Γ) :
    dnorm k (fun α' γ => m (fun i => α' (e i)) γ) α' γ = dnorm k m (fun i => α' (e i)) γ := by
  have h : lift1 (fun α' γ => m (fun i => α' (e i)) γ) γ = lift1 m γ ∘ relabelL e := by
    funext β
    simp only [lift1, Function.comp_apply, ofLp_relabelL]
  rw [dnorm, dnorm, h, ← ofReal_norm, ← ofReal_norm,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, relabelL_toLp]

theorem sum_enorm_reindex (e : ι ≃ ι') (α' : ι' → ℝ) :
    ∑ j, ‖α' j‖ₑ = ∑ i, ‖α' (e i)‖ₑ :=
  (Equiv.sum_comp e fun j => ‖α' j‖ₑ).symm

theorem lintegral_reindex (e : ι ≃ ι') {F : (ι → ℝ) → ℝ≥0∞} :
    ∫⁻ α' : ι' → ℝ, F (fun i => α' (e i)) = ∫⁻ α, F α := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : ι' => ℝ) e).symm
  exact h.lintegral_comp_emb (MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ) e).symm.measurableEmbedding F

theorem SymReg.reindex (e : ι ≃ ι') {Γ : Type*} [MeasureSpace Γ] {m : (ι → ℝ) → Γ → ℂ}
    (h : SymReg m) : SymReg fun α' γ => m (fun i => α' (e i)) γ where
  smooth γ := (h.smooth γ).comp (contDiff_pi.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι' => ℝ) (e i)).contDiff)
  meas := by
    have hmeas : Measurable fun p : (ι' → ℝ) × Γ => ((fun i => p.1 (e i)), p.2) :=
      (Measurable.of_eval fun i => (measurable_pi_apply (e i)).comp measurable_fst).prodMk
        measurable_snd
    exact h.meas.comp_measurable hmeas
  dom k := by
    have : ∀ γ, supD k (fun α' γ => m (fun i => α' (e i)) γ) γ = supD k m γ := fun γ => by
      unfold supD
      simp_rw [dnorm_reindex]
      exact (e.arrowCongr (Equiv.refl ℝ)).symm.surjective.iSup_comp (fun α => dnorm k m α γ)
        |>.trans rfl
    simp_rw [this]
    exact h.dom k

theorem JSym.Bound.reindex (e : ι ≃ ι') {R : JSym ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    (R.reindex e).Bound θ A N where
  nonneg := h.nonneg
  bundle j := h.bundle (e.symm j)
  reg := h.reg.reindex e
  norm k := by
    refine le_of_eq_of_le ?_ (h.norm k)
    unfold jNorm
    simp only [JSym.reindex, dnorm_reindex]
    have hw : ∀ (α' : ι' → ℝ) (γ₁ : ℝ), wJ θ α' γ₁ = wJ θ (fun i => α' (e i)) γ₁ := by
      intro α' γ₁; unfold wJ; rw [sum_enorm_reindex e]
    simp_rw [hw]
    exact lintegral_reindex e (F := fun α => ∫⁻ γ : ℝ × ℝ, wJ θ α γ.1 * dnorm k R.m α γ)

end WaveTurbulence.ClassJR
