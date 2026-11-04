/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TraceSymbol
public import WaveTurbulence.Foundations.ClassJR.MCSob

/-! # One derivative pays the frozen energy coordinate in the ℓ¹ symbol norm -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ClassJR WithLp
open scoped ContDiff ENNReal

/-- The one-coordinate affine path in the actual source ℓ¹ space. -/
theorem optionInsert_toLp_eq {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → ℝ) (r : ℝ) :
    toLp 1 (optionInsert r β) =
      optionZeroL1 (toLp 1 β)+r • (PiLp.single 1 none (1:ℝ) : L1 (Option ι)) := by
  ext i
  cases i <;> simp [optionInsert,optionZeroL1]

/-- The derivative of the source affine insertion has norm one. -/
theorem hasDerivAt_optionInsert_toLp {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → ℝ) (r : ℝ) :
    HasDerivAt (fun s => toLp 1 (optionInsert s β))
      (PiLp.single 1 none (1:ℝ) : L1 (Option ι)) r := by
  simp_rw [optionInsert_toLp_eq]
  simpa only [id_eq,one_smul] using ((hasDerivAt_id r).smul_const (PiLp.single 1 none (1:ℝ) : L1 (Option ι))).const_add
    (optionZeroL1 (toLp 1 β))

/-- Each derivative tensor along the coordinate line is paid by the next
full derivative tensor, without a factor depending on the variable count. -/
theorem norm_deriv_tensor_optionInsert_le {ι Γ : Type} [Fintype ι] [DecidableEq ι]
    {C : (Option ι → ℝ) → Γ → ℂ} {lam : Γ}
    (hs : ContDiff ℝ ∞ (fun α => C α lam)) (k : ℕ) (β : ι → ℝ) (r : ℝ) :
    ‖deriv (fun s => iteratedFDeriv ℝ k (lift1 C lam) (toLp 1 (optionInsert s β))) r‖ ≤
      ‖iteratedFDeriv ℝ (k+1) (lift1 C lam) (toLp 1 (optionInsert r β))‖ := by
  let Φ := iteratedFDeriv ℝ k (lift1 C lam)
  have hΦ : ContDiff ℝ ∞ Φ := (contDiff_lift1 hs).iteratedFDeriv_right (by exact_mod_cast le_top)
  have hd := (hΦ.differentiable (by simp) (toLp 1 (optionInsert r β))).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_optionInsert_toLp β r)
  change ‖deriv (Φ ∘ (fun s => toLp 1 (optionInsert s β))) r‖ ≤ _
  rw [hd.deriv]
  calc
    _ ≤ ‖fderiv ℝ Φ (toLp 1 (optionInsert r β))‖ * ‖(PiLp.single 1 none (1:ℝ) : L1 (Option ι))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ Φ (toLp 1 (optionInsert r β))‖ := by simp
    _ = _ := by
      exact norm_fderiv_iteratedFDeriv

end WaveTurbulence.RegAsymp
