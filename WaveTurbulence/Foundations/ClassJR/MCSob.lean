/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Reindex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A crude Sobolev inequality: integrated derivatives bound the supremum

For a smooth `G : ℝⁿ → E`, `‖G(α)‖ ≤ 2ⁿ Σ_{j ≤ n} ∫ ‖D^j G‖` (`enorm_le_sum_lintegral_iteratedFDeriv`).

The proof is the unit-cube form of the fundamental theorem of calculus. In one variable,
`‖h(x)‖ ≤ ∫_x^{x+1} (‖h‖ + ‖h'‖)` (`enorm_le_lintegral_Icc`); it is iterated over the coordinates.

DH21 Proposition 5.1 (L936–L944) bounds the `L¹(dα dλ)` norms of the `α`-derivatives of its
coefficients `𝒞`. Its frequencies `λ` are shifted by bundles of the `α` variables (DH21 (expandG)),
so the supremum over `α` is not controlled factor by factor. This inequality turns the integrated
bounds into the domination clause of `SymReg` (`SymReg.of_lintegral`). The constants are irrelevant:
the result is used only qualitatively, to differentiate under the integral sign.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

section OneD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The one-dimensional cube inequality**: `‖h(x)‖ ≤ ∫_{[x, x+1]} (‖h‖ + ‖h'‖)`. -/
theorem enorm_le_lintegral_Icc {h : ℝ → E} (hh : ContDiff ℝ 1 h) (x : ℝ) :
    ‖h x‖ₑ ≤ ∫⁻ y in Icc x (x + 1), (‖h y‖ₑ + ‖deriv h y‖ₑ) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  have key : ∀ y ∈ Icc x (x + 1),
      ‖h x‖ₑ ≤ ‖h y‖ₑ + ∫⁻ z in Icc x (x + 1), ‖deriv h z‖ₑ := by
    intro y hy
    have hFTC : ∫ z in x..y, deriv h z = h y - h x :=
      intervalIntegral.integral_deriv_eq_sub (fun z _ => hdiff z) (hd.intervalIntegrable _ _)
    have e : h x = h y - ∫ z in x..y, deriv h z := by rw [hFTC]; abel
    rw [e]
    refine (enorm_sub_le).trans (add_le_add le_rfl ?_)
    rw [intervalIntegral.integral_of_le hy.1]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    exact lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hy.2))
  have hvol : volume (Icc x (x + 1)) = 1 := by rw [Real.volume_Icc]; simp
  calc ‖h x‖ₑ = ∫⁻ _ in Icc x (x + 1), ‖h x‖ₑ := by rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ y in Icc x (x + 1), (‖h y‖ₑ + ∫⁻ z in Icc x (x + 1), ‖deriv h z‖ₑ) :=
        setLIntegral_mono' measurableSet_Icc key
    _ = (∫⁻ y in Icc x (x + 1), ‖h y‖ₑ) + ∫⁻ z in Icc x (x + 1), ‖deriv h z‖ₑ := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, hvol, mul_one]
    _ = _ := by
        rw [lintegral_add_left hh.continuous.enorm.measurable]

end OneD

section NDim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The embedding `β' ↦ (0, β')` of `ℝⁿ` into `ℝⁿ⁺¹`. -/
@[expose] noncomputable def consZero (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i => Fin.cases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
    (fun j => ContinuousLinearMap.proj j) i

theorem consZero_apply (n : ℕ) (β : Fin n → ℝ) : consZero n β = Fin.cons 0 β := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]

theorem norm_consZero_le (n : ℕ) : ‖consZero n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun β => ?_
  rw [one_mul, consZero_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg β)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using norm_le_pi_norm β j

theorem cons_eq_consZero_add (n : ℕ) (y : ℝ) (β : Fin n → ℝ) :
    (Fin.cons y β : Fin (n + 1) → ℝ) = consZero n β + Fin.cons y 0 := by
  rw [consZero_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

omit [CompleteSpace E] in
theorem norm_iteratedFDeriv_slice_le {n : ℕ} {G : (Fin (n + 1) → ℝ) → E} (hG : ContDiff ℝ ∞ G) (y : ℝ)
    (j : ℕ) (β : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (fun β' : Fin n → ℝ => G (Fin.cons y β')) β‖ ≤
      ‖iteratedFDeriv ℝ j G (Fin.cons y β)‖ := by
  have e : (fun β' : Fin n → ℝ => G (Fin.cons y β')) =
      (fun z => G (z + Fin.cons y 0)) ∘ consZero n := by
    funext β'; simp only [Function.comp_apply]; rw [cons_eq_consZero_add]
  have hT : ContDiff ℝ ∞ fun z : Fin (n + 1) → ℝ => G (z + Fin.cons y 0) :=
    hG.comp (contDiff_id.add contDiff_const)
  rw [e, (consZero n).iteratedFDeriv_comp_right hT β (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right, ← cons_eq_consZero_add]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ j G (Fin.cons y β)‖ * ∏ _i : Fin j, ‖consZero n‖
      ≤ ‖iteratedFDeriv ℝ j G (Fin.cons y β)‖ * 1 := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) (norm_consZero_le n)
    _ = _ := mul_one _

/-- The unit vector `e₀` of `ℝⁿ⁺¹`. -/
@[expose] noncomputable def e0 (n : ℕ) : Fin (n + 1) → ℝ := Pi.single 0 1

theorem norm_e0 (n : ℕ) : ‖e0 n‖ = 1 := by simp [e0, Pi.norm_single]

omit [CompleteSpace E] in
theorem norm_iteratedFDeriv_slice_deriv_le {n : ℕ} {G : (Fin (n + 1) → ℝ) → E} (hG : ContDiff ℝ ∞ G)
    (y : ℝ) (j : ℕ) (β : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β') (e0 n)) β‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) G (Fin.cons y β)‖ := by
  have hF : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by exact_mod_cast le_top)
  have e : (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β') (e0 n)) =
      (ContinuousLinearMap.apply ℝ E (e0 n)) ∘ (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β')) :=
    rfl
  have hS : ContDiff ℝ ∞ fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β') := by
    have : (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β')) =
        (fun z => fderiv ℝ G (z + Fin.cons y 0)) ∘ consZero n := by
      funext β'; simp only [Function.comp_apply]; rw [cons_eq_consZero_add]
    rw [this]
    exact (hF.comp (contDiff_id.add contDiff_const)).comp (consZero n).contDiff
  rw [e, (ContinuousLinearMap.apply ℝ E (e0 n)).iteratedFDeriv_comp_left hS.contDiffAt
    (by exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hap : ‖ContinuousLinearMap.apply ℝ E (e0 n)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
    rw [one_mul]
    calc ‖ContinuousLinearMap.apply ℝ E (e0 n) L‖ = ‖L (e0 n)‖ := rfl
      _ ≤ ‖L‖ * ‖e0 n‖ := L.le_opNorm _
      _ = ‖L‖ := by rw [norm_e0, mul_one]
  calc ‖ContinuousLinearMap.apply ℝ E (e0 n)‖ *
        ‖iteratedFDeriv ℝ j (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β')) β‖
      ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ G) (Fin.cons y β)‖ := by
        gcongr
        exact norm_iteratedFDeriv_slice_le hF y j β
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

theorem measurable_cons_comp {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) := by
  have : (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) =
      F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm := by
    funext p; simp [MeasurableEquiv.piFinSuccAbove]; rfl
  rw [this]
  exact hF.comp (MeasurableEquiv.piFinSuccAbove _ 0).symm.measurable

/-- Measurability of the slice integrals. -/
theorem measurable_lintegral_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun y : ℝ => ∫⁻ β' : Fin n → ℝ, F (Fin.cons y β') :=
  (measurable_cons_comp hF).lintegral_prod_right'

/-- `∫ F = ∫_y ∫_{β'} F(y, β')` on `ℝⁿ⁺¹`. -/
theorem lintegral_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ β, F β = ∫⁻ y : ℝ, ∫⁻ β' : Fin n → ℝ, F (Fin.cons y β') := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e.symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
    simp [he, MeasurableEquiv.piFinSuccAbove]; rfl
  calc ∫⁻ β, F β = ∫⁻ p : ℝ × (Fin n → ℝ), F (e.symm p) :=
        (hmp.lintegral_comp_emb e.symm.measurableEmbedding F).symm
    _ = ∫⁻ p : ℝ × (Fin n → ℝ), F (Fin.cons p.1 p.2) := by simp_rw [hsymm]
    _ = _ := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod _ (measurable_cons_comp hF).aemeasurable

/-- **The cube inequality in `n` variables**: `‖G(α)‖ ≤ 2ⁿ Σ_{j ≤ n} ∫ ‖D^j G‖`. -/
theorem enorm_le_sum_lintegral_iteratedFDeriv :
    ∀ (n : ℕ) (G : (Fin n → ℝ) → E), ContDiff ℝ ∞ G → ∀ α : Fin n → ℝ,
      ‖G α‖ₑ ≤ 2 ^ n * ∑ j ∈ range (n + 1), ∫⁻ β, ‖iteratedFDeriv ℝ j G β‖ₑ
  | 0, G, _, α => by
    have hα : α = default := Subsingleton.elim _ _
    simp only [pow_zero, one_mul, zero_add, range_one, sum_singleton]
    rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default by
      rw [MeasureTheory.volume_pi]; exact Measure.pi_of_empty _ _, lintegral_dirac, hα]
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
  | n + 1, G, hG, α => by
    set a := Fin.tail α with ha
    -- the line through `α` in the direction `e₀`
    set h : ℝ → E := fun y => G (Fin.cons y a) with hh
    have hline : ∀ y, (Fin.cons y a : Fin (n + 1) → ℝ) = y • e0 n + Fin.cons 0 a := fun y => by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [e0]
    have hcomp : h = G ∘ fun y => y • e0 n + Fin.cons 0 a := by
      funext y; simp only [hh, Function.comp_apply]; rw [hline y]
    have hhd : ∀ y, HasDerivAt h (fderiv ℝ G (Fin.cons y a) (e0 n)) y := fun y => by
      have hl : HasDerivAt (fun y : ℝ => y • e0 n + Fin.cons 0 a) (e0 n) y := by
        simpa using ((hasDerivAt_id y).smul_const (e0 n)).add_const (Fin.cons 0 a : Fin (n + 1) → ℝ)
      have hG' := (hG.differentiable (by simp) (y • e0 n + Fin.cons 0 a)).hasFDerivAt
      have := hG'.comp_hasDerivAt y hl
      rw [hcomp, hline y]
      exact this
    have hhc : ContDiff ℝ 1 h := by
      rw [hcomp]
      exact (hG.of_le (by exact_mod_cast le_top)).comp
        ((contDiff_id.smul contDiff_const).add contDiff_const)
    have hderiv : ∀ y, deriv h y = fderiv ℝ G (Fin.cons y a) (e0 n) := fun y => (hhd y).deriv
    have h0 : h (α 0) = G α := by simp [hh, ha, Fin.cons_self_tail]
    -- the slices
    have hS : ∀ y, ContDiff ℝ ∞ fun β' : Fin n → ℝ => G (Fin.cons y β') := fun y => by
      have : (fun β' : Fin n → ℝ => G (Fin.cons y β')) =
          (fun z => G (z + Fin.cons y 0)) ∘ consZero n := by
        funext β'; simp only [Function.comp_apply]; rw [cons_eq_consZero_add]
      rw [this]
      exact (hG.comp (contDiff_id.add contDiff_const)).comp (consZero n).contDiff
    have hS' : ∀ y, ContDiff ℝ ∞ fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β') (e0 n) :=
      fun y => by
        have hF : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by exact_mod_cast le_top)
        have : (fun β' : Fin n → ℝ => fderiv ℝ G (Fin.cons y β') (e0 n)) =
            (ContinuousLinearMap.apply ℝ E (e0 n)) ∘
              ((fun z => fderiv ℝ G (z + Fin.cons y 0)) ∘ consZero n) := by
          funext β'
          simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
          rw [cons_eq_consZero_add]
        rw [this]
        exact (ContinuousLinearMap.apply ℝ E (e0 n)).contDiff.comp
          ((hF.comp (contDiff_id.add contDiff_const)).comp (consZero n).contDiff)
    have hmeas : ∀ j, Measurable fun β : Fin (n + 1) → ℝ => ‖iteratedFDeriv ℝ j G β‖ₑ := fun j =>
      ((hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).enorm).measurable
    set I : ℕ → ℝ≥0∞ := fun j => ∫⁻ β, ‖iteratedFDeriv ℝ j G β‖ₑ with hI
    have hslice : ∀ y,
        ‖h y‖ₑ + ‖deriv h y‖ₑ ≤ 2 ^ n * ∑ j ∈ range (n + 1),
          ((∫⁻ β' : Fin n → ℝ, ‖iteratedFDeriv ℝ j G (Fin.cons y β')‖ₑ) +
            ∫⁻ β' : Fin n → ℝ, ‖iteratedFDeriv ℝ (j + 1) G (Fin.cons y β')‖ₑ) := fun y => by
      rw [hderiv, Finset.sum_add_distrib, mul_add]
      refine add_le_add ?_ ?_
      · refine (enorm_le_sum_lintegral_iteratedFDeriv n _ (hS y) a).trans ?_
        gcongr with j hj
        exact enorm_le_iff_norm_le.2 (norm_iteratedFDeriv_slice_le hG y j _)
      · refine (enorm_le_sum_lintegral_iteratedFDeriv n _ (hS' y) a).trans ?_
        gcongr with j hj
        exact enorm_le_iff_norm_le.2 (norm_iteratedFDeriv_slice_deriv_le hG y j _)
    calc ‖G α‖ₑ = ‖h (α 0)‖ₑ := by rw [h0]
      _ ≤ ∫⁻ y in Icc (α 0) (α 0 + 1), (‖h y‖ₑ + ‖deriv h y‖ₑ) := enorm_le_lintegral_Icc hhc _
      _ ≤ ∫⁻ y, (‖h y‖ₑ + ‖deriv h y‖ₑ) := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ y, 2 ^ n * ∑ j ∈ range (n + 1),
            ((∫⁻ β' : Fin n → ℝ, ‖iteratedFDeriv ℝ j G (Fin.cons y β')‖ₑ) +
              ∫⁻ β' : Fin n → ℝ, ‖iteratedFDeriv ℝ (j + 1) G (Fin.cons y β')‖ₑ) :=
          lintegral_mono hslice
      _ = 2 ^ n * ∑ j ∈ range (n + 1), (I j + I (j + 1)) := by
          rw [lintegral_const_mul _ ?_, lintegral_finsetSum _ ?_]
          · congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [lintegral_add_left ?_]
            · simp only [hI]
              rw [lintegral_cons (hmeas j), lintegral_cons (hmeas (j + 1))]
            exact (measurable_lintegral_cons (hmeas j))
          · intro j _
            exact (measurable_lintegral_cons (hmeas j)).add (measurable_lintegral_cons (hmeas (j + 1)))
          · exact Finset.measurable_sum _ fun j _ =>
              (measurable_lintegral_cons (hmeas j)).add (measurable_lintegral_cons (hmeas (j + 1)))
      _ = 2 ^ n * (∑ j ∈ range (n + 1), I j + ∑ j ∈ range (n + 1), I (j + 1)) := by
          rw [Finset.sum_add_distrib]
      _ ≤ 2 ^ n * (∑ j ∈ range (n + 1 + 1), I j + ∑ j ∈ range (n + 1 + 1), I j) := by
          gcongr
          · omega
          · rw [Finset.sum_range_succ' (fun j => I j) (n + 1)]
            exact le_add_right le_rfl
      _ = 2 ^ (n + 1) * ∑ j ∈ range (n + 1 + 1), I j := by rw [pow_succ]; ring

end NDim

section Symbols

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) :
    ∀ (j k : ℕ) (x : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x‖ =
      ‖iteratedFDeriv ℝ (k + j) f x‖
  | 0, k, x => by rw [norm_iteratedFDeriv_zero, Nat.add_zero]
  | j + 1, k, x => by
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (iteratedFDeriv ℝ k f) =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F) ∘
          iteratedFDeriv ℝ (k + 1) f := by
      rw [iteratedFDeriv_succ_eq_comp_left]
      funext y
      simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_iteratedFDeriv f j (k + 1) x, show k + 1 + j = k + (j + 1) by omega]

/-- The identification `ℝⁿ → ℓ¹(n)`. -/
@[expose] noncomputable def toL1 (n : ℕ) : (Fin n → ℝ) →L[ℝ] L1 (Fin n) :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap

theorem toL1_apply (n : ℕ) (β : Fin n → ℝ) : toL1 n β = WithLp.toLp 1 β := rfl

/-- **Sup bound in `n` variables**: `|∂^k m(α)| ≤ 2ⁿ Σ_{j ≤ n} ‖T‖^j ∫ |∂^{k+j} m|`. -/
theorem dnorm_le_sum_lintegral_fin {n : ℕ} {Γ : Type*} {m : (Fin n → ℝ) → Γ → ℂ} {γ : Γ}
    (hs : ContDiff ℝ ∞ fun α => m α γ) (k : ℕ) (α : Fin n → ℝ) :
    dnorm k m α γ ≤ 2 ^ n * ∑ j ∈ range (n + 1),
      ‖toL1 n‖ₑ ^ j * ∫⁻ β, dnorm (k + j) m β γ := by
  have hF : ContDiff ℝ ∞ (lift1 m γ) := contDiff_lift1 hs
  set Φ := iteratedFDeriv ℝ k (lift1 m γ) with hΦ
  have hΦs : ContDiff ℝ ∞ Φ := hF.iteratedFDeriv_right (by exact_mod_cast le_top)
  set G := Φ ∘ toL1 n with hG
  have hGs : ContDiff ℝ ∞ G := hΦs.comp (toL1 n).contDiff
  have hGα : ∀ β, ‖G β‖ₑ = dnorm k m β γ := fun β => rfl
  have hDG : ∀ j β, ‖iteratedFDeriv ℝ j G β‖ₑ ≤ ‖toL1 n‖ₑ ^ j * dnorm (k + j) m β γ := by
    intro j β
    rw [hG, (toL1 n).iteratedFDeriv_comp_right hΦs β (by exact_mod_cast le_top)]
    rw [← ofReal_norm, dnorm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hΦ,
      norm_iteratedFDeriv_iteratedFDeriv, mul_comm]
    rfl
  rw [← hGα]
  refine (enorm_le_sum_lintegral_iteratedFDeriv n G hGs α).trans ?_
  gcongr with j hj
  rw [← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_mono fun β => hDG j β

/-- **Sup bound for symbols in any finite set of variables.** -/
theorem exists_dnorm_le_sum_lintegral {ι : Type*} [Fintype ι] {Γ : Type*} (k : ℕ) :
    ∃ c : ℕ → ℝ≥0∞, (∀ j, c j ≠ ⊤) ∧ ∀ (m : (ι → ℝ) → Γ → ℂ) (γ : Γ),
      ContDiff ℝ ∞ (fun α => m α γ) → ∀ α, dnorm k m α γ ≤
        ∑ j ∈ range (Fintype.card ι + 1), c j * ∫⁻ β, dnorm (k + j) m β γ := by
  set n := Fintype.card ι
  set e : ι ≃ Fin n := Fintype.equivFin ι
  refine ⟨fun j => 2 ^ n * ‖toL1 n‖ₑ ^ j, fun j => by simp [ENNReal.mul_ne_top],
    fun m γ hs α => ?_⟩
  set m' : (Fin n → ℝ) → Γ → ℂ := fun α' γ => m (fun i => α' (e i)) γ
  have hs' : ContDiff ℝ ∞ fun α' => m' α' γ := hs.comp (contDiff_pi.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (e i)).contDiff)
  have hα : (fun i => (α ∘ e.symm) (e i)) = α := by funext i; simp
  have h1 := dnorm_le_sum_lintegral_fin (m := m') hs' k (α ∘ e.symm)
  rw [dnorm_reindex, hα] at h1
  refine h1.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]
  congr 2
  rw [← lintegral_reindex e]
  refine lintegral_congr fun β => ?_
  exact dnorm_reindex e m (k + j) β γ

/-- **Regularity from integrated derivative bounds.** A symbol that is smooth in `α`, jointly
measurable, and whose `α`-derivatives of every order have finite `L¹(dα dγ)` norm, satisfies the
domination clause of `SymReg`. -/
theorem SymReg.of_lintegral {ι : Type*} [Fintype ι] {Γ : Type*} [MeasureSpace Γ]
    [SFinite (volume : Measure Γ)] {m : (ι → ℝ) → Γ → ℂ}
    (hs : ∀ γ, ContDiff ℝ ∞ fun α => m α γ) (hm : StronglyMeasurable (Function.uncurry m))
    (hi : ∀ k, ∫⁻ α, ∫⁻ γ, dnorm k m α γ ≠ ⊤) : SymReg m where
  smooth := hs
  meas := hm
  dom k := by
    obtain ⟨c, hc, hb⟩ := exists_dnorm_le_sum_lintegral (ι := ι) (Γ := Γ) k
    have hmeas : ∀ j, Measurable (Function.uncurry (dnorm (k + j) m)) := fun j =>
      measurable_dnorm hs hm (k + j)
    have hsup : ∀ γ, supD k m γ ≤
        ∑ j ∈ range (Fintype.card ι + 1), c j * ∫⁻ β, dnorm (k + j) m β γ := fun γ =>
      iSup_le fun α => hb m γ (hs γ) α
    have hmeasI : ∀ j, Measurable fun γ => ∫⁻ β, dnorm (k + j) m β γ := fun j =>
      (hmeas j).lintegral_prod_left'
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hsup)
    rw [lintegral_finsetSum _ fun j _ => (hmeasI j).const_mul _]
    refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
    have hsw : AEMeasurable (Function.uncurry fun (γ : Γ) (β : ι → ℝ) => dnorm (k + j) m β γ)
        ((volume : Measure Γ).prod (volume : Measure (ι → ℝ))) :=
      ((hmeas j).comp measurable_swap).aemeasurable
    rw [lintegral_const_mul _ (hmeasI j), lintegral_lintegral_swap hsw]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hc j)) (lt_top_iff_ne_top.2 (hi (k + j)))

end Symbols

end WaveTurbulence.ClassJR
