/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import WaveTurbulence.Foundations.SumintPar.CountedSourceExtensionAgreement
public import WaveTurbulence.Foundations.SumintPar.CountedSourceExtensionNorm
public import WaveTurbulence.Foundations.SumintPar.LocalizedExtensionCounting

/-! # The localized ambient extension with a character-mixture multiplier (DEGEN-VINE)

`mixLocalized` is the finite-sum form of `SumintPar.localizedSourceExtension` with the multiplier
`m(E, x)` inserted in every lattice term.  Its agreement with the multiplied lattice sum, measurability,
integrability and time mass are proved as for the unmultiplied extension (`|m| ≤ mass`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- The multiplied localized ambient extension (finite sum over the cutoff box). -/
noncomputable def mixLocalized (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) : ℂ :=
  ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ) *
    ∑ x ∈ inputCutoffBox L p,
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ) *
        localizedSourceWeight D L a b E x * M.val L E x *
          phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t

/-- Agreement with the multiplied lattice expression on the output cube. -/
theorem exists_mixLocalized_agreement (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) {h : ℝ} (hh : 0 < h)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∃ p : D.S.VIdx → Fin d → ℝ, ∀ E : Fin 4 → Mom d,
      (∀ j, ‖E j-D.centre j‖ ≤ 1) → ∀ t : Fin 3 → ℝ,
      (∀ j, t j ∈ Icc (0:ℝ) N) →
      mixLocalized M hI N h L γ δ η a b p E t =
        ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
          ∑' x : D.S.VIdx → Fin d → ℤ, localizedSourceWeight D L a b E x * M.val L E x *
            (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) := by
  classical
  obtain ⟨p,hp⟩ := exists_inputCutoff_insertion D hD a b
  refine ⟨p,?_⟩
  intro E hE t ht
  have hinsert (x : D.S.VIdx → Fin d → ℤ) : localizedSourceWeight D L a b E x =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)*localizedSourceWeight D L a b E x :=
    hp E hE x
  have hzero (x : D.S.VIdx → Fin d → ℤ) (hx : x ∉ inputCutoffBox L p) :
      localizedSourceWeight D L a b E x = 0 := by
    rw [hinsert x,inputCutoff_product_eq_zero hL p x hx,Complex.ofReal_zero,zero_mul]
  unfold mixLocalized
  congr 1
  rw [tsum_eq_sum (s := inputCutoffBox L p) (fun x hx => by rw [hzero x hx,zero_mul,zero_mul])]
  apply Finset.sum_congr rfl
  intro x _
  rw [phaseCellExtension_agreement D hI N hh L γ δ η x (E 0-E 1) t ht, ← hinsert x]

theorem measurable_mixLocalized (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d) :
    Measurable (mixLocalized M hI N h L γ δ η a b p E) := by
  unfold mixLocalized
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro x _
  exact measurable_const.mul (measurable_phaseCellExtension D hI N h L γ δ η x (E 0-E 1))

theorem integrable_mixLocalized (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {L γ δ η : ℝ}
    (hL : 0 < L) (hη : η ≤ 1/3)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ) (E : Fin 4 → Mom d) :
    Integrable (mixLocalized M hI N h L γ δ η a b p E) := by
  unfold mixLocalized
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro x _
  exact (integrable_phaseCellExtension D hI N h L γ δ η hη x (E 0-E 1)).const_mul _

/-- Time mass of one multiplied localized extension. -/
theorem exists_mixLocalized_mass_bound (hd : 1 ≤ d) (M : CharMix D.S d) (hI : 0 < D.S.I) (N : ℕ) (h : ℝ)
    {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
      (E : Fin 4 → Mom d),
      (∫⁻ t, ‖mixLocalized M hI N h L γ δ η a b p E t‖ₑ) ≤
        ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*
          (C * M.mass)) *
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_phaseCellExtension_mass_bound D hI N h L γ δ η hη
  refine ⟨C,hC,?_⟩
  intro a b p E
  let R : ℝ := ‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card
  have hR : 0 ≤ R := by positivity
  have hQ (x : D.S.VIdx → Fin d → ℤ) :
      ‖((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inputCutoff_product_bounds p (fun v => latticePoint L (x v))).1]
    exact (ENNReal.ofReal_le_ofReal (inputCutoff_product_bounds p (fun v => latticePoint L (x v))).2).trans_eq ENNReal.ofReal_one
  have hMm (x : D.S.VIdx → Fin d → ℤ) : ‖M.val L E x‖ₑ ≤ ENNReal.ofReal M.mass := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (M.norm_val_le L E x)
  have hm (x : D.S.VIdx → Fin d → ℤ) :
      (∫⁻ t, ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (integrable_phaseCellExtension D hI N h L γ δ η hη x (E 0-E 1))]
    exact ENNReal.ofReal_le_ofReal (hbound x (E 0-E 1))
  have hpoint (t : Fin 3 → ℝ) : ‖mixLocalized M hI N h L γ δ η a b p E t‖ₑ ≤
      ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        (‖localizedSourceWeight D L a b E x‖ₑ * ENNReal.ofReal M.mass) *
          ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ := by
    unfold mixLocalized
    rw [enorm_mul, ← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR]
    apply mul_le_mul' le_rfl
    apply (enorm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x _
    rw [enorm_mul,enorm_mul,enorm_mul]
    exact mul_le_mul' (mul_le_mul' ((mul_le_mul' (hQ x) le_rfl).trans_eq (one_mul _)) (hMm x)) le_rfl
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        (‖localizedSourceWeight D L a b E x‖ₑ * ENNReal.ofReal M.mass) *
          ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        (‖localizedSourceWeight D L a b E x‖ₑ * ENNReal.ofReal M.mass) *
          (∫⁻ t, ‖phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t‖ₑ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)
      · intro x _
        exact measurable_const.mul (measurable_phaseCellExtension D hI N h L γ δ η x (E 0-E 1)).enorm
    _ ≤ ENNReal.ofReal R * ∑ x ∈ inputCutoffBox L p,
        (‖localizedSourceWeight D L a b E x‖ₑ * ENNReal.ofReal M.mass) * ENNReal.ofReal C := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum (fun x _ => mul_le_mul' le_rfl (hm x))
    _ = ENNReal.ofReal (R*(C * M.mass))*∑ x ∈ inputCutoffBox L p, ‖localizedSourceWeight D L a b E x‖ₑ := by
      rw [← Finset.sum_mul,ENNReal.ofReal_mul hR, ENNReal.ofReal_mul hC]
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)

end WaveTurbulence.DegenVinePar
