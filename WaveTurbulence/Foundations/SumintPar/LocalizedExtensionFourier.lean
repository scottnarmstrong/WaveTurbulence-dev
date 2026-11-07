/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormalizedCoefficientExpansion
public import WaveTurbulence.Foundations.SumintPar.SourceExtensionIntegralBound
public import WaveTurbulence.Foundations.SumintPar.PhaseCellAgreement

/-!
# Exact spatial Fourier recombination of each localized ambient extension

The coefficient inverse decay cancels the kernel input decay exactly.
Finite rank permits coefficient inversion pointwise in every output time.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- The literal spatial Fourier recombination of one localized ambient extension. -/
@[expose] noncomputable def localizedSourceExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) : ℂ :=
  ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
    normalizedSourceCoefficient D L γ η a b (E 0 - E 1) ξ *
      (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ) *
      weightedSourceExtension D hI N h L γ δ η p
        (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) (E 0-E 1) t

/-- Exact finite spatial inversion for the actual ambient extension, at every output time. -/
theorem localizedSourceExtension_eq_sum {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (p : D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    localizedSourceExtension D hI N h L γ δ η a b p E t =
      ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ) *
        ∑ x ∈ inputCutoffBox L p,
          ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ) *
            localizedSourceWeight D L a b E x * phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t := by
  classical
  let C := normalizedSourceCoefficient D L γ η a b (E 0 - E 1)
  let χ := fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
    (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E):ℂ)
  let ν := fun ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d =>
    inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))
  let R : ℝ := ‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card
  let W := sourceWeightDecay D L γ η
  let Q := fun x : D.S.VIdx → Fin d → ℤ =>
    ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)
  let H := fun x : D.S.VIdx → Fin d → ℤ => phaseCellExtension D hI N h L γ δ η x (E 0-E 1) t
  have he : (fun ξ => C ξ*χ ξ*weightedSourceExtension D hI N h L γ δ η p (ν ξ) (E 0-E 1) t) =
      fun ξ => ∑ x ∈ inputCutoffBox L p,
        (C ξ*χ ξ*inputCharacter D L (ν ξ) x)*(((W*R:ℝ):ℂ)*Q x*H x) := by
    funext ξ
    rw [weightedSourceExtension_eq_sum D hI N h hL γ δ η hη,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [W,R,Q,H]
    ring
  have hi (x : D.S.VIdx → Fin d → ℤ) : Integrable
      (fun ξ => (C ξ*χ ξ*inputCharacter D L (ν ξ) x)*(((W*R:ℝ):ℂ)*Q x*H x)) :=
    (integrable_normalized_source_modulatedCoefficient hd D hL hD a b x E).mul_const _
  have hcancel : ((W*R:ℝ):ℂ)*(((W⁻¹:ℝ):ℂ)) = (R:ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    have hw : W ≠ 0 := (sourceWeightDecay_pos D hL γ η).ne'
    field_simp [hw]
  change (∫ ξ, C ξ*χ ξ*weightedSourceExtension D hI N h L γ δ η p (ν ξ) (E 0-E 1) t) = _
  rw [he,integral_finsetSum _ (fun x _ => hi x),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_mul_const,normalized_source_coefficient_expansion hd D hL hD a b x E]
  change (((W⁻¹:ℝ):ℂ)*localizedSourceWeight D L a b E x)*(((W*R:ℝ):ℂ)*Q x*H x) =
    (R:ℂ)*(Q x*localizedSourceWeight D L a b E x*H x)
  calc
    _ = (((W*R:ℝ):ℂ)*((W⁻¹:ℝ):ℂ))*(Q x*localizedSourceWeight D L a b E x*H x) := by ring
    _ = _ := by rw [hcancel]

end WaveTurbulence.SumintPar
