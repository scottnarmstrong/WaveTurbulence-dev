/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CountedSourceExtensionNorm
public import WaveTurbulence.Foundations.SumintPar.LocalizedExtensionAgreement
public import WaveTurbulence.Foundations.SumintPar.SourceLabelExpression

/-!
# Pointwise agreement of the complete explicit source ambient extension

All cutoff centers are chosen before the output momenta and times. The
counting integral is the actual absolutely convergent localization series
on the entire source cube, and equals the exact drafted expression.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace WaveTurbulence.SumintPar

/-- The exact drafted source expression has the complete explicit ambient extension on its output cube. -/
theorem exists_countedSourceExtension_agreement {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) {h : ℝ} (hh : 0 < h) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps) :
    ∃ p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ,
      ∀ E : Fin 4 → Mom d, (∀ j, ‖E j-D.centre j‖ ≤ 1) →
      ∀ t : Fin 3 → ℝ, (∀ j, t j ∈ Icc (0:ℝ) N) →
        countedSourceExtension D hI N h L γ δ η hD p E t = D.expr hI L γ δ η t E := by
  classical
  choose p hp using fun j : SourceLocalizationLabel D hD =>
    exists_localizedSourceExtension_agreement (δ := δ) hd D hI N hh hL hη hD j.1 j.2.val
  refine ⟨p,?_⟩
  intro E hE t ht
  let G := fun (j : SourceLocalizationLabel D hD) (x : D.S.VIdx → Fin d → ℤ) =>
    localizedSourceWeight D L j.1 j.2.val E x *
      (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ)
  have hs : Summable (fun q : SourceLocalizationLabel D hD × (D.S.VIdx → Fin d → ℤ) =>
      ‖G q.1 q.2‖) := summable_norm_sourceLabel_expression hd D hI hA hL hD E hE t
  have hm : Summable (fun j => ‖∑' x, G j x‖) :=
    hs.prod.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_tsum_le_tsum_norm (hs.prod_factor j))
  have he (j : SourceLocalizationLabel D hD) :
      localizedSourceExtension D hI N h L γ δ η j.1 j.2.val (p j) E t =
        ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
          ∑' x, G j x := hp j E hE t ht
  have hseries : Summable (fun j : SourceLocalizationLabel D hD =>
      ‖localizedSourceExtension D hI N h L γ δ η j.1 j.2.val (p j) E t‖) := by
    simp_rw [he,norm_mul]
    exact hm.mul_left _
  unfold countedSourceExtension
  rw [count_integral_eq_tsum _ hseries]
  simp_rw [he]
  rw [tsum_mul_left]
  have hsum := tsum_sourceLabel_expression (δ := δ) hd D hI hA hL hD E hE t
  change (∑' j, ∑' x, G j x) = _ at hsum
  rw [hsum]
  rfl

end WaveTurbulence.SumintPar
