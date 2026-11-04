/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionCounting
public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionNorm

/-!
# The full countable source ambient extension and its Fourier coefficient cost

All primary labels and their actual finite alternative families are
recombined by a genuine counting integral. The sharp norm cost is the
summed normalized Fourier coefficient mass, independent of step count.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- The complete source ambient extension for a chosen family of cutoff centers. -/
@[expose] noncomputable def countedSourceExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ) {A : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) : ℂ :=
  ∫ j : SourceLocalizationLabel D hD,
    localizedSourceExtension D hI N h L γ δ η j.1 j.2.val (p j) E t ∂Measure.count

/-- Conditional linear recombination estimate for the complete source ambient extension. -/
theorem XNorm00_countedSourceExtension_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    {V : Type*} [Countable V] (E : V → Fin 4 → Mom d)
    (hE : ∀ v j, ‖E v j-D.centre j‖ ≤ 1) (θ : ℝ) (B : ℝ≥0∞)
    (hF : ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d),
      XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (E v 0-E v 1) t) ≤ B) :
    XNorm00 θ (fun t v => countedSourceExtension D hI N h L γ δ η hD p (E v) t) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (30*d)*cellFourierFactor d)^D.S.M)*B := by
  let F := fun (j : SourceLocalizationLabel D hD) t v =>
    localizedSourceExtension D hI N h L γ δ η j.1 j.2.val (p j) (E v) t
  apply (XNorm00_count_integral_le θ F
    (fun j v => measurable_localizedSourceExtension hd D hI N h hL hη hD j.1 j.2.val (p j) (E v))
    (fun j v => integrable_localizedSourceExtension hd D hI N h hL hη hD j.1 j.2.val (p j) (E v))
    (fun v => tsum_localizedSourceExtension_mass_lt_top hd D hI N h hA hL hη hD p (E v) (hE v))).trans
  calc
    _ ≤ ∑' j : SourceLocalizationLabel D hD,
        (∫⁻ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d, ‖normalizedSourceCoefficient D L γ η j.1 j.2.val ξ‖ₑ)*B :=
      ENNReal.tsum_le_tsum (fun j => XNorm00_localizedSourceExtension_le hd D hI N h hL hη hD
        j.1 j.2.val (p j) E θ B (hF (p j)))
    _ = (∑' a, ∑ b ∈ sourceAlternativeLabels D hD a,
        ENNReal.ofReal (∫ ξ, ‖normalizedSourceCoefficient D L γ η a b ξ‖))*B := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp_rw [← ofReal_integral_norm_eq_lintegral_enorm
        (integrable_normalizedSourceCoefficient hd D hL hD _ _)]
      exact tsum_sourceLocalizationLabel D hD (fun a b =>
        ENNReal.ofReal (∫ ξ, ‖normalizedSourceCoefficient D L γ η a b ξ‖))
    _ ≤ _ := mul_le_mul' (tsum_normalizedSourceCoefficient_mass_le hd D hA hL hD) le_rfl

end WaveTurbulence.Sumint
