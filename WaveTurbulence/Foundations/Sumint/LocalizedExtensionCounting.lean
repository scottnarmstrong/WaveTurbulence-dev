/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.LocalizedExtensionMassBound
public import WaveTurbulence.Foundations.Sumint.SourceLocalizationLabels
public import WaveTurbulence.Foundations.Sumint.LocalizedLatticeMass
public import WaveTurbulence.Foundations.Sumint.CountableExtensionMinkowski

/-!
# Genuine countable recombination of the actual localized ambient extensions

The absolute time mass is summable over precisely the source primary
labels and their finite alternative families. No oscillatory gain is
spent to justify the counting-product integral.
-/

public section
open MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- Actual ambient time masses are summable over the complete source localization family. -/
theorem tsum_localizedSourceExtension_mass_lt_top {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) {A L γ δ η : ℝ} {Dsteps : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (p : SourceLocalizationLabel D hD → D.S.VIdx → Fin d → ℝ)
    (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    (∑' j : SourceLocalizationLabel D hD, ∫⁻ t,
      ‖localizedSourceExtension D hI N h L γ δ η j.1 j.2.val (p j) E t‖ₑ) < ⊤ := by
  obtain ⟨C,hC,hbound⟩ := exists_localizedSourceExtension_mass_bound (δ := δ) hd D hI N h hL hη hD
  calc
    _ ≤ ∑' j : SourceLocalizationLabel D hD,
        ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*C)*
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L j.1 j.2.val E x‖ₑ :=
      ENNReal.tsum_le_tsum (fun j => hbound j.1 j.2.val (p j) E)
    _ = ENNReal.ofReal (‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card*C)*
        ∑' a, ∑ b ∈ sourceAlternativeLabels D hD a,
          ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact tsum_sourceLocalizationLabel D hD (fun a b => ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (localized_source_weight_mass_lt_top hd D hA hL hD E hE)

end WaveTurbulence.Sumint
