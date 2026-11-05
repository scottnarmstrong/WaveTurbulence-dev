/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MaskedLeafLocalDensity

/-! # Joint measurability of the actual spatial derivative tensors -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ContDiff ENNReal

/-- The actual root derivative tensor is jointly measurable in lambda and
all leaf frequencies. The NT scalar is never differentiated in momentum. -/
theorem stronglyMeasurable_derivative_maskedLeafLocalDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      iteratedFDeriv ℝ j (maskedLeafLocalDensity hQ hG L δ γ J C F c z p.1 p.2) k) := by
  have hcont : Continuous (fun q : ℂ × Mom d =>
      iteratedFDeriv ℝ j (maskedModulation c q.1 q.2) k) :=
    continuous_iteratedFDeriv_smooth_modulated (sourceRootMask c) (contDiff_sourceRootMask c)
      (fun q : ℂ × Mom d => q.1) continuous_fst (fun q : ℂ × Mom d => q.2) continuous_snd k j
  have hcoef := stronglyMeasurable_leafSpectrumCoefficient (m := 2*Q.links.length+1) hK hB hF
  have hcoefMap : Measurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      (c,p.2)) := measurable_const.prodMk measurable_snd
  have hscalar := (hcoef.comp_measurable hcoefMap).mul
    (stronglyMeasurable_leafModulatedRemainder hQ hG hd hn L δ γ J hC z)
  have hfreq : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      ∑ a, toLp 2 (α a)) := by fun_prop
  have hfreqSM := hfreq.stronglyMeasurable.comp_measurable
    (measurable_snd : Measurable (Prod.snd :
      (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) → _))
  have hp := hscalar.prodMk hfreqSM
  have hh := hcont.stronglyMeasurable.comp_measurable hp.measurable
  simp_rw [maskedLeafLocalDensity_eq_maskedModulation]
  exact hh

end WaveTurbulence.RegAsymp
