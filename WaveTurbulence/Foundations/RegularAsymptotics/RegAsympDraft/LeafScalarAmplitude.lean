/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafLocalDensity
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialMeasure
public import WaveTurbulence.Foundations.RegAsymp.MaskedModulation

/-! # Actual leaf amplitudes for arbitrary measurable scalar source terms -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- The exact finite-cover scalar amplitude, before root modulation.
The scalar can be the NT remainder or the original Wick correction. -/
def leafScalarAmplitude {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {d : ℕ} (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) : ℂ :=
  if q.2.1.2 ∈ S q.2.1.1 then leafSpectrumCoefficient F q.2.1.1 q.2.2 *
    R q.1 (leafModulations hQ hG q.2.2).1 (leafModulations hQ hG q.2.2).2 q.2.1.2 else 0

/-- The literal source mask and root Fourier character multiply the
original scalar source term; no scalar is moved to the time kernel. -/
def maskedLeafScalarDensity {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {d : ℕ} (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) : ℂ :=
  maskedModulation q.2.1.1 (leafScalarAmplitude hQ hG R F S q) (∑ a, toLp 2 (q.2.2 a)) k

/-- Actual scalar amplitudes are jointly measurable in all source
parameters and countable choices of centers. -/
theorem stronglyMeasurable_leafScalarAmplitude {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R p.1 p.2.1 p.2.2 z))
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (leafScalarAmplitude hQ hG R F S) := by
  classical
  have hm : Measurable (fun p :
      ((Fin (2*Q.links.length+1) → Fin d → ℤ) × ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) ×
      ((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) =>
      if p.1.2 ∈ S p.1.1 then leafSpectrumCoefficient F p.1.1 p.2.2 *
        R p.2.1 (leafModulations hQ hG p.2.2).1 (leafModulations hQ hG p.2.2).2 p.1.2 else 0) := by
    apply measurable_from_prod_countable_right
    intro c
    by_cases hc : c.2 ∈ S c.1
    · simp only [hc,ite_true]
      have hcoefMap : Measurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) => (c.1,p.2)) :=
        measurable_const.prodMk measurable_snd
      have hcoef := (stronglyMeasurable_leafSpectrumCoefficient (m := 2*Q.links.length+1) hK hB hF).comp_measurable hcoefMap
      have hscalarMap : Measurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
          (p.1,leafModulations hQ hG p.2)) :=
        measurable_fst.prodMk ((continuous_leafModulations hQ hG d).measurable.comp measurable_snd)
      have hscalar := (hR c.2).comp_measurable hscalarMap
      exact (hcoef.mul hscalar).measurable
    · simp only [hc,ite_false]
      exact measurable_const
  have hp : Measurable (fun q : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      (q.2.1,(q.1,q.2.2))) := measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  exact (hm.comp hp).stronglyMeasurable

end WaveTurbulence.RegAsymp
