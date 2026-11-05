/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialMeasure
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafLocalDensity
public import WaveTurbulence.Foundations.RegAsymp.SpectralProfileMajorant

/-! # A common spectral integral for all localized couple remainders -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal

/-- Restrict the link center to the actual root-uniform finite cell cover. -/
def leafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (lam : ℝ × ℝ) (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) : ℂ :=
  if p.1.2 ∈ S p.1.1 then leafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 k lam p.2 else 0

/-- Joint measurability includes both countable localization arrays and all frequencies. -/
theorem stronglyMeasurable_leafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      leafSpatialRemainderDensity hQ hG L δ γ J C F S p.1 p.2 k) := by
  classical
  have hm : Measurable (fun p :
      ((Fin (2*Q.links.length+1) → Fin d → ℤ) × ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) ×
        ((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) =>
      if p.1.2 ∈ S p.1.1 then leafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 k p.2.1 p.2.2 else 0) := by
    apply measurable_from_prod_countable_right
    intro c
    dsimp only
    by_cases hc : c.2 ∈ S c.1
    · simp only [hc,ite_true]
      exact (stronglyMeasurable_leafLocalDensity hQ hG hd hn L δ γ J hC hK hB hF c.1 c.2 k).measurable
    · simp only [hc,ite_false]
      exact measurable_const
  have hmap : Measurable (fun p : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      (p.2.1,(p.1,p.2.2))) := measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  have hh := hm.stronglyMeasurable.comp_measurable hmap
  exact hh

/-- The common spatial sample measure is σ-finite. -/
theorem sFinite_leafSpatialMeasure (d n m : ℕ) : SFinite (leafSpatialMeasure d n m) := by
  unfold leafSpatialMeasure
  infer_instance

/-- The summed spectral frequency density is measurable in λ for every root. -/
theorem stronglyMeasurable_integral_leafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) :
    StronglyMeasurable (fun lam => ∫ p, leafSpatialRemainderDensity hQ hG L δ γ J C F S lam p k
      ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
  have := sFinite_leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  exact (stronglyMeasurable_leafSpatialRemainderDensity hQ hG hd hn L δ γ J hC hK hB hF S k).integral_prod_right'

end WaveTurbulence.RegAsymp
