/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MaskedLeafDerivativeMeasurable
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpatialRemainder

/-! # The full actual spatial sample density with root derivatives -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ContDiff ENNReal

/-- Retain the actual finite link cover and the mask chosen before Fourier inversion. -/
def maskedLeafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (lam : ℝ × ℝ) (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) : ℂ :=
  if p.1.2 ∈ S p.1.1 then maskedLeafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 lam p.2 k else 0

section
variable {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))

/-- The new density inserts precisely the source root mask, without altering the finite cover. -/
theorem maskedLeafSpatialRemainderDensity_eq_mask_mul (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) :
    maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p k =
      sourceRootMask p.1.1 k * leafSpatialRemainderDensity hQ hG L δ γ J C F S lam p k := by
  classical
  by_cases h : p.1.2 ∈ S p.1.1 <;>
    simp only [maskedLeafSpatialRemainderDensity,leafSpatialRemainderDensity,h,ite_true,ite_false,
      maskedLeafLocalDensity,mul_zero]

/-- The fixed cover indicator selects whole smooth root functions. -/
theorem maskedLeafSpatialRemainderDensity_eq_function (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p =
      if p.1.2 ∈ S p.1.1 then maskedLeafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 lam p.2 else 0 := by
  classical
  funext k
  by_cases h : p.1.2 ∈ S p.1.1 <;> simp [maskedLeafSpatialRemainderDensity,h]

/-- Every actual sample amplitude is smooth in root momentum. -/
theorem contDiff_maskedLeafSpatialRemainderDensity (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) :
    ContDiff ℝ ∞ (maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p) := by
  classical
  rw [maskedLeafSpatialRemainderDensity_eq_function]
  by_cases h : p.1.2 ∈ S p.1.1
  · simp only [h,ite_true]
    exact contDiff_maskedLeafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 lam p.2
  · simp only [h,ite_false]
    exact contDiff_const

/-- Derivatives keep the same actual finite-cover indicator. -/
theorem derivative_maskedLeafSpatialRemainderDensity (lam : ℝ × ℝ)
    (p : LeafSpatialSample d Q.links.length (2*Q.links.length+1)) (k : Mom d) (j : ℕ) :
    iteratedFDeriv ℝ j (maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p) k =
      if p.1.2 ∈ S p.1.1 then
        iteratedFDeriv ℝ j (maskedLeafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 lam p.2) k else 0 := by
  classical
  rw [maskedLeafSpatialRemainderDensity_eq_function]
  by_cases h : p.1.2 ∈ S p.1.1 <;> simp [h]
end

/-- Joint measurability covers every countable localization center and
all time/leaf frequencies, with the literal derivative tensor retained. -/
theorem stronglyMeasurable_derivative_maskedLeafSpatialRemainderDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      iteratedFDeriv ℝ j (maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S p.1 p.2) k) := by
  classical
  have hm : StronglyMeasurable (fun p :
      ((Fin (2*Q.links.length+1) → Fin d → ℤ) × ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) ×
      ((ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) =>
      if p.1.2 ∈ S p.1.1 then
        iteratedFDeriv ℝ j (maskedLeafLocalDensity hQ hG L δ γ J C F p.1.1 p.1.2 p.2.1 p.2.2) k else 0) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (c : (Fin (2*Q.links.length+1) → Fin d → ℤ) ×
          ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
        (q : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ)) =>
        if c.2 ∈ S c.1 then
          iteratedFDeriv ℝ j (maskedLeafLocalDensity hQ hG L δ γ J C F c.1 c.2 q.1 q.2) k else 0)
    · intro _
      exact continuous_of_discreteTopology
    intro c
    by_cases hc : c.2 ∈ S c.1
    · simp only [hc,ite_true]
      exact (stronglyMeasurable_derivative_maskedLeafLocalDensity hQ hG hd hn L δ γ J hC hK hB hF c.1 c.2 k j)
    · simp only [hc,ite_false]
      exact stronglyMeasurable_const
  have hmap : Measurable (fun p : (ℝ × ℝ) × LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      (p.2.1,(p.1,p.2.2))) := measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd)
  simp_rw [derivative_maskedLeafSpatialRemainderDensity]
  exact hm.comp_measurable hmap

end WaveTurbulence.RegAsymp
