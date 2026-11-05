/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpectralCoefficient
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalRemainderJoint

/-! # The actual leaf-only spectral remainder density -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal

/-- The two link modulation arrays computed from the actual leaf rows. -/
def leafModulations {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    (Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d) :=
  ((fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0))),
    (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))))

theorem continuous_leafModulations {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (d : ℕ) :
    Continuous (leafModulations hQ hG (d := d)) := by
  have hc : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      fun a => toLp 2 (α a)) := by fun_prop
  exact (continuous_pi (fun j => (continuous_sourceFrequencyPullback hQ hG (some (j,0))).comp hc)).prodMk
    (continuous_pi (fun j => (continuous_sourceFrequencyPullback hQ hG (some (j,1))).comp hc))

/-- A literal spectral density, with the root character and all input transforms retained. -/
def leafLocalDensity {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (k : Mom d)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) : ℂ :=
  (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) * leafSpectrumCoefficient F c α *
    localRemainder L δ γ J C (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 lam z

/-- The literal remainder remains jointly measurable after the actual row pullback. -/
theorem stronglyMeasurable_leafModulatedRemainder {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : ClassJR.SymReg C)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      localRemainder L δ γ J C (leafModulations hQ hG p.2).1 (leafModulations hQ hG p.2).2 p.1 z) := by
  have hr := stronglyMeasurable_localRemainder_joint hd hn L δ γ J hC.meas z
  have hmap : Measurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      (p.1,leafModulations hQ hG p.2)) :=
    measurable_fst.prodMk ((continuous_leafModulations hQ hG d).measurable.comp measurable_snd)
  have hh := hr.comp_measurable hmap
  exact hh

/-- The root character is a continuous unit-modulus factor. -/
theorem continuous_leafRootCharacter {d m : ℕ} (k : Mom d) :
    Continuous (fun α : Fin m → Fin d → ℝ =>
      (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ)) := by
  fun_prop

/-- The actual spatial and temporal frequency integrals have a jointly measurable density. -/
theorem stronglyMeasurable_leafLocalDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    {C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : ClassJR.SymReg C) {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (k : Mom d) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      leafLocalDensity hQ hG L δ γ J C F c z k p.1 p.2) := by
  have hr' := stronglyMeasurable_leafModulatedRemainder hQ hG hd hn L δ γ J hC z
  have hcoef := stronglyMeasurable_leafSpectrumCoefficient (m := 2*Q.links.length+1) hK hB hF
  have hcoefMap : Measurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
      (c,p.2)) := measurable_const.prodMk measurable_snd
  have hc := hcoef.comp_measurable hcoefMap
  have hp := (continuous_leafRootCharacter (m := 2*Q.links.length+1) k).stronglyMeasurable.comp_measurable
    (measurable_snd : Measurable (Prod.snd : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) → _))
  change StronglyMeasurable (fun p : (ℝ × ℝ) × (Fin (2*Q.links.length+1) → Fin d → ℝ) =>
    (Real.fourierChar (inner ℝ (∑ a, toLp 2 (p.2 a)) k) : ℂ) * leafSpectrumCoefficient F c p.2 *
      localRemainder L δ γ J C (leafModulations hQ hG p.2).1 (leafModulations hQ hG p.2).2 p.1 z)
  have hpc := hp.mul hc
  have hall := hpc.mul hr'
  exact hall

/-- The common local remainder envelope is paid by precisely one actual
leaf-frequency moment, independently of root momentum. -/
theorem norm_leafLocalDensity_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ}
    (L δ γ : ℝ) (J : Finset (Fin Q.links.length))
    (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (F : Fin (2*Q.links.length+1) → Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (k : Mom d)
    (lam : ℝ × ℝ) (α : Fin (2*Q.links.length+1) → Fin d → ℝ)
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ β γ', ‖localRemainder L δ γ J C β γ' lam z‖ ≤
      ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*R)*B) :
    ‖leafLocalDensity hQ hG L δ γ J C F c z k lam α‖ ≤
      ((1+2*Real.pi)*R*spectralFrequencyLoss Q)*
        ((1+∑ a, ‖toLp 2 (α a)‖)*‖leafSpectrumCoefficient F c α‖)*B := by
  unfold leafLocalDensity
  rw [norm_mul,norm_mul,Circle.norm_coe,one_mul]
  have hh := mul_le_mul_of_nonneg_left
    (hb (leafModulations hQ hG α).1 (leafModulations hQ hG α).2)
    (norm_nonneg (leafSpectrumCoefficient F c α))
  apply hh.trans
  have hw := leaf_modulation_weight_le hQ hG α
  have hs : 0 ≤ (1+2*Real.pi)*R*‖leafSpectrumCoefficient F c α‖*B := by positivity
  have hm := mul_le_mul_of_nonneg_left hw hs
  simpa only [leafModulations,mul_assoc,mul_left_comm,mul_comm] using hm

end WaveTurbulence.RA1Leafwise
