/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralSpatialMixture
public import WaveTurbulence.Foundations.RegAsymp.PairedCutoffCharacter
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRegularity
import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Full spatial restriction bounds for actual source-frequency mixtures -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR Incoh WaveTurbulence.Fourier
open scoped ContDiff ENNReal

/-- The actual inverse source profile has a full spatial restriction bound.
All momentum suprema stay inside time-frequency integration, and the
extension satisfies the landed almost-everywhere spatial regularity guard. -/
theorem mixedRestrictionNorm_paired_spatialMixture_le {d N W : ℕ} {U : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] {η : ℝ} (hη : 0 ≤ η)
    (A : Mom d → (ℝ × ℝ) × U → ℂ) (v : (ℝ × ℝ) × U → ℝ)
    (hA : ∀ q, ContDiff ℝ N (fun k => A k q))
    (hA0 : ∀ k, StronglyMeasurable (A k))
    (hmeas : ∀ j ≤ N, ∀ k, AEStronglyMeasurable
      (fun q => iteratedFDeriv ℝ j (fun k => A k q) k) (volume.prod μ))
    (hv : Integrable v (volume.prod μ)) (hvm : Measurable v) (hvn : ∀ q, 0 ≤ v q)
    (hb : ∀ j ≤ N, ∀ k q, momentumBracket k^W *
      ‖iteratedFDeriv ℝ j (fun k => A k q) k‖ ≤ v q)
    {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) :
    mixedRestrictionNorm η N W T Set.univ
      (fun t k => pairedInverseProfile (fun lam => ∫ u, A k.val (lam,u) ∂μ) t.val) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (∫⁻ q, wL η q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) := by
  let ν : Measure ((ℝ × ℝ) × U) := volume.prod μ
  have hnorm (k : Mom d) (q : (ℝ × ℝ) × U) : ‖A k q‖ ≤ v q := by
    have h0 := hb 0 (Nat.zero_le N) k q
    rw [norm_iteratedFDeriv_zero] at h0
    exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (one_le_momentumBracket k))).trans h0
  have hiA (k : Mom d) : Integrable (A k) ν :=
    hv.mono' (hA0 k).aestronglyMeasurable (ae_of_all _ (hnorm k))
  have hK : StronglyMeasurable (fun p : (Fin 2 → ℝ) × ((ℝ × ℝ) × U) =>
      pairedCutoffCharacter p.2.1 p.1) :=
    continuous_pairedCutoffCharacter.stronglyMeasurable.comp_measurable
      (g := fun p : (Fin 2 → ℝ) × ((ℝ × ℝ) × U) => (p.1, p.2.1))
      (measurable_fst.prodMk measurable_snd.fst)
  have hjoint (k : Mom d) : Integrable (fun p : (Fin 2 → ℝ) × ((ℝ × ℝ) × U) =>
      A k p.2 * pairedCutoffCharacter p.2.1 p.1) (volume.prod ν) := by
    have hd := integrable_unitSquareCutoff.norm.mul_prod hv
    have hm := ((hA0 k).comp_measurable measurable_snd).mul hK
    apply hd.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro p
    change ‖A k p.2 * pairedCutoffCharacter p.2.1 p.1‖ ≤ ‖unitSquareCutoff p.1‖ * v p.2
    rw [norm_mul,norm_pairedCutoffCharacter]
    exact (mul_le_mul_of_nonneg_right (hnorm k p.2) (norm_nonneg _)).trans_eq (mul_comm _ _)
  let F := fun (t : Fin 2 → ℝ) (k : Mom d) =>
    ∫ q, A k q * pairedCutoffCharacter q.1 t ∂ν
  have hagree (t : T) (k : (Set.univ : Set (Mom d))) :
      F t.val k.val = pairedInverseProfile (fun lam => ∫ u, A k.val (lam,u) ∂μ) t.val := by
    have hE : StronglyMeasurable (fun q : (ℝ × ℝ) × U => e2 q.1 (t.val 0) (t.val 1)) :=
      (show Continuous (fun lam : ℝ × ℝ => e2 lam (t.val 0) (t.val 1)) by
        unfold e2; fun_prop).stronglyMeasurable.comp_measurable measurable_fst
    have hiE := (hiA k.val).mul_bdd (c := 1) hE.aestronglyMeasurable
      (ae_of_all _ (fun q => (norm_e2 q.1 (t.val 0) (t.val 1)).le))
    dsimp only [F,pairedCutoffCharacter]
    simp only [unitSquareCutoff_eq_one (hT t.val t.property),one_mul]
    rw [integral_prod _ hiE]
    simp only [pairedInverseProfile,integral_mul_const]
  apply (mixedRestrictionNorm_le_extension F hagree).trans
  have hbound := mixedFourierNorm_spectralMixture_le ν η A v
    (fun t q => pairedCutoffCharacter q.1 t) hA hmeas hv hvm hvn hb hK
    (fun q => integrable_pairedCutoffCharacter q.1) hjoint
    (H := ENNReal.ofReal (∫ t, ‖unitSquareCutoff t‖)) ENNReal.ofReal_lt_top
    (fun q => (eLpNorm_pairedCutoffCharacter_one q.1).le)
  apply hbound.trans
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal (v q)*
        (ENNReal.ofReal (2^η)*wL η q.1*timeFourierNorm η unitSquareCutoff) ∂ν :=
      lintegral_mono (fun q => mul_le_mul' le_rfl (timeFourierNorm_pairedCutoffCharacter_le hη q.1))
    _ = ∫⁻ q, (ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff)*
        (wL η q.1*ENNReal.ofReal (v q)) ∂ν := by
      apply lintegral_congr
      intro q
      ac_rfl
    _ = _ := lintegral_const_mul _
      (((measurable_wL η).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hvm))

end WaveTurbulence.RegAsymp
