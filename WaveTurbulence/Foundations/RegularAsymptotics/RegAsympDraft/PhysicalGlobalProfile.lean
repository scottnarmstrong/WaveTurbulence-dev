/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceProfileCounting
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalDensityDecomposition
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalCellSymbols
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalCellLocalization

/-! # Global recombination of the original integrable source profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ClassJR Set

/-- Integrable original scalar source densities recombine over exactly
the original selected cells, with finite source-profile summation justified
by joint L1 rather than a formal interchange. -/
theorem masked_source_profiles_recombine {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} {I : Type*} [Fintype I]
    (R : I → (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (v : I → ℂ) (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hi : ∀ i, Integrable (fun q => maskedLeafScalarDensity hQ hG (R i) F S q k)
      (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))))
    (t : Fin 2 → ℝ) :
    (∑' u : SourceCellIndex S, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      sourceRootMask u.1 k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
          ∑ i, v i*pairedInverseProfile (fun lam => R i lam
            (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 u.2.val) t)) =
    ∑ i, v i*pairedInverseProfile (fun lam => ∫ p,
      maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k
        ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t := by
  classical
  let μ := leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let : SFinite (leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) := by
    unfold leafSpatialMeasure
    infer_instance
  let f := fun p : LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
    ∑ i, v i*pairedInverseProfile (fun lam => maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k) t
  have hif : Integrable f μ := integrable_finsetSum _ (fun i _ =>
    (integrable_pairedInverseProfile_samples μ (hi i) t).const_mul (v i))
  have hsupport : ∀ c z, z ∉ S c → ∀ α, f ((c,z),α) = 0 := by
    intro c z hz α
    simp only [f,pairedInverseProfile_maskedLeafScalarDensity,hz,ite_false,mul_zero,Finset.sum_const_zero]
  have hc := leafSpatial_integral_eq_sourceCellIndex S f hif hsupport
  have hpoint (u : SourceCellIndex S) (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
      f ((u.1,u.2.val),α) = sourceRootMask u.1 k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
          ∑ i, v i*pairedInverseProfile (fun lam => R i lam
            (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 u.2.val) t) := by
    simp only [f,pairedInverseProfile_maskedLeafScalarDensity,u.2.property,ite_true]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint] at hc
  rw [← hc]
  change (∫ p, ∑ i, v i*pairedInverseProfile (fun lam =>
    maskedLeafScalarDensity hQ hG (R i) F S (lam,p) k) t ∂μ) = _
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_pairedInverseProfile_samples μ (hi i) t).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,← pairedInverseProfile_integral_swap μ (hi i) t]

end WaveTurbulence.RegAsymp
