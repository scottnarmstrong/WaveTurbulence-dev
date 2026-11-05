/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootScalarIntegrability
public import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Qualitative actual inverse-profile integrability for tree source recombination -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR

/-- A single integrable original-lambda majorant gives actual normalized inverse
profiles, uniformly in counted leaf cells and modulations. The assumptions are purely
qualitative and do not contain the desired RA1 spatial or time estimate. -/
theorem tree_normalized_inverseProfile_qualitative {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G)
    (R : (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R p.1 p.2.1 p.2.2 z))
    (E : (ℝ × ℝ) → ℝ) (hiE : Integrable E)
    (hbR : ∀ᵐ lam, ∀ z β γ, ‖R lam β γ z‖ ≤ E lam)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    (∀ u, Integrable (fun lam => treeNormalizedScalar hX R S lam u)) ∧
      (∀ t : Fin 2 → ℝ, StronglyMeasurable (fun u =>
        pairedInverseProfile (fun lam => treeNormalizedScalar hX R S lam u) t)) ∧
      ∀ (t : Fin 2 → ℝ) u,
        ‖pairedInverseProfile (fun lam => treeNormalizedScalar hX R S lam u) t‖ ≤ ∫ lam, E lam := by
  have hmA := stronglyMeasurable_treeNormalizedScalar hX R hR S
  have hb (u) : ∀ᵐ lam, ‖treeNormalizedScalar hX R S lam u‖ ≤ E lam := by
    filter_upwards [hbR] with lam hlam
    rw [treeNormalizedScalar,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (treeLeafModulationWeight_pos u.2).le]
    apply (div_le_self (norm_nonneg _) ?_).trans (hlam _ _ _)
    unfold treeLeafModulationWeight
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hi (u) : Integrable (fun lam => treeNormalizedScalar hX R S lam u) :=
    hiE.mono' (hmA.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable (hb u)
  refine ⟨hi,?_,?_⟩
  · intro t
    have he : StronglyMeasurable (fun p : (ℝ × ℝ) ×
        (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) =>
          e2 p.1 (t 0) (t 1)) :=
      (show Continuous (fun lam : ℝ × ℝ => e2 lam (t 0) (t 1)) by
        unfold e2; fun_prop).stronglyMeasurable.comp_measurable measurable_fst
    exact (hmA.mul he).integral_prod_left'
  · intro t u
    apply norm_integral_le_of_norm_le hiE
    filter_upwards [hb u] with lam hlam
    rw [norm_mul,norm_e2,mul_one]
    exact hlam

end WaveTurbulence.RegAsymp
