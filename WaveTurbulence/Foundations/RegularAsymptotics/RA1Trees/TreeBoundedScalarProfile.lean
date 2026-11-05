/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedLatticeScalar
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootScalarIntegrability

/-! # Actual bounded original lattice coefficients in the moving-root tree mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links

/-- The exact original lattice scalar normalized by the single leaf moment in the amplitude. -/
def treeBoundedScalar {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (L : ℝ)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) → ℂ :=
  treeNormalizedScalar hX (fun _ β γ z => treeHalfCellLatticeScalar L H z β γ) S (0,0)

/-- The actual scalar is strongly measurable jointly in all counted and Fourier variables. -/
theorem stronglyMeasurable_treeBoundedScalar {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 0 < L)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (treeBoundedScalar hX L H S) := by
  let R := fun (_ : ℝ × ℝ) β γ z => treeHalfCellLatticeScalar L H z β γ
  have hmR (z) : StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R p.1 p.2.1 p.2.2 z) :=
    (continuous_treeHalfCellLatticeScalar hL H z).stronglyMeasurable.comp_measurable measurable_snd
  exact (stronglyMeasurable_treeNormalizedScalar hX R hmR S).comp_measurable
    (g := fun u : SourceCellIndex S ×
      (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) => (((0,0):ℝ × ℝ),u))
    (measurable_const.prodMk measurable_id)

/-- No momentum frequency loss is needed to establish the original-kernel exchanges:
the actual localized lattice scalar is uniformly bounded before dividing by its leaf moment. -/
theorem treeBoundedScalar_norm_le {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hH : ∀ g, ‖H g‖ ≤ D)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    ‖treeBoundedScalar hX L H S u‖ ≤ (2^d*L^d)^(2*(X.treeLinks (G.sig 0)).length)*D := by
  rw [treeBoundedScalar,treeNormalizedScalar,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (treeLeafModulationWeight_pos u.2).le]
  apply (div_le_self (norm_nonneg _) ?_).trans
    (treeHalfCellLatticeScalar_norm_le hL H hD hH _ _ _)
  unfold treeLeafModulationWeight
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end WaveTurbulence.RegAsymp
