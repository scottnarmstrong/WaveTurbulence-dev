/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedLatticeScalar

/-! # The actual unintegrated half-cell scalar for continuum source recovery -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst

/-- The actual physical half-cell coefficient with the original one-moment normalization. -/
def treePointScalar {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    (SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) → ℂ :=
  treeNormalizedScalar hX (fun _ β γ z => halfCellAmplitude z β γ x y) S (0,0)

/-- Actual modulation continuity and countability supply strong measurability. -/
theorem stronglyMeasurable_treePointScalar {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    StronglyMeasurable (treePointScalar hX x y S) := by
  let R := fun (_ : ℝ × ℝ) β γ z => halfCellAmplitude z β γ x y
  have hmR (z) : StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R p.1 p.2.1 p.2.2 z) :=
    (continuous_halfCellAmplitude_joint z).stronglyMeasurable.comp_measurable
      (g := fun p : (ℝ × ℝ) × ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => (p.2,(x,y)))
      (measurable_snd.prodMk measurable_const)
  exact (stronglyMeasurable_treeNormalizedScalar hX R hmR S).comp_measurable
    (g := fun u : SourceCellIndex S ×
      (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) => (((0,0):ℝ × ℝ),u))
    (measurable_const.prodMk measurable_id)

/-- The retained original half cells have amplitude at most one. -/
theorem treePointScalar_norm_le_one {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    ‖treePointScalar hX x y S u‖ ≤ 1 := by
  rw [treePointScalar,treeNormalizedScalar,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (treeLeafModulationWeight_pos u.2).le]
  apply (div_le_self (norm_nonneg _) ?_).trans (tree_norm_halfCellAmplitude_le_one _ _ _ x y)
  unfold treeLeafModulationWeight
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end WaveTurbulence.RegAsymp
