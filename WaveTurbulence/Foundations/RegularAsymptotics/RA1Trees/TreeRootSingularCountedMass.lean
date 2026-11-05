/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootSingularMoments

/-! # Actual counted first-moment fields for the tree singular-mixture interface -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst

/-- The original source norms give each counted first-moment L1 field and summable
actual masses, exactly the interface of countable half-cell singular Fubini. -/
theorem treeRootSingularCoefficient_countable_moments {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    (∀ c : SourceCellIndex S,
      Integrable (fun α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ =>
        ‖treeRootSingularCoefficient hX f S k c α‖ *
          (1+((∑ j, ‖(treeLeafModulations hX α).1 j‖)+(∑ j, ‖(treeLeafModulations hX α).2 j‖))))) ∧
      Summable (fun c : SourceCellIndex S =>
        ∫ α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ,
          ‖treeRootSingularCoefficient hX f S k c α‖ *
            (1+((∑ j, ‖(treeLeafModulations hX α).1 j‖)+(∑ j, ‖(treeLeafModulations hX α).2 j‖)))) := by
  have hi := integrable_treeRootSingularCoefficient_moment hX f hK hM hB hf S hS k
  rw [treeLeafCellMeasure] at hi
  refine ⟨Measure.ae_count_iff.mp ((integrable_prod_iff hi.aestronglyMeasurable).mp hi).1,?_⟩
  exact (integrable_count_iff.mp hi.integral_prod_left).of_norm

end WaveTurbulence.RegAsymp
