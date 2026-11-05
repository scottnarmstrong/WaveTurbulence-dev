/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootScalarIntegrability

/-! # Original tree leaf moments supply the actual countable singular-mixture mass -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst

/-- The actual moving-root spectral coefficient after removing its single added moment. -/
def treeRootSingularCoefficient {d : ℕ} {G : Garden 1} {X : RegChain} (_hX : X.DecodesTree G)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (c : SourceCellIndex S) (α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) : ℂ :=
  rootAmplitudeSum (treeRootLeafAmplitude f S) k (c,α)/(treeLeafModulationWeight α:ℂ)

/-- Actual zero-order derivative measurability gives joint measurability of this coefficient. -/
theorem stronglyMeasurable_treeRootSingularCoefficient {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B : ℝ}
    (hK : d+1 ≤ K) (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) (k : Mom d) :
    StronglyMeasurable (Function.uncurry (treeRootSingularCoefficient hX f S k)) := by
  have hw : StronglyMeasurable (fun p : SourceCellIndex S ×
      (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) => (treeLeafModulationWeight p.2:ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_treeLeafModulationWeight).stronglyMeasurable.comp_measurable measurable_snd
  exact (stronglyMeasurable_rootAmplitudeSum_treeRootLeaf f hK hf S k).div hw

/-- The original C2 row bound pays the single first modulation moment, at every counted cell. -/
theorem treeRootSingularCoefficient_moment_le {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) (k : Mom d)
    (c : SourceCellIndex S) (α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) :
    ‖treeRootSingularCoefficient hX f S k c α‖*
      (1+((∑ j, ‖(treeLeafModulations hX α).1 j‖)+(∑ j, ‖(treeLeafModulations hX α).2 j‖))) ≤
      treeSpectralFrequencyLoss X (G.sig 0)*‖rootAmplitudeSum (treeRootLeafAmplitude f S) k (c,α)‖ := by
  have hw := treeLeafModulationWeight_pos α
  have hb := tree_leaf_modulation_weight_le hX α
  change 1+((∑ j, ‖(treeLeafModulations hX α).1 j‖)+
    (∑ j, ‖(treeLeafModulations hX α).2 j‖)) ≤
      treeSpectralFrequencyLoss X (G.sig 0)*treeLeafModulationWeight α at hb
  rw [treeRootSingularCoefficient,norm_div,Complex.norm_real,Real.norm_of_nonneg hw.le]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hw.le)).trans_eq
  field_simp

/-- The original input norms give global counted first-moment integrability, before
any source singular operator or recursion is applied. -/
theorem integrable_treeRootSingularCoefficient_moment {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    Integrable (fun p : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) =>
      ‖treeRootSingularCoefficient hX f S k p.1 p.2‖ *
        (1+((∑ j, ‖(treeLeafModulations hX p.2).1 j‖)+(∑ j, ‖(treeLeafModulations hX p.2).2 j‖))))
          (treeLeafCellMeasure S) := by
  have hiA : Integrable (rootAmplitudeSum (treeRootLeafAmplitude f S) k) (treeLeafCellMeasure S) := by
    simpa only [mul_one] using integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar (D := 1) f hK hM hB hf S hS
      (fun _ => (1:ℂ)) stronglyMeasurable_const (fun _ => by simp) k
  have hc : Continuous (fun α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ =>
      1+((∑ j, ‖(treeLeafModulations hX α).1 j‖)+(∑ j, ‖(treeLeafModulations hX α).2 j‖))) := by
    apply continuous_const.add
    apply Continuous.add
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp (continuous_treeLeafModulations (d := d) hX).fst).norm
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp (continuous_treeLeafModulations (d := d) hX).snd).norm
  have hm := (stronglyMeasurable_treeRootSingularCoefficient hX f (by omega) hf S k).norm.mul
    (hc.stronglyMeasurable.comp_measurable measurable_snd)
  apply (hiA.norm.const_mul (treeSpectralFrequencyLoss X (G.sig 0))).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro p
  have hp : 0 ≤ ‖treeRootSingularCoefficient hX f S k p.1 p.2‖ *
      (1+((∑ j, ‖(treeLeafModulations hX p.2).1 j‖)+(∑ j, ‖(treeLeafModulations hX p.2).2 j‖))) := by
    positivity
  exact (Real.norm_of_nonneg hp).trans_le (treeRootSingularCoefficient_moment_le hX f S k p.1 p.2)

end WaveTurbulence.RegAsymp
