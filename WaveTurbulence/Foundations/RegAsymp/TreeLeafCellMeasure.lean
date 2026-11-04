/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeafProfiles
public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure

/-! # The selected tree link cells with leaf-only Fourier frequencies

The same finite geometric cover is counted once for each actual leaf-center array.
Link cutoffs remain in physical space, so no link-frequency moments enter this measure.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh
open scoped ENNReal

/-- The actual selected cells, with only independent leaf Fourier variables. -/
def treeLeafCellMeasure {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    Measure (SourceCellIndex S × (Fin m → Fin d → ℝ)) := Measure.count.prod volume

instance {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ)) :
    SigmaFinite (treeLeafCellMeasure S) := by unfold treeLeafCellMeasure; infer_instance

/-- Each actual moment envelope is continuous in all independent leaf frequencies. -/
theorem continuous_treeLeafMomentEnvelope {d m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (c : Fin m → Fin d → ℤ) : Continuous (treeLeafMomentEnvelope J f c) := by
  unfold treeLeafMomentEnvelope
  simp_rw [← ApproxNT.enorm_finset_prod]
  apply Continuous.enorm
  apply continuous_finsetProd
  intro a _
  exact ((continuous_spectralMomentProfile (n := 0) J (fun _ : Fin 1 => f a)
    (fun _ : Fin 1 => c a) hK hB (fun _ => hf a) (.inl 0)).comp (continuous_apply a))

/-- Literal finite-fiber multiplicity for any nonnegative measurable leaf density. -/
theorem lintegral_treeLeafCellMeasure {d n m : ℕ}
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (E : (Fin m → Fin d → ℤ) → (Fin m → Fin d → ℝ) → ℝ≥0∞)
    (hE : ∀ c, Measurable (E c)) :
    (∫⁻ u, E u.1.1 u.2 ∂treeLeafCellMeasure S) =
      ∑' c : Fin m → Fin d → ℤ, (S c).card * ∫⁻ α, E c α := by
  have hm : Measurable (fun u : SourceCellIndex S × (Fin m → Fin d → ℝ) => E u.1.1 u.2) :=
    measurable_from_prod_countable_right (fun u => hE u.1)
  rw [treeLeafCellMeasure, lintegral_prod _ hm.aemeasurable, lintegral_count]
  exact tsum_sourceCellIndex S (fun c => ∫⁻ α, E c α)

/-- The source finite cover pays exactly its geometric multiplicity; the individual leaf
moment totals have not been replaced by translated spatial norms. -/
theorem lintegral_treeLeafCellMoment_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B C : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n) :
    (∫⁻ u, treeLeafMomentEnvelope J f u.1.1 u.2 ∂treeLeafCellMeasure S) ≤
      ENNReal.ofReal (C^n) * ∏ a, leafFourierMomentTotal J (f a) := by
  rw [lintegral_treeLeafCellMeasure S _ (fun c =>
    (continuous_treeLeafMomentEnvelope J f hK hB hf c).measurable)]
  calc
    _ ≤ ∑' c : Fin m → Fin d → ℤ, ENNReal.ofReal (C^n) *
        ∫⁻ α, treeLeafMomentEnvelope J f c α := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply mul_le_mul' _ le_rfl
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hS c)
    _ = ENNReal.ofReal (C^n) * (∑' c : Fin m → Fin d → ℤ,
        ∫⁻ α, treeLeafMomentEnvelope J f c α) := ENNReal.tsum_mul_left
    _ = _ := by rw [tsum_lintegral_treeLeafMomentEnvelope J f hK hB hf]

/-- All selected cells and moving-root leaf frequencies have the same uniform geometric
moment mass. This is the actual mass required by the tree spatial mixture. -/
theorem lintegral_treeLeafCellMoment_root_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B C : ℝ} (hK : d+1+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n) (q : Fin d → ℤ) :
    (∫⁻ u, treeLeafMomentEnvelope J (appendRootInput f (treeRootPartition q)) u.1.1 u.2
      ∂treeLeafCellMeasure S) ≤ ENNReal.ofReal (C^n) *
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B)^(m+1) := by
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  exact (lintegral_treeLeafCellMoment_le J _ (by omega) hBq.le hq S hS).trans
    (mul_le_mul' le_rfl (prod_leafFourierMomentTotal_appendRootPartition_le J f hK hM hB hf q))

end WaveTurbulence.RegAsymp
