/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.TreeRootSpectralFamily
public import WaveTurbulence.Foundations.Incoh.SmoothModulatedDerivative
public import WaveTurbulence.Foundations.Incoh.CountableSliceMeasurability

/-! Ported by source from C2-B-TOP `C2BTop.RootJets` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Measurability of the root-modulated amplitude jets

The source amplitudes of C2-B-REG have the form `ψ(k) · c(ξ) · e(⟨v(ξ), k⟩)` on each countable
cell.  Multiplying by the root character `e(⟨Ξ(a), k⟩)` only shifts the frequency to `v(ξ) + Ξ(a)`, so
the jets are a continuous function of `(ξ, Ξ(a))` on each cell; this gives the joint strong
measurability on the product of the spectral and presentation parameters. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh

/-- Generic jets measurability for root-modulated smooth modulations on countable cells. -/
theorem stronglyMeasurable_rootChar_modulated_jets {d : ℕ} {I X α : Type*}
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace α]
    (ψ : I → Mom d → ℂ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (c : I → X → ℂ) (hc : ∀ i, Continuous (c i))
    (v : X → Mom d) (hv : Continuous v) (Ξ : α → Mom d) (hΞ : Measurable Ξ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : (I × X) × α => iteratedFDeriv ℝ j
      (fun k => rootChar (Ξ u.2) k * (ψ u.1.1 k * (c u.1.1 u.1.2 *
        (Real.fourierChar (inner ℝ (v u.1.2) k) : ℂ)))) k) := by
  let Ψ : I → X × Mom d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Mom d) ℂ := fun i (x : X × Mom d) =>
    iteratedFDeriv ℝ j (fun k => ψ i k * (c i x.1 *
      (Real.fourierChar (inner ℝ (v x.1 + x.2) k) : ℂ))) k
  have hΨ : StronglyMeasurable (Function.uncurry Ψ) :=
    stronglyMeasurable_countable_slices Ψ (fun i => continuous_iteratedFDeriv_smooth_modulated (ψ i)
      (hψ i) (fun x : X × Mom d => c i x.1) ((hc i).comp continuous_fst)
      (fun x : X × Mom d => v x.1 + x.2)
      ((hv.comp continuous_fst).add continuous_snd) k j)
  have he : (fun u : (I × X) × α => iteratedFDeriv ℝ j
      (fun k => rootChar (Ξ u.2) k * (ψ u.1.1 k * (c u.1.1 u.1.2 *
        (Real.fourierChar (inner ℝ (v u.1.2) k) : ℂ)))) k) =
      fun u => Function.uncurry Ψ (u.1.1, (u.1.2, Ξ u.2)) := by
    funext u
    simp only [Function.uncurry_apply_pair, Ψ]
    congr 1
    funext k
    simp only [rootChar, inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  rw [he]
  exact hΨ.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk (hΞ.comp measurable_snd)))

/-- Couple amplitudes: the root-modulated masked jets are jointly strongly measurable. -/
theorem stronglyMeasurable_rootMaskedJets {d n m w K M : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {Ξ : α → Mom d} (hΞ : Measurable Ξ) {B : ℝ} (hK : d + 1 ≤ K) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (Ξ u.2) k *
        (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1) k) := by
  have he (u : (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) × α) :
      (fun k => rootChar (Ξ u.2) k * (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u.1) =
        fun k => rootChar (Ξ u.2) k * (sourceRootMask u.1.1.1 k *
          ((MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f u.1.1.1 u.1.1.2.val 0 u.1.2 *
            (Real.fourierChar (inner ℝ (P.spectralShift u.1.2 none) k) : ℂ))) := by
    funext k
    simp only [MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial,
      MomentumTreeData.maskedSourceSpectralAmplitudeSpatial,
      MomentumTreeData.sourceSpectralAmplitudeSpatial, inner_zero_right, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one]
    ring
  simp_rw [he]
  exact stronglyMeasurable_rootChar_modulated_jets (fun c : SourceCellIndex S => sourceRootMask c.1)
    (fun c => contDiff_sourceRootMask c.1)
    (fun c ξ => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P)) ζ f c.1 c.2.val 0 ξ)
    (fun c => (MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P)) ζ f c.1 c.2.val hK hB h 0)
    (fun ξ => P.spectralShift ξ none) ((MomentumTreeData.continuous_spectralShiftSpatial (P := P)) none) Ξ hΞ k j

/-- Tree amplitudes: the root-modulated single-root jets are jointly strongly measurable. -/
theorem stronglyMeasurable_rootTreeJets {d n m w K M : ℕ} {α : Type*}
    [MeasurableSpace α] (P : MomentumTreeData n m w) (ζ : Circle) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m + 1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {Ξ : α → Mom d} (hΞ : Measurable Ξ) {B : ℝ} (hK : d + 1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (Ξ u.2) k *
        (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u.1) k) := by
  obtain ⟨Bq, hBq, hq⟩ := exists_spatialNorm_bound_appendRootPartitionSpatial f hf q
  let f' := appendRootInputSpatial f (treeRootPartitionSpatial q)
  have he (u : (SourceCellIndex S × (LocalizedCellIndex n (m + 1) → Fin d → ℝ)) × α) :
      (fun k => rootChar (Ξ u.2) k * (MomentumTreeData.treeRootSpectralAmplitudeSpatial (P := P)) ζ f S q k u.1) =
        fun k => rootChar (Ξ u.2) k * ((treeRootCutoffSpatial q k * sourceRootMask u.1.1.1 k) *
          ((MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P.withRootInput)) ζ f' u.1.1.1 u.1.1.2.val 0 u.1.2 *
            (Real.fourierChar (inner ℝ (P.withRootInput.spectralShift u.1.2 none) k) : ℂ))) := by
    funext k
    simp only [MomentumTreeData.treeRootSpectralAmplitudeSpatial,
      MomentumTreeData.rootCutoffSpectralAmplitudeSpatial,
      MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial,
      MomentumTreeData.maskedSourceSpectralAmplitudeSpatial,
      MomentumTreeData.sourceSpectralAmplitudeSpatial, inner_zero_right, AddChar.map_zero_eq_one,
      Circle.coe_one, mul_one, f']
    ring
  simp_rw [he]
  exact stronglyMeasurable_rootChar_modulated_jets
    (fun c : SourceCellIndex S => fun k => treeRootCutoffSpatial q k * sourceRootMask c.1 k)
    (fun c => (contDiff_treeRootCutoffSpatial q).mul (contDiff_sourceRootMask c.1))
    (fun c ξ => (MomentumTreeData.sourceSpectralAmplitudeSpatial (P := P.withRootInput)) ζ f' c.1 c.2.val 0 ξ)
    (fun c => (MomentumTreeData.continuous_sourceSpectralAmplitudeSpatial (P := P.withRootInput)) ζ f' c.1 c.2.val hK hBq.le hq 0)
    (fun ξ => P.withRootInput.spectralShift ξ none) ((MomentumTreeData.continuous_spectralShiftSpatial (P := P.withRootInput)) none)
    Ξ hΞ k j

end WaveTurbulence.Flower.IncTop