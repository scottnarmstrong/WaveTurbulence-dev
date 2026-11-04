/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeRootLeafAmplitude
public import WaveTurbulence.Foundations.RegAsymp.TreeLeafCellMeasure

/-! # Actual moving-root leaf amplitudes with uniform counted derivative mass -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal ContDiff

/-- The exact leaf-only amplitude used by the tree root-localized NT mixture. -/
def treeRootLeafAmplitude {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) : ℂ :=
  treeRootLeafModulation q u.1.1
    (treeLeafSpectrum (appendRootInput f (treeRootPartition q)) u.1.1 u.2)
    (fun a => toLp 2 (u.2 a)) k

/-- The actual common derivative envelope, with the one extra NT frequency moment. -/
def treeRootLeafEnvelope {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) : ℝ :=
  treeRootLeafDerivativeConstant d J *
    (treeLeafMomentEnvelope (J+1) (appendRootInput f (treeRootPartition q)) u.1.1 u.2).toReal

theorem treeRootLeafEnvelope_nonneg {d n m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) :
    0 ≤ treeRootLeafEnvelope J f S q u :=
  mul_nonneg (treeRootLeafDerivativeConstant_nonneg _ _) ENNReal.toReal_nonneg

theorem contDiff_treeRootLeafAmplitude {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) :
    ContDiff ℝ ∞ (fun k => treeRootLeafAmplitude f S q k u) := contDiff_treeRootLeafModulation _ _ _ _

theorem treeRootLeafAmplitude_eq_zero {d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ))
    (hk : treeRootCutoff q k = 0) : treeRootLeafAmplitude f S q k u = 0 :=
  treeRootLeafModulation_eq_zero _ _ _ _ _ hk

theorem norm_iteratedFDeriv_treeRootLeafAmplitude_le {d n m J j : ℕ}
    (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (hj : j ≤ J) (k : Mom d) (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (fun k => treeRootLeafAmplitude f S q k u) k‖ ≤
      treeRootLeafEnvelope J f S q u :=
  norm_iteratedFDeriv_treeRootLeafModulation_spectrum_le _ _ _ _ hj k

/-- The envelope is measured on the actual countable centers and original Lebesgue frequencies. -/
theorem measurable_treeRootLeafEnvelope {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) : Measurable (treeRootLeafEnvelope J f S q) := by
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  apply measurable_const.mul
  apply ENNReal.measurable_toReal.comp
  exact measurable_from_prod_countable_right (fun c =>
    (continuous_treeLeafMomentEnvelope (J+1) _ hK hBq.le hq c.1).measurable)

/-- Actual derivative tensors are strongly measurable in the counted cells and the
independent leaf frequencies; no separability premise on a tensor space is assumed. -/
theorem stronglyMeasurable_treeRootLeafAmplitude_derivative {d n m K M : ℕ}
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (j : ℕ) :
    StronglyMeasurable (fun u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ) =>
      iteratedFDeriv ℝ j (fun k => treeRootLeafAmplitude f S q k u) k) := by
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  change StronglyMeasurable (Function.uncurry (fun (cell : SourceCellIndex S) α =>
    iteratedFDeriv ℝ j (fun k => treeRootLeafAmplitude f S q k (cell,α)) k))
  apply stronglyMeasurable_countable_slices
  intro cell
  let g := appendRootInput f (treeRootPartition q)
  have hcoef : Continuous (treeLeafSpectrum g cell.1) := by
    unfold treeLeafSpectrum
    apply continuous_finsetProd
    intro a _
    have hi := Fourier.integrable_of_timeFourierNorm_lt_top
      ((timeFourierNorm_leafCell_le hK hBq.le (hq a) (cell.1 a)).trans_lt ENNReal.ofReal_lt_top)
    exact (Fourier.timeFourier_continuous hi).comp (continuous_apply a)
  have hto : Continuous (fun ξ : Fin d → ℝ => (toLp 2 ξ : Mom d)) := PiLp.continuous_toLp 2 _
  let v := fun α : Fin (m+1) → Fin d → ℝ => ∑ a, (toLp 2 (α a):Mom d)
  have hv : Continuous v := by unfold v; fun_prop
  let c := fun α : Fin (m+1) → Fin d → ℝ =>
    ((((1+∑ a, ‖(toLp 2 (α a):Mom d)‖):ℝ):ℂ)*treeLeafSpectrum g cell.1 α)
  have hc : Continuous c := by dsimp only [c]; fun_prop
  let ψ := fun k : Mom d => treeRootCutoff q k * sourceRootMask cell.1 k
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_treeRootCutoff q).mul (contDiff_sourceRootMask cell.1)
  have he (α : Fin (m+1) → Fin d → ℝ) :
      (fun k => treeRootLeafAmplitude f S q k (cell,α)) =
        fun k => ψ k * (c α * (Real.fourierChar (inner ℝ (v α) k):ℂ)) := by
    funext k
    simp only [treeRootLeafAmplitude, treeRootLeafModulation, maskedModulation, ψ, c, v, g]
    ring
  simp_rw [he]
  exact continuous_iteratedFDeriv_smooth_modulated ψ hψ c hc v hv k j

/-- Actual counted mass with its root-center-independent geometric constant. -/
theorem lintegral_treeRootLeafEnvelope_le {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B C : ℝ} (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n) (q : Fin d → ℤ) :
    (∫⁻ u, ENNReal.ofReal (treeRootLeafEnvelope J f S q u) ∂treeLeafCellMeasure S) ≤
      ENNReal.ofReal (treeRootLeafDerivativeConstant d J) * (ENNReal.ofReal (C^n) *
        ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M * treeAugmentedInputBound d K M B)^(m+1)) := by
  have he (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) :
      ENNReal.ofReal (treeRootLeafEnvelope J f S q u) =
      ENNReal.ofReal (treeRootLeafDerivativeConstant d J) *
        treeLeafMomentEnvelope (J+1) (appendRootInput f (treeRootPartition q)) u.1.1 u.2 := by
    rw [treeRootLeafEnvelope, ENNReal.ofReal_mul (treeRootLeafDerivativeConstant_nonneg _ _),
      ENNReal.ofReal_toReal (treeLeafMomentEnvelope_ne_top _ _ _ _)]
  simp_rw [he]
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  have hm : Measurable (fun u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ) =>
      treeLeafMomentEnvelope (J+1) (appendRootInput f (treeRootPartition q)) u.1.1 u.2) :=
    measurable_from_prod_countable_right (fun c =>
      (continuous_treeLeafMomentEnvelope (J+1) _ (by omega) hBq.le hq c.1).measurable)
  rw [lintegral_const_mul _ hm]
  exact mul_le_mul' le_rfl (lintegral_treeLeafCellMoment_root_le (J+1) f (by omega) hM hB hf S hS q)

/-- Integrability follows from this actual finite source mass, not an assumed final bound. -/
theorem integrable_treeRootLeafEnvelope {d n m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B C : ℝ} (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n) (q : Fin d → ℤ) :
    Integrable (treeRootLeafEnvelope J f S q) (treeLeafCellMeasure S) := by
  refine ⟨(measurable_treeRootLeafEnvelope J f (by omega) hf S q).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have hfinite := (lintegral_treeRootLeafEnvelope_le J f hK hM hB hf S hS q).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)))
  simpa only [← ofReal_norm, Real.norm_of_nonneg (treeRootLeafEnvelope_nonneg J f S q _)] using hfinite

end WaveTurbulence.RegAsymp
