/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CellFourierInversion
public import WaveTurbulence.Foundations.Incoh.SpectralMomentContinuity
public import WaveTurbulence.Foundations.Incoh.MomentumTreeInputs
public import WaveTurbulence.Foundations.Incoh.SourceRootFrequency
public import WaveTurbulence.Foundations.Incoh.TreeAugmentedInputBounds
public import WaveTurbulence.Foundations.ApproxNT.Products

/-! # Independent leaf Fourier inversion for the actual tree momentum carrier

Link cutoffs remain in physical space. Only original leaf inputs and the temporary
moving root input are Fourier expanded; their actual moment totals stay separate.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal

/-- Transpose of the literal source input rows, with no link-cutoff Fourier variables. -/
def treeLeafFrequency {d n m w : ℕ} (P : MomentumTreeData n m w)
    (α : Fin m → Mom d) (j : MomentumCoordinate n) : Mom d :=
  ∑ a, P.inputRow a j • α a

/-- The root frequency is exactly the sum of the independent leaf frequencies. -/
theorem treeLeafFrequency_root {d n m w : ℕ} (P : MomentumTreeData n m w)
    (α : Fin m → Mom d) : treeLeafFrequency P α none = ∑ a, α a := by
  simp only [treeLeafFrequency, P.input_root_column, one_smul]

/-- Exact finite transpose identity of the actual input momentum map. -/
theorem sum_inner_treeInputMomentum {d n m w : ℕ} (P : MomentumTreeData n m w)
    (α : Fin m → Mom d) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (∑ a, inner ℝ (α a) (P.inputMomentum k x a)) =
      ∑ j : MomentumCoordinate n, inner ℝ (treeLeafFrequency P α j) (rootLinkMomenta k x j) := by
  change (∑ a, inner ℝ (α a) (∑ j : MomentumCoordinate n, P.inputRow a j • rootLinkMomenta k x j)) = _
  simp only [inner_sum, treeLeafFrequency, sum_inner, ← Int.cast_smul_eq_zsmul ℝ,
    inner_smul_right, inner_smul_left, conj_trivial]
  rw [Finset.sum_comm]

/-- Separate the actual root phase and the two frequencies of each link. -/
theorem sum_inner_treeInputMomentum_root_links {d n m w : ℕ} (P : MomentumTreeData n m w)
    (α : Fin m → Mom d) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (∑ a, inner ℝ (α a) (P.inputMomentum k x a)) =
      inner ℝ (∑ a, α a) k + ∑ j,
        (inner ℝ (treeLeafFrequency P α (some (j,0))) (x j 0) +
          inner ℝ (treeLeafFrequency P α (some (j,1))) (x j 1)) := by
  rw [sum_inner_treeInputMomentum P α k x]
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two,
    rootLinkMomenta, treeLeafFrequency_root]

/-- Literal independent-leaf Fourier inversion, valid also for the empty input family. -/
theorem tree_leafCellProduct_eq_frequencyIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {f : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    (∏ a, leafCell (f a) (c a) (P.inputMomentum k x a)) =
      ∫ α : Fin m → Fin d → ℝ,
        ∏ a, Real.fourierChar (Fourier.timePairing d (α a) (ofLp (P.inputMomentum k x a))) •
          Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) (α a) := by
  rw [integral_fintype_prod_volume_eq_prod (fun (a : Fin m) (ξ : Fin d → ℝ) =>
    Real.fourierChar (Fourier.timePairing d ξ (ofLp (P.inputMomentum k x a))) •
      Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) ξ)]
  exact Finset.prod_congr rfl (fun a _ => leafCell_eq_fourierIntegral hK hB (hf a) (c a) _)

/-- The actual independent leaf coefficient. -/
def treeLeafSpectrum {d m : ℕ} (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) : ℂ :=
  ∏ a, Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) (α a)

/-- Independent source Fourier moments, including all separate leaf centers. -/
def treeLeafMomentEnvelope {d m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) : ℝ≥0∞ :=
  ∏ a, ‖((((1+‖toLp 2 (α a)‖)^J:ℝ):ℂ)*
    Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) (α a))‖ₑ

/-- One total frequency moment is paid independently at the leaves, without a loss
in the number of leaves or in the moment order. -/
theorem treeLeafSpectrum_moment_le {d m : ℕ} (J : ℕ) (f : Fin m → Mom d → ℂ)
    (c : Fin m → Fin d → ℤ) (α : Fin m → Fin d → ℝ) :
    ENNReal.ofReal ((1+∑ a, ‖toLp 2 (α a)‖)^J) * ‖treeLeafSpectrum f c α‖ₑ ≤
      treeLeafMomentEnvelope J f c α := by
  have hs := one_add_sum_le_prod_one_add Finset.univ
    (fun a : Fin m => ‖toLp 2 (α a)‖) (fun _ _ => norm_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+∑ a, ‖toLp 2 (α a)‖) hs J
  rw [← Finset.prod_pow] at hp
  have hw (a : Fin m) : ‖(((1+‖toLp 2 (α a)‖)^J:ℝ):ℂ)‖ₑ =
      ENNReal.ofReal ((1+‖toLp 2 (α a)‖)^J) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp only [treeLeafSpectrum, treeLeafMomentEnvelope, ApproxNT.enorm_finset_prod, enorm_mul, hw]
  rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl

/-- Exact Tonelli factorization retains actual per-input masses rather than bounding them
by a common translated spatial norm. -/
theorem tsum_lintegral_treeLeafMomentEnvelope {d m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ, ∫⁻ α, treeLeafMomentEnvelope J f c α) =
      ∏ a, leafFourierMomentTotal J (f a) := by
  have hmeas (a : Fin m) (c : Fin d → ℤ) :
      Measurable (fun ξ : Fin d → ℝ => ‖((((1+‖toLp 2 ξ‖)^J:ℝ):ℂ)*
        Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) c (toLp 2 y)) ξ)‖ₑ) :=
    (continuous_spectralMomentProfile (n := 0) J (fun _ : Fin 1 => f a)
      (fun _ : Fin 1 => c) hK hB (fun _ => hf a) (.inl 0)).measurable.enorm
  calc
    _ = ∑' c : Fin m → Fin d → ℤ, ∏ a, leafFourierMomentMass J (f a) (c a) := by
      apply tsum_congr
      intro c
      exact ApproxNT.lintegral_fintype_prod_eq_prod (μ := volume)
        (fun (a : Fin m) (ξ : Fin d → ℝ) => ‖((((1+‖toLp 2 ξ‖)^J:ℝ):ℂ)*
          Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) ξ)‖ₑ)
        (fun a => hmeas a (c a))
    _ = _ := tsum_fin_product_ennreal m (fun a c => leafFourierMomentMass J (f a) c)

/-- The appended moving-root input has a uniform geometric leaf-only Fourier mass.
Its center-dependent spatial norm is used solely to justify measurability. -/
theorem tsum_lintegral_treeLeafMomentEnvelope_root_le {d m K M : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) (q : Fin d → ℤ) :
    (∑' c : Fin (m+1) → Fin d → ℤ,
      ∫⁻ α, treeLeafMomentEnvelope J (appendRootInput f (treeRootPartition q)) c α) ≤
      ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B)^(m+1) := by
  obtain ⟨Bq,hBq,hq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  rw [tsum_lintegral_treeLeafMomentEnvelope J _ (by omega) hBq.le hq]
  exact prod_leafFourierMomentTotal_appendRootPartition_le J f hK hM hB hf q

end WaveTurbulence.RegAsymp
