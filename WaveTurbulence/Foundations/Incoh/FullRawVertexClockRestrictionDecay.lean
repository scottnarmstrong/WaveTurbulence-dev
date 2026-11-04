/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FullRawOneClockRestrictionDecay
public import WaveTurbulence.Foundations.Incoh.OneClockVertexDecay
public import WaveTurbulence.Foundations.Incoh.RawVertexClockRestrictionDecay

/-! # Raw incoherence decay for the one-trivial-tree couple case

TARGET L1049, audit P-1: the final raw-source theorem selects only one
genuine root vertex and has no second-root-clock premise.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual raw source couple restriction decay with its explicit dimensional localization cost. -/
theorem exists_rawVertexClockKernel_fullRestriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J W K M : ℕ,
          ∀ P : MomentumTreeData n m w, ∀ _Croot : RootInputCoordinates P,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ v : Fin n × Fin 2, ∀ a : Fin 2, ∀ b : ℝ,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → W + 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          Fourier.mixedRestrictionNorm η J W (vertexClockBox v a Q b) A
            (fun t k => P.sourceVertexClockKernel ζ v a L γ δ Q I f t k) ≤
            (ENNReal.ofReal (maskedSourceSpatialConstant d m J W) * ENNReal.ofReal (Cₗ ^ n) *
              (ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W * B) ^ m *
              ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hb⟩ := exists_rawOneClockKernel_fullRestriction_bound d hd
  refine ⟨Cₗ, hCₗ, ?_⟩
  intro η hη hη₁
  obtain ⟨C₀, hC₀, hb⟩ := hb η hη hη₁
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w J W K M P Croot hinputs Q hspan hg v a b I hI hbox f B hK hM hB hf ζ A
  let hn := one_le_linkCount_of_incoherent Q hg
  let R := oneClockSelection n hn v a
  have hroot : R.rootVertex a = v := oneClockSelection_rootVertex n hn v a
  have heval (w : Fin n → Fin 2 → ℝ) : (R.equiv w).1 a = w v.1 v.2 := by
    have he := R.equiv_symm_rootVertex (R.equiv w).1 (R.equiv w).2 a
    rw [hroot] at he
    simpa only [Prod.eta, MeasurableEquiv.symm_apply_apply] using he.symm
  have hbase : R.baseRootTimes Q a = (vertexLayer Q v : ℝ) := by
    rw [RootCoordinates.baseRootTimes, hroot]
  have hboxeq : R.oneClockBox a Q b = vertexClockBox v a Q b := by
    unfold RootCoordinates.oneClockBox vertexClockBox
    congr 1 <;> funext j <;> by_cases hj : j = a <;> simp [hj, hbase]
  have hker (t : Fin 2 → ℝ) (k : Mom d) :
      P.sourceOneClockKernel ζ R a L γ δ Q I f t k =
        P.sourceVertexClockKernel ζ v a L γ δ Q I f t k := by
    unfold MomentumTreeData.sourceOneClockKernel MomentumTreeData.sourceVertexClockKernel
    congr 2
    ext w
    simp only [RootCoordinates.oneClockCut, mem_ofPred_eq, heval]
  have hr := hb L hL n m w J W K M P Croot hinputs Q hspan hg R a b I hI hbox f B hK hM hB hf ζ A
  rw [hboxeq] at hr
  simpa only [hker] using hr

end WaveTurbulence.Incoh
