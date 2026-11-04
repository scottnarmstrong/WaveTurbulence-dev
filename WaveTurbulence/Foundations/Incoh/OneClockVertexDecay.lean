/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OneClockCoupleDecay
public import WaveTurbulence.Foundations.Incoh.OneClockSelection

/-!
# Intrinsic one-vertex source theorem for degenerate couples

TARGET L1049, audit P-1. The statement selects only the actual genuine
root vertex. The proof constructs the auxiliary clock explicitly, so no
second-root-coordinate carrier is assumed by the final source theorem.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Literal one-root-clock source integral, with no auxiliary clock in its definition. -/
@[expose] def vertexClockKernel {d n : ℕ} (v : Fin n × Fin 2) (a : Fin 2)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ :=
  normalizedLinkIntegral L γ δ Q (I ∩ {w | w v.1 v.2 ≤ t a})

/-- The actual root layer and an arbitrary passive external unit interval. -/
@[expose] def vertexClockBox {d n : ℕ} (v : Fin n × Fin 2) (a : Fin 2)
    (Q : Fin n → LayerLink d) (b : ℝ) : Set (Fin 2 → ℝ) :=
  Icc (fun j => if j = a then (vertexLayer Q v : ℝ) else b)
    (fun j => (if j = a then (vertexLayer Q v : ℝ) else b) + 1)

/-- TARGET's one-trivial-tree case has the final temporal restriction bound without two source roots. -/
theorem exists_vertexClockKernel_timeRestriction_bound (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ v : Fin n × Fin 2, ∀ a : Fin 2, ∀ b : ℝ,
        Fourier.timeRestrictionNorm η (vertexClockBox v a Q b)
          (fun t => vertexClockKernel v a L γ δ Q I t) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_oneClockKernel_timeRestriction_bound d hd η hη hη₁
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hg hspan I hI hbox v a b
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
  have hker (t : Fin 2 → ℝ) : R.oneClockKernel a L γ δ Q I t = vertexClockKernel v a L γ δ Q I t := by
    unfold RootCoordinates.oneClockKernel vertexClockKernel
    congr 2
    ext w
    simp only [RootCoordinates.oneClockCut, mem_ofPred_eq, heval]
  have hr := hb L hL n Q hg hspan I hI hbox R a b
  rw [hboxeq] at hr
  simpa only [hker] using hr

end WaveTurbulence.Incoh
