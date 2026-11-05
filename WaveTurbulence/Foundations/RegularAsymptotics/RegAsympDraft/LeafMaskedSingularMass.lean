/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSingularCellMass
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskBounds

/-! # The literal root mask and character preserve global singular coefficient mass -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ApproxNT

/-- The actual root masks have a dimensional uniform scalar bound. -/
theorem norm_sourceRootMask_le {d m : ℕ} (c : Fin m → Fin d → ℤ) (k : Mom d) :
    ‖sourceRootMask c k‖ ≤ rootMaskDerivativeConstant d 0 := by
  simpa only [norm_iteratedFDeriv_zero] using
    norm_iteratedFDeriv_sourceRootMask_le (J := 0) c (j := 0) le_rfl k

/-- Exact coefficient for the original source, retaining its root mask
and the root Fourier character from the leaf-only inversion. -/
def leafMaskedSingularCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (i : LeafSingularCellIndex S)
    (uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) : ℂ :=
  leafSingularCellCoefficient hQ hG F S i uv *
    (sourceRootMask i.1 k*(Real.fourierChar (inner ℝ (∑ a, toLp 2 (uv.1 a)) k):ℂ))

theorem norm_leafMaskedSingularCoefficient_le {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (i : LeafSingularCellIndex S)
    (uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d))) :
    ‖leafMaskedSingularCoefficient hQ hG F S k i uv‖ ≤
      rootMaskDerivativeConstant d 0*‖leafSingularCellCoefficient hQ hG F S i uv‖ := by
  rw [leafMaskedSingularCoefficient,norm_mul,norm_mul,Circle.norm_coe,mul_one]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (norm_sourceRootMask_le i.1 k)
    (norm_nonneg (leafSingularCellCoefficient hQ hG F S i uv))

theorem stronglyMeasurable_leafMaskedSingularCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    {F : Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d) (i : LeafSingularCellIndex S) :
    StronglyMeasurable (leafMaskedSingularCoefficient hQ hG F S k i) := by
  have hchar : Continuous (fun uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      (Real.fourierChar (inner ℝ (∑ a, toLp 2 (uv.1 a)) k):ℂ)) := by fun_prop
  exact (stronglyMeasurable_leafSingularCellCoefficient hQ hG hK hB hF S i).mul
    (stronglyMeasurable_const.mul hchar.stronglyMeasurable)

theorem integrable_leafMaskedSingularCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) (k : Mom d) (i : LeafSingularCellIndex S) :
    Integrable (leafMaskedSingularCoefficient hQ hG F S k i) := by
  have hi := (integrable_leafSingularCellCoefficient hQ hG hn hK hM hB hF S i).norm.const_mul
    (rootMaskDerivativeConstant d 0)
  exact hi.mono' (stronglyMeasurable_leafMaskedSingularCoefficient hQ hG (by omega) hB hF S k i).aestronglyMeasurable
    (ae_of_all _ (norm_leafMaskedSingularCoefficient_le hQ hG F S k i))

/-- The original mask and character preserve the countable absolute
coefficient mass required by the actual singular integral representation. -/
theorem summable_integral_norm_leafMaskedSingularCoefficient {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) (k : Mom d) :
    Summable (fun i : LeafSingularCellIndex S => ∫ uv, ‖leafMaskedSingularCoefficient hQ hG F S k i uv‖) := by
  have hs := (summable_integral_norm_leafSingularCellCoefficient hQ hG hn hK hM hB hF S hS).mul_left
    (rootMaskDerivativeConstant d 0)
  apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _ hs
  intro i
  rw [← integral_const_mul]
  exact integral_mono
    (integrable_leafMaskedSingularCoefficient hQ hG hn hK hM hB hF S k i).norm
    ((integrable_leafSingularCellCoefficient hQ hG hn hK hM hB hF S i).norm.const_mul _)
    (norm_leafMaskedSingularCoefficient_le hQ hG F S k i)

end WaveTurbulence.RegAsymp
