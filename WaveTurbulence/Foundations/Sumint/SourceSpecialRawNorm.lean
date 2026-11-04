/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialCoreGrouping
public import WaveTurbulence.Foundations.Sumint.SourceCoreNormFactor

/-!
# Exact first bad core raw norm in native three-time coordinates

The raw norm is precisely the original distinguished linear norm times
the first pair norm and its literal gap amplitude.
-/

public section
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The literal first bad raw core has exactly its original two old-factor norms. -/
theorem sourceCoreRawNorm_special {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (z : SourceCoreCoordinate D (.inl a.1) → ℝ) :
    sourceCoreRawNorm D L γ δ η p ν r t (.inl a.1) z =
      ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t (.inl a.1)
        (sourceCoreOldTimes D (.inl a.1) z ⟨.inl a.1,rfl⟩))*
      ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t (.inr (.inl a))
        (sourceCoreOldTimes D (.inl a.1) z ⟨.inr (.inl a),by simp only [sourceCoreGroup,ite_eq_left ha]⟩)) := by
  let f (b : FactorIdx D.S) : ℝ≥0∞ := if hb : sourceCoreGroup D b = .inl a.1 then
    ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t b (sourceCoreOldTimes D (.inl a.1) z ⟨b,hb⟩)) else 1
  have hf (b : {b : FactorIdx D.S // sourceCoreGroup D b = .inl a.1}) :
      f b.1 = ENNReal.ofReal (sourceTimeNormFactor D L γ δ η p ν r t b.1 (sourceCoreOldTimes D (.inl a.1) z b)) :=
    dite_eq_left b.2
  calc
    _ = ∏ b : {b : FactorIdx D.S // sourceCoreGroup D b = .inl a.1}, f b.1 := by
      unfold sourceCoreRawNorm
      apply Finset.prod_congr rfl
      intro b _
      exact (hf b).symm
    _ = _ := by
      rw [prod_sourceCore_special_fiber D a ha]
      simp only [f,dite_eq_left (show sourceCoreGroup D (.inl a.1) = .inl a.1 from rfl),
        dite_eq_left (show sourceCoreGroup D (.inr (.inl a)) = .inl a.1 by simp only [sourceCoreGroup,ite_eq_left ha])]

/-- In the exact native grouping the first bad raw norm reads the original scalar and pair source sums. -/
theorem sourceCoreRawNorm_special_grouped {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) (z : Fin 3 → ℝ) :
    sourceCoreRawNorm D L γ δ η p ν r t (.inl a.1) ((sourceSpecialCoreGrouping D a ha).symm z) =
      ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t a.1 (z 2)‖ *
        ENNReal.ofReal (pairGapAmplitude D η a (z 0,z 1)*‖pairTimeSum D L γ δ p ν r t a (z 0,z 1)‖) := by
  rw [sourceCoreRawNorm_special D L γ δ η p ν r t a ha,
    sourceSpecialCoreGrouping_symm_linear,sourceSpecialCoreGrouping_symm_pair]
  simp only [sourceTimeNormFactor,timeGapFactor,plainTimeNormFactor,one_mul,Matrix.cons_val_zero,
    Matrix.cons_val_one]

end WaveTurbulence.Sumint
