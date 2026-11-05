/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3ZModel
public import WaveTurbulence.Foundations.XChain.SysDraft.API
/-! (Copied verbatim from wt-cumul's INDUCT `ZBounds.lean`, sha256 `102d4a2ca32c9837044b08b9b1ab9b2b4e40c54c28043afdb30e777cfbf62dbe`; namespace `Induct` ↦ `Fixedpt` and the
imports of copied INDUCT modules renamed.)

 Uniform summability of Z curves in the class used by the NLS/Duhamel API. -/
public section
namespace WaveTurbulence.Fixedpt
open Set

/-- The draft jbr power agrees with the landed NLS class weight. -/
theorem zWeight_eq {d : ℕ} (L Λ : ℝ) (n : Fin d → ℤ) :
    zWeight L Λ n = (1 + ‖latticePoint L n‖ ^ 2) ^ (Λ / 2) := by
  unfold zWeight jbr
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- A Z curve with exponent at least d+1 has a uniform bound in the solution class. -/
theorem zSpace_class_bound {d p : ℕ} {L Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ) (t : ZTime p) (n : Fin d → ℤ) :
    (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖b t n‖ ≤
      (ZNorm L Λ b).toReal := by
  refine (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans (zSpace_weighted_bound hb t n)
  rw [zWeight_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖latticePoint L n‖])
    (by linarith)

/-- Extension by clamping time preserves the uniform class bound. -/
theorem zSpace_extended_class {d p : ℕ} {L Λ T : ℝ}
    {b : ZTime p → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ) :
    NLS.IsAkBounded L T (IccExtend (by linarith : (p : ℝ) ≤ p + 1) b) := by
  refine ⟨(ZNorm L Λ b).toReal, fun t _ n => ?_⟩
  exact zSpace_class_bound hb hΛ _ n

/-- Values of a Z curve are absolutely summable; the envelope is uniform in time. -/
theorem zSpace_summable {d p : ℕ} {L Λ : ℝ} (hL : 0 < L)
    {b : ZTime p → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ)
    (t : ZTime p) : Summable fun n => ‖b t n‖ := by
  have hc := zSpace_extended_class (T := p + 1) hb hΛ
  obtain ⟨C, _, hC⟩ := NLS.IsAkBounded.exists_norm_le hL hc
  have htime : t.1 ∈ Icc (0 : ℝ) (p + 1) := ⟨(Nat.cast_nonneg p).trans t.2.1, t.2.2⟩
  have he : IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t.1 = b t :=
    IccExtend_of_mem _ b t.2
  have hbound (n : Fin d → ℤ) : ‖b t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
    rw [← he]
    exact hC t htime n
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
    (NLS.summable_inv_one_add_norm_pow.mul_left C)

end WaveTurbulence.Fixedpt
