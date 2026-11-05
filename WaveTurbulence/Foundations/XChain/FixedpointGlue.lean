/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedpointDuhamel
public import WaveTurbulence.Foundations.XChain.IntegralRegularity
public import WaveTurbulence.Foundations.XChain.ZOperations
/-! TARGET S1: the actual Lop fixed point extends the old classed a-system solution. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open SysAPI

theorem fixedpoint_glue {d p : ℕ} (L γ δ : ℝ) (hL : 0 < L) (N : ℕ)
    {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsASolution L γ δ p c a)
    {Λ A C : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ) (hΛA : Λ ≤ A)
    (htr : ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
      ‖aTr L γ δ p N (a p) t n‖ ≤ jbr (latticePoint L n) ^ (-A) * C)
    (hfp : b = (fun (t : ZTime p) n => Lop L γ δ p N (a p) 0 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N (a p) 1 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N (a p) 2 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N (a p) 3 b t n)) :
    IsASolution L γ δ (p + 1) c (fun s => if s ≤ p then a s else
      fun n => aTr L γ δ p N (a p) s n + IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s n) := by
  have hc := SysAPI.IsASolution.summable_norm hL ha ⟨Nat.cast_nonneg p, le_rfl⟩
  let f : ZTime p → (Fin d → ℤ) → ℂ := fun t n => aTr L γ δ p N (a p) t n + b t n
  have hf : f ∈ ZSpace L Λ p :=
    zSpace_add (zSpace_mono hΛA (aTr_mem_ZSpace L γ δ N hc A C htr)) hb
  let B : ℝ → (Fin d → ℤ) → ℂ := fun t n =>
    aTr L γ δ p N (a p) t n + IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n
  have hB (t : ZTime p) : B t = f t := by
    dsimp only [B, f]
    rw [IccExtend_of_mem _ b t.2]
  have hi (t : ZTime p) (n : Fin d → ℤ) :
      B t n = a p n + ∫ s in (p : ℝ)..t.1,
        aNonlin L γ δ 1 s (B s) (fun m => (starRingEnd ℂ) (B s m)) (B s) n := by
    rw [hB t]
    exact fixedpoint_duhamel L γ δ hL N hc hb hΛ hfp t n
  apply SysAPI.IsASolution.glue (Nat.cast_nonneg p) (by linarith) ha B
  · funext n
    have h := hi ⟨p, by constructor <;> linarith⟩ n
    simpa only [intervalIntegral.integral_same, add_zero] using h
  · refine ⟨(ZNorm L Λ f).toReal, fun t ht n => ?_⟩
    rw [show B t = f ⟨t, ht⟩ from hB ⟨t, ht⟩]
    exact zSpace_class_bound hf hΛ _ n
  · exact zCurve_hasDerivWithinAt L γ δ hL hf hΛ B hB (a p) hi

end WaveTurbulence.Induct
