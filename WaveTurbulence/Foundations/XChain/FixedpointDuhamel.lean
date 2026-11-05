/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SlotIntegrability
/-! The constructed fixed point satisfies the actual integral a-system, with no slot hypotheses. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset Set
open SysAPI

theorem fixedpoint_duhamel {d p : ℕ} (L γ δ : ℝ) (hL : 0 < L) (N : ℕ)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    {Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ)
    (hfp : b = (fun (t : ZTime p) n => Lop L γ δ p N c 0 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N c 1 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N c 2 b t n) +
      (fun (t : ZTime p) n => Lop L γ δ p N c 3 b t n))
    (t : ZTime p) (n : Fin d → ℤ) :
    aTr L γ δ p N c t n + b t n = c n + ∫ s in (p : ℝ)..t.1,
      aNonlin L γ δ 1 s
        (fun m => aTr L γ δ p N c s m + IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m)
        (fun m => (starRingEnd ℂ) (aTr L γ δ p N c s m +
          IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m))
        (fun m => aTr L γ δ p N c s m + IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s m) n := by
  have h := (duhamel_iff_Lop' L γ δ p N hc (zSpace_summable hL hb hΛ) t.2.1 n
    (fun x _ => intervalIntegrable_slotTriple L γ δ hL N hc hb hΛ x t n)).mpr (by
      rw [IccExtend_of_mem _ b t.2]
      have he := congrFun (congrFun hfp t) n
      simpa only [Pi.add_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using he)
  rw [IccExtend_of_mem _ b t.2] at h
  exact h

end WaveTurbulence.Induct
