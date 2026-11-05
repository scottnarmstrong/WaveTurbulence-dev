/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ZBounds
public import WaveTurbulence.Foundations.XChain.TreeTimeContinuity
/-! Elementary Z operations and conversion of the fixedpoint gate's tree bound. -/
public section
namespace WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem ZNorm_le_of_decay {d p : ℕ} (L Λ C : ℝ)
    {f : ZTime p → (Fin d → ℤ) → ℂ}
    (hf : ∀ t n, ‖f t n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * C) :
    ZNorm L Λ f ≤ ENNReal.ofReal C := by
  apply iSup_le fun t => iSup_le fun n => ?_
  apply ENNReal.ofReal_le_ofReal
  have hw := zWeight_pos L Λ n
  calc
    _ ≤ zWeight L Λ n * (jbr (latticePoint L n) ^ (-Λ) * C) :=
      mul_le_mul_of_nonneg_left (hf t n) hw.le
    _ = C := by
      have hj : 0 < jbr (latticePoint L n) := Real.sqrt_pos.mpr (by positivity)
      rw [Real.rpow_neg hj.le]
      exact mul_inv_cancel_left₀ hw.ne' _

theorem ZNorm_add_le {d p : ℕ} (L Λ : ℝ)
    (f g : ZTime p → (Fin d → ℤ) → ℂ) :
    ZNorm L Λ (f + g) ≤ ZNorm L Λ f + ZNorm L Λ g := by
  apply iSup_le fun t => iSup_le fun n => ?_
  have hw := (zWeight_pos L Λ n).le
  calc
    _ ≤ ENNReal.ofReal (zWeight L Λ n * ‖f t n‖ + zWeight L Λ n * ‖g t n‖) :=
      ENNReal.ofReal_le_ofReal (by simpa only [Pi.add_apply, mul_add, zWeight] using
        (mul_le_mul_of_nonneg_left (norm_add_le (f t n) (g t n)) hw))
    _ = ENNReal.ofReal (zWeight L Λ n * ‖f t n‖) +
        ENNReal.ofReal (zWeight L Λ n * ‖g t n‖) :=
      ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _))
    _ ≤ _ := add_le_add
      (le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖f t n‖)) n))
      (le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖g t n‖)) n))

theorem ZNorm_mono {d p : ℕ} (L : ℝ) {Λ A : ℝ} (hΛ : Λ ≤ A)
    (f : ZTime p → (Fin d → ℤ) → ℂ) : ZNorm L Λ f ≤ ZNorm L A f := by
  apply iSup_le fun t => iSup_le fun n => ?_
  apply le_trans _ (le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal
    (jbr (latticePoint L n) ^ A * ‖f t n‖)) n))
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le _ hΛ
  unfold jbr
  exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖latticePoint L n‖])

theorem zSpace_mono {d p : ℕ} {L Λ A : ℝ} (hΛ : Λ ≤ A)
    {f : ZTime p → (Fin d → ℤ) → ℂ} (hf : f ∈ ZSpace L A p) : f ∈ ZSpace L Λ p :=
  ⟨hf.1, (ZNorm_mono L hΛ f).trans_lt hf.2⟩

theorem zSpace_add {d p : ℕ} {L Λ : ℝ} {f g : ZTime p → (Fin d → ℤ) → ℂ}
    (hf : f ∈ ZSpace L Λ p) (hg : g ∈ ZSpace L Λ p) : f + g ∈ ZSpace L Λ p :=
  ⟨fun n => (hf.1 n).add (hg.1 n),
    (ZNorm_add_le L Λ f g).trans_lt (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩

theorem aTr_mem_ZSpace {d p : ℕ} (L γ δ : ℝ) (N : ℕ) {c : (Fin d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖) (Λ C : ℝ)
    (htr : ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
      ‖aTr L γ δ p N c t n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * C) :
    (fun (t : ZTime p) n => aTr L γ δ p N c t n) ∈ ZSpace L Λ p := by
  refine ⟨fun n => continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_aTr L γ δ p N (p + 1) hc n), ?_⟩
  exact (ZNorm_le_of_decay L Λ C (fun t n => htr t t.2 n)).trans_lt ENNReal.ofReal_lt_top

end WaveTurbulence.Induct
