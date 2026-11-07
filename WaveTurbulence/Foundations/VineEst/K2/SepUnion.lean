/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TraceBox
public import WaveTurbulence.Foundations.SumintSigned.NormScalar
public import WaveTurbulence.Foundations.Fourier.Norm00VBasic
public import WaveTurbulence.Foundations.Fourier.Norm00VCutoff

/-! # W2-KIND2 (far case): the separated-union lemma (R114, qh ≥ q4 + 2)

`XNorm00Restr_union_sep`: for two sets in unit cells `cell q`, `cell q'` that are `≥ 1` apart in one coordinate (`q j + 2 ≤ q' j` or
`q' j + 2 ≤ q j`), `‖F‖_{𝔛^θ(B ∪ B')} ≤ (cc + 1) (‖F‖_{𝔛^θ(B)} + ‖F‖_{𝔛^θ(B')})` with the translation-invariant cutoff constant
`cc = cutoffMultiplierConstant θ (cutQ 0)`.  The proof glues two arbitrary extensions with the translated smooth cutoffs `cutQ q`, `cutQ q'`
(`cutQ q = 1` on `cell q` and `= 0` on the far cell); there is no exponent loss and no clamp.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

theorem cutQ_eq_zero_of_sep {r : ℕ} {q q' t : Fin r → ℝ} (j : Fin r) (ht : t ∈ cell q)
    (hsep : q j + 2 ≤ q' j ∨ q' j + 2 ≤ q j) : cutQ q' t = 0 := by
  unfold cutQ coordinateCutoff
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  have h1 := ht j
  simp only [mem_Icc] at h1
  have := chiUnit_eq_zero (x := t j - q' j) (by
    rcases hsep with h | h
    · left; linarith [h1.2]
    · right; linarith [h1.1])
  simpa using this

/-- **The separated-union lemma.** -/
theorem XNorm00Restr_union_sep {r : ℕ} {V : Type*} (θ : ℝ) {q q' : Fin r → ℝ} (j : Fin r)
    (hsep : q j + 2 ≤ q' j ∨ q' j + 2 ≤ q j) {B B' : Set (Fin r → ℝ)} (hB : B ⊆ cell q) (hB' : B' ⊆ cell q')
    (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ (B ∪ B') K F ≤
      (cutoffMultiplierConstant θ (cutQ (0 : Fin r → ℝ)) + 1) * (XNorm00Restr θ B K F + XNorm00Restr θ B' K F) := by
  have hcc : cutoffMultiplierConstant θ (cutQ (0 : Fin r → ℝ)) ≠ ⊤ :=
    (cutoffMultiplierConstant_lt_top θ (cutQ_hasCompactSupport _) (cutQ_contDiff _)).ne
  set c : ℝ≥0∞ := cutoffMultiplierConstant θ (cutQ (0 : Fin r → ℝ)) + 1 with hc
  have hc0 : c ≠ 0 := by simp [hc]
  have hct : c ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hcc, ENNReal.one_ne_top⟩
  have hcc1 : cutoffMultiplierConstant θ (cutQ (0 : Fin r → ℝ)) ≤ c := le_self_add
  have key : ∀ G G' : (Fin r → ℝ) → V → ℂ, (∀ t ∈ B, ∀ v ∈ K, G t v = F t v) → (∀ t ∈ B', ∀ v ∈ K, G' t v = F t v) →
      XNorm00Restr θ (B ∪ B') K F ≤ c * XNorm00 θ G + c * XNorm00 θ G' := by
    intro G G' hG hG'
    by_cases h1 : XNorm00 θ G = ⊤
    · rw [h1, ENNReal.mul_top hc0]; simp
    by_cases h2 : XNorm00 θ G' = ⊤
    · rw [h2, ENNReal.mul_top hc0]; simp
    have f1 : mixedFourierNorm00 θ G < ⊤ := by
      rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact lt_top_iff_ne_top.2 h1
    have f2 : mixedFourierNorm00 θ G' < ⊤ := by
      rw [← NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]; exact lt_top_iff_ne_top.2 h2
    let H : (Fin r → ℝ) → V → ℂ := fun t v => G t v * cutQ q t + G' t v * cutQ q' t
    have hH : ∀ t ∈ B ∪ B', ∀ v ∈ K, H t v = F t v := by
      intro t ht v hv
      rcases ht with ht | ht
      · simp only [H, cutQ_eq_one (hB ht), cutQ_eq_zero_of_sep j (hB ht) hsep, mul_one, mul_zero, add_zero]
        exact hG t ht v hv
      · have hs' : q' j + 2 ≤ q j ∨ q j + 2 ≤ q' j := hsep.symm
        simp only [H, cutQ_eq_one (hB' ht), cutQ_eq_zero_of_sep j (hB' ht) hs', mul_one, mul_zero, zero_add]
        exact hG' t ht v hv
    refine (iInf₂_le H hH).trans ?_
    rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00,
      NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
    refine (mixedFourierNorm00_add_le θ (fun t v => G t v * cutQ q t) (fun t v => G' t v * cutQ q' t)).trans ?_
    have e1 := mixedFourierNorm00_mul_cutoff_le θ f1 (cutQ_hasCompactSupport q) (cutQ_contDiff q)
    have e2 := mixedFourierNorm00_mul_cutoff_le θ f2 (cutQ_hasCompactSupport q') (cutQ_contDiff q')
    rw [Eng.cc_translate] at e1 e2
    exact add_le_add (e1.trans (mul_le_mul' hcc1 le_rfl)) (e2.trans (mul_le_mul' hcc1 le_rfl))
  have e : c * XNorm00Restr θ B K F + c * XNorm00Restr θ B' K F = c * (XNorm00Restr θ B K F + XNorm00Restr θ B' K F) :=
    (mul_add _ _ _).symm
  rw [← e]
  generalize XNorm00Restr θ (B ∪ B') K F = x at key ⊢
  unfold XNorm00Restr
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine ENNReal.le_iInf₂_add_iInf₂ fun G hG G' hG' => ?_
  exact key G G' hG hG'

end WaveTurbulence.VineEstS5C.P4.W2.K2
