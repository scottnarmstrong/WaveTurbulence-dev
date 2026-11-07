/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.DefectRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ThetaMono

/-! # P2: conjugation invariance of the scalar time norm `XNorm00Restr`

`XNorm00Restr θ B K (conj F) = XNorm00Restr θ B K F` (no swap): `timeFT (conj F) λ = conj (timeFT F (-λ))`, the map
`λ ↦ -λ` preserves Lebesgue measure and `maxBracketPow`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence MeasureTheory
open scoped ENNReal ComplexConjugate

variable {r : ℕ} {V : Type*}

theorem timeFT_conj (F : (Fin r → ℝ) → V → ℂ) (lam : Fin r → ℝ) (v : V) :
    timeFT (fun t w => conj (F t w)) lam v = conj (timeFT F (-lam) v) := by
  unfold timeFT
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem maxBracketPow_neg (θ : ℝ) (lam : Fin r → ℝ) : maxBracketPow θ (-lam) = maxBracketPow θ lam := by
  unfold maxBracketPow
  simp [Pi.neg_apply, neg_sq]

theorem XNorm00_conj_le (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (fun t w => conj (F t w)) ≤ XNorm00 θ F := by
  classical
  unfold XNorm00
  by_cases hF : ∀ v, Integrable fun t => F t v
  · have hF' : ∀ v, Integrable fun t => conj (F t v) := fun v => by
      simpa using (Complex.conjCLE.integrable_comp_iff (φ := fun t => F t v) (μ := volume)).2 (hF v)
    rw [if_pos hF, if_pos hF']
    have hpt : ∀ lam : Fin r → ℝ, maxBracketPow θ lam * ⨆ v, ‖timeFT (fun t w => conj (F t w)) lam v‖ₑ =
        (fun μ : Fin r → ℝ => maxBracketPow θ μ * ⨆ v, ‖timeFT F μ v‖ₑ) (-lam) := by
      intro lam
      simp only [timeFT_conj, maxBracketPow_neg, RCLike.enorm_conj]
    rw [lintegral_congr hpt]
    exact le_of_eq ((Measure.measurePreserving_neg (volume : Measure (Fin r → ℝ))).lintegral_comp_emb
      (MeasurableEquiv.neg (Fin r → ℝ)).measurableEmbedding
      (fun μ : Fin r → ℝ => maxBracketPow θ μ * ⨆ v, ‖timeFT F μ v‖ₑ))
  · rw [if_neg hF]
    exact le_top

theorem XNorm00_conj (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00 θ (fun t w => conj (F t w)) = XNorm00 θ F := by
  refine le_antisymm (XNorm00_conj_le θ F) ?_
  have := XNorm00_conj_le θ (fun t w => conj (F t w))
  simpa using this

theorem XNorm00Restr_conj (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ B K (fun t w => conj (F t w)) = XNorm00Restr θ B K F := by
  unfold XNorm00Restr
  apply le_antisymm
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ t ∈ B, ∀ v ∈ K, (fun t w => conj (G t w)) t v = (fun t w => conj (F t w)) t v := by
      intro t ht v hv; simp only [hG t ht v hv]
    exact iInf_le_of_le (fun t w => conj (G t w)) (iInf_le_of_le hc (XNorm00_conj θ G).le)
  · refine le_iInf fun G => le_iInf fun hG => ?_
    have hc : ∀ t ∈ B, ∀ v ∈ K, (fun t w => conj (G t w)) t v = F t v := by
      intro t ht v hv; simp only [hG t ht v hv, Complex.conj_conj]
    exact iInf_le_of_le (fun t w => conj (G t w)) (iInf_le_of_le hc (XNorm00_conj θ G).le)

end WaveTurbulence.VineEstS5C.P2
