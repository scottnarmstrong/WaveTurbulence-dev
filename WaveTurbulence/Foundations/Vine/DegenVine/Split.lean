/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedBoundRestr
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink
public import WaveTurbulence.Foundations.Vine.DegenVine.Eps

/-! # The `ε`-weighted clocked expression and the main/defect split (DEGEN-VINE)

`clockedExprWith e` is V5's `clockedExpr` with the lattice sum weighted by a bounded coefficient `e(x)`
(for the vine chain `e = ε`, the product of `epsCoef` over the nodes of the chain).  With `e ≡ 1` it is
`clockedExpr` (the V5 main term).  The split `clockedExprWith ε = clockedExpr + clockedExprWith (ε - 1)`
and the norm inequality `‖K_ε‖ ≤ (c + 1)(‖K_main‖ + ‖K_defect‖)` (countable Minkowski, two terms) are
the *combination lemma*; the defect `ε - 1` is supported on the degenerate set (`DegenVine.Eps`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Mink
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintDatum d}

/-- `clockedExpr` with the lattice sum weighted by `e(x)`. -/
noncomputable def clockedExprWith (e : (D.S.VIdx → (Fin d → ℤ)) → ℂ) (cr : ClockedRows D)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) : ℂ :=
  ∑' x : D.S.VIdx → (Fin d → ℤ), e x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ

theorem clockedExprWith_one (cr : ClockedRows D) (cfs cs : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) :
    clockedExprWith (fun _ => 1) cr cfs cs hI L γ δ η tt E = clockedExpr cr cfs cs hI L γ δ η tt E := by
  unfold clockedExprWith clockedExpr
  simp only [one_mul]

/-- **Split.** If the unweighted summand is absolutely summable and `e` is bounded, then
`K_e = K_1 + K_{e-1}`. -/
theorem clockedExprWith_split (e : (D.S.VIdx → (Fin d → ℤ)) → ℂ) (B : ℝ) (he : ∀ x, ‖e x - 1‖ ≤ B)
    (cr : ClockedRows D) (cfs cs : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d)
    (hs : Summable fun x : D.S.VIdx → (Fin d → ℤ) => ‖∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
      clockedIntegrand cr cfs cs L γ δ η x E tt τ‖) :
    clockedExprWith e cr cfs cs hI L γ δ η tt E =
      clockedExpr cr cfs cs hI L γ δ η tt E +
        clockedExprWith (fun x => e x - 1) cr cfs cs hI L γ δ η tt E := by
  unfold clockedExprWith clockedExpr
  set I : (D.S.VIdx → (Fin d → ℤ)) → ℂ := fun x => ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    clockedIntegrand cr cfs cs L γ δ η x E tt τ with hIdef
  have h1 : Summable I := hs.of_norm
  have h2 : Summable fun x => (e x - 1) * I x := by
    refine Summable.of_norm_bounded (hs.mul_left B) fun x => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (he x) (norm_nonneg _)
  rw [← h1.tsum_add h2]
  exact tsum_congr fun x => by ring

/-- **Combination lemma (norm form).** -/
theorem norm_clockedExprWith_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℝ)
    {B : Set (Fin 3 → ℝ)} (hB : B ⊆ cell q) {K : Set (Fin 4 → Mom d)} (hK : K.Countable)
    (F F₁ F₂ : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
    (hF : ∀ t ∈ B, ∀ v ∈ K, F t v = F₁ t v + F₂ t v) :
    XNorm00Restr θ B K F ≤
      (cutoffMultiplierConstant θ (cutQ q) + 1) * (XNorm00Restr θ B K F₁ + XNorm00Restr θ B K F₂) := by
  have := XNorm00Restr_tsum_le (ι := Bool) hθ q hB hK
    (fun j => if j then F₁ else F₂) F fun t ht v hv => by
      have h := hasSum_fintype (fun j : Bool => (if j then F₁ else F₂) t v)
      rw [Fintype.sum_bool] at h
      rw [hF t ht v hv]
      simpa using h
  simpa [tsum_fintype, Fintype.sum_bool, add_comm] using this

end WaveTurbulence.DegenVine
