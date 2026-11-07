/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintSigned

/-! # `SumintSigned` at the doubled step `δ' = 2δ` (V5 obligation 6)

V4 proved that the actual vine-chain phase is `signedPhase` at `δ' = 2δ` (the factor 2 of
`ζΩ = 2⟨x,y⟩`).  The prefix `WTPrefixA` ties `τ* = 𝔇δ`, so the instance for the step `2δ` with the
same number `𝔇` of unit windows has `τ*' = 2τ*`.  The conclusion of `sumint` does not involve the
solution `φ`; the prefix quantifies over all `(φin, τ*, φ)`, so we instantiate it at the trivial
solution `φ = 0` on `[0, 2τ*]`.  The orders `N_p` depend only on `(d, L, 𝔇)`.
No statement is changed: `SumintSignedDoubled` is a consequence of `SumintSigned`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 MeasureTheory Finset Set
open scoped ENNReal SchwartzMap

/-- `SumintSigned` with the phase at the step `2δ` and the right-hand side still in terms of `δ`
(`(C₁ (2δ)^{-1/2})^M ≤ (C₁ δ^{-1/2})^M`). -/
def SumintSignedDoubled : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I) (coreFirstSign coreSign : Fin D.S.I → ℤˣ), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 →
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K
          (fun tt v => signedExpr D coreFirstSign coreSign hI P.L P.γ (2 * P.δ) P.η tt v) ≤
        ENNReal.ofReal (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7))

/-- The trivial solution `φ ≡ 0` of (WKE) on any `[0, τ]`. -/
theorem isWKESolution_zero {d : ℕ} (τ : ℝ) :
    IsWKESolution (0 : 𝓢(Mom d, ℝ)) τ (fun _ => 0) := by
  refine ⟨continuousOn_const, rfl, fun s _ k => ?_⟩
  have h : collisionOp (0 : Mom d → ℝ) 0 0 k = 0 := by simp [collisionOp]
  have h2 := hasDerivWithinAt_const s (Icc 0 τ) (0 : ℝ)
  simpa [h] using h2

/-- **V5 obligation 6/7 resolved without changing a statement.** `SumintSigned` implies its
version at the doubled step `2δ`: instantiate the prefix at `φin = 0`, `φ = 0`, `τ*' = 2τ*`,
`δ' = 2δ`, the same `𝔇` and the same `L`. -/
theorem sumintSignedDoubled_of_sumintSigned (hS : SumintSigned) : SumintSignedDoubled := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hS d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη' A hA φin hφin τstar hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, hν⟩ := hη η hη' A hA (0 : 𝓢(Mom d, ℝ)) (fun k => le_refl _) (2 * τstar)
    (by linarith) (fun _ => 0) (isWKESolution_zero _)
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν' => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hν ν hν'
  refine ⟨δ₀ / 2, by linarith, fun δ hδ' D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, hL⟩ := hδ (2 * δ) ⟨by linarith [hδ'.1], by linarith [hδ'.2]⟩ D hD
    (by rw [hτD]; ring)
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hLL => ?_⟩
  intro D' hI cfs cs hAdm hM
  have hN : ∀ k, (WTParams.mk d γ η φin τstar φ C₁ ν δ D C₂ L).Rdown k =
      (WTParams.mk d γ η (0 : 𝓢(Mom d, ℝ)) (2 * τstar) (fun _ => 0) C₁ ν (2 * δ) D C₂ L).Rdown k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [WTParams.Rdown, ih]
  have hM' : D'.S.M ≤ (WTParams.mk d γ η (0 : 𝓢(Mom d, ℝ)) (2 * τstar) (fun _ => 0) C₁ ν (2 * δ) D C₂ L).N 1 ^ 4 := by
    have := hM
    simp only [WTParams.N, WTParams.R] at this ⊢
    rwa [← hN]
  have key := hL L hLL D' hI cfs cs hAdm hM'
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hδpos : 0 < δ := hδ'.1
  have hC : 0 < C₁ := by linarith
  have hpar : 0 ≤ ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D'.param v) :=
    Real.iSup_nonneg (fun v => Real.sqrt_nonneg _)
  have hrpow : (2 * δ) ^ (-(1 : ℝ) / 2) ≤ δ ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hδpos (by linarith) (by norm_num)
  have hX : 0 ≤ C₁ * (2 * δ) ^ (-(1 : ℝ) / 2) := by positivity
  have hpow : (C₁ * (2 * δ) ^ (-(1 : ℝ) / 2)) ^ D'.S.M ≤ (C₁ * δ ^ (-(1 : ℝ) / 2)) ^ D'.S.M :=
    pow_le_pow_left₀ hX (by gcongr) _
  have hL0 : 0 ≤ L ^ (((D'.S.M : ℝ) * (d - γ) -
            η ^ 2 * ((Finset.univ.filter fun i => D'.S.nor i = false).card + D'.M₁) -
            η ^ 8 * D'.M₀ + η ^ 7)) := Real.rpow_nonneg (by linarith) _
  have hP : 0 ≤ C₁ * (⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D'.param v)) ^ (η ^ 6) :=
    mul_nonneg hC.le (Real.rpow_nonneg hpar _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hP) hL0

end WaveTurbulence.VineEstS3
