/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Merge

/-! # P2: the single-level engine bound (V5 Step 4d part C, packet P2, item 4)

**`vineLevel_bound`**: for a `SumintPar` datum `D`, an ambient family `(cr₀, M₀)` of weight rows and mode families (the rows
of the OTHER vines, supplied by P3) and two row data `K` (𝒦 row, `inl v₀`) and `L` (ℒ row, `inr v₀`) of the vine `v₀` with
a.e. mode expansions, the clocked expression with the rows of `v₀` replaced by `K, L` obeys the `clockedBoundMix3`
bound with `∏ ρ, M.b ρ = K.b * L.b * ∏_{ρ ∉ {𝒦 v₀, ℒ v₀}} M₀.b ρ`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ}

/-- **The single-level engine bound.**  The hypotheses are those of `clockedBoundMix3` (`Cph` bounds the kind-2 phase on the
time domain, `hAdm` is `Admissible` for every weight family with the `WeightBounds` of the datum, `hM` the count of vector
indices), with the clocked rows `mergeCR cr₀ v₀ K L` and the mode families `mergeCM M₀ v₀ K L`. -/
theorem vineLevel_bound {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (K : RowData D (6 * P.η ^ 6) (Sum.inl v₀)) (L : RowData D (6 * P.η ^ 6) (Sum.inr v₀))
    (hK : K.Ae hI) (hLr : L.Ae hI)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k)) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        (K.b * L.b * ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ) := by
  have h := clockedBoundMix3 hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM (mergeCR cr₀ v₀ K L)
    (mergeCM M₀ v₀ K L) (merge_hser cr₀ M₀ v₀ K L hI hK hLr h0)
  rwa [prod_mergeCM_b] at h

end WaveTurbulence.VineEstS5C.P2
