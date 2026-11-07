/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Level
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Rows

/-! # P2: single-level bound, both vine rows separated (pieces (a), (b); K row and L row of `sepRow2` type) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

/-- **Single-level bound, separated 𝒦 row and separated ℒ row.**  The rows are `J_K(c₀,c₁) M_K(r,k)` at the clocks
`(τ_{vK 0}, τ_{vK 1})` and `J_L(c₀,c₁) M_L(k)` at `(τ_{vL 0}, τ_{vL 1})`; the bound is the engine constant times
`(C β_K S_K)(C β_L S_L) ∏_{other rows} b`. -/
theorem level_SS {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    (hθ : (0 : ℝ) ≤ 6 * P.η ^ 6) (hθ' : 6 * P.η ^ 6 ≤ 1 - P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k))
    (vK vL : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (hvL : Function.Injective vL)
    (qK qL : Fin 2 → ℝ) (BK BL : Set (Fin 2 → ℝ)) (JK JL : (Fin 2 → ℝ) → ℂ) (βK βL : ℝ≥0∞)
    (MK : Mom P.d → Mom P.d → ℂ) (ML : Mom P.d → Mom P.d → ℂ),
    βK ≠ ⊤ → βL ≠ ⊤ → BK ⊆ cell qK → BK ⊆ closure (interior BK) → BL ⊆ cell qL → BL ⊆ closure (interior BL) →
    XNorm00Restr (V := Unit) (1 - P.η) BK Set.univ (fun ts _ => JK ts) < βK →
    XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < βL →
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v₀)) (MK r)) ≠ ⊤ →
    (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v₀)) (ML r)) ≠ ⊤ →
    (∀ r r' k : Mom P.d, ML r k = ML r' k) →
    (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK) →
    (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ BL) →
    ∃ K : RowData D (6 * P.η ^ 6) (Sum.inl v₀), ∃ L : RowData D (6 * P.η ^ 6) (Sum.inr v₀),
      (∀ c r k, K.W c r k = JK ![c 0, c 1] * MK r k) ∧ (∀ c r k, L.W c r k = JL ![c 0, c 1] * ML r k) ∧
      (∀ i, K.slot i = Sum.inl (![vK 0, vK 1, vK 0] i)) ∧ (∀ i, L.slot i = Sum.inl (![vL 0, vL 1, vL 0] i)) ∧
      K.Ae hI ∧ L.Ae hI ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ((C * βK * ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v₀)) (MK r)) *
          (C * βL * ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v₀)) (ML r)) *
          ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ) := by
  obtain ⟨C, hC, hrow⟩ := sepRow2_exists (d := P.d) hθ hθ'
  refine ⟨C, hC, fun {D} hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ h0 vK vL hvK hvL qK qL BK BL JK JL βK βL MK ML
    hβK hβL hcK iK hcL iL hJK hJL hMK hML hind hclK hclL => ?_⟩
  obtain ⟨K, hKW, hKs, hKb, hKae⟩ := hrow D hI (Sum.inl v₀) vK hvK qK BK JK βK MK hβK hcK iK hJK hMK
    (fun w hw => absurd hw (by simp)) hclK
  obtain ⟨L, hLW, hLs, hLb, hLae⟩ := hrow D hI (Sum.inr v₀) vL hvL qL BL JL βL ML hβL hcL iL hJL hML
    (fun w hw => by cases hw; exact hind) hclL
  refine ⟨K, L, hKW, hLW, hKs, hLs, hKae, hLae, ?_⟩
  have := vineLevel_bound hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ K L hKae hLae h0
  rwa [hKb, hLb] at this

end WaveTurbulence.VineEstS5C.P2
