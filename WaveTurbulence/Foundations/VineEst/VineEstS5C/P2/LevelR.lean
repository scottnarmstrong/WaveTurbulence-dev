/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Level
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemAe

/-! # P2: single-level bounds with a remainder row (clause (d); step 3)

`level_SR` (separated 𝒦, remainder ℒ), `level_RS` (remainder 𝒦, separated ℒ), `level_RR` (both remainders).  The remainder rows are
`remRow_ae_exists` rows: `W c r k = f ![c 0, c 1] k` for a kernel `f` that agrees (a.e. in time on the box, for all `k`) with a function
continuous in time, with `XNormRestr (6 η^6) wN (rowOrder) B univ f < b`; `D.wN = Λ₁`, `D.wDec = Λ₂` are fixed numerals. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

theorem level_SR {A : ℝ} {P : WTParams}
    (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    (hθ : (0 : ℝ) ≤ 6 * P.η ^ 6) (hθ' : 6 * P.η ^ 6 ≤ 1 - P.η) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C CK CL : ℝ≥0∞, C ≠ ⊤ ∧ CK ≠ ⊤ ∧ CL ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (hwN : D.wN = Λ₁) (hwDec : D.wDec = Λ₂)
    (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k))
    (vK : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (qK : Fin 2 → ℝ) (BK : Set (Fin 2 → ℝ)) (JK : (Fin 2 → ℝ) → ℂ)
    (βK : ℝ≥0∞) (MK : Mom P.d → Mom P.d → ℂ)
    (hβK : βK ≠ ⊤) (hcK : BK ⊆ cell qK) (iK : BK ⊆ closure (interior BK))
    (hJK : XNorm00Restr (V := Unit) (1 - P.η) BK Set.univ (fun ts _ => JK ts) < βK)
    (hMK : (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v₀)) (MK r)) ≠ ⊤)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK)
    (vL : Fin 2 → D.S.TVar) (hvL : Function.Injective vL) (qL : Fin 2 → ℝ) (BL : Set (Fin 2 → ℝ))
    (fL fL' : (Fin 2 → ℝ) → Mom P.d → ℂ) (bL : ℝ≥0∞)
    (hbL : bL ≠ ⊤) (hcL : BL ⊆ cell qL) (iL : BL ⊆ closure (interior BL)) (hcontL : ∀ k, Continuous fun t => fL' t k)
    (haeL : ∀ᵐ t, t ∈ BL → ∀ k, fL t k = fL' t k)
    (hXL : XNormRestr (6 * P.η ^ 6) Λ₁ 0 BL Set.univ fL < bL)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ BL),
    ∃ K : RowData D (6 * P.η ^ 6) (Sum.inl v₀), ∃ L : RowData D (6 * P.η ^ 6) (Sum.inr v₀),
      (∀ c r k, K.W c r k = JK ![c 0, c 1] * MK r k) ∧ (∀ i, K.slot i = Sum.inl (![vK 0, vK 1, vK 0] i)) ∧
      (∀ c r k, L.W c r k = fL ![c 0, c 1] k) ∧ (∀ i, L.slot i = Sum.inl (![vL 0, vL 1, vL 0] i)) ∧
      K.Ae hI ∧ L.Ae hI ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ((C * βK * ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inl v₀)) (MK r)) * (CL * bL) *
          ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ) := by
  obtain ⟨C, hC, hrow⟩ := sepRow2_exists (d := P.d) hθ hθ'
  obtain ⟨CK, hCK, hremK⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ Λ₂ hΛ
  obtain ⟨CL, hCL, hremL⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ 0 hΛ
  refine ⟨C, CK, CL, hC, hCK, hCL, fun {D} hI Mx hη3 Cph hCph0 hCph hreg hAdm hM hwN hwDec cr₀ M₀ v₀ h0 vK hvK qK BK JK βK MK hβK hcK iK hJK hMK hclK vL hvL qL BL fL fL' bL hbL hcL iL hcontL haeL hXL hclL => ?_⟩
  obtain ⟨K, hKW, hKs, hKb, hKae⟩ := hrow D hI (Sum.inl v₀) vK hvK qK BK JK βK MK hβK hcK iK hJK hMK
    (fun w hw => absurd hw (by simp)) hclK
  obtain ⟨L, hLW, hLs, hLb, hLae⟩ := hremL D hI (Sum.inr v₀) hwN (by simp [rowOrder]) vL hvL qL BL fL fL' bL hbL hcL iL
    hcontL haeL hXL hclL
  refine ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, ?_⟩
  have := vineLevel_bound hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ K L hKae hLae h0
  rwa [hKb, hLb] at this

theorem level_RS {A : ℝ} {P : WTParams}
    (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    (hθ : (0 : ℝ) ≤ 6 * P.η ^ 6) (hθ' : 6 * P.η ^ 6 ≤ 1 - P.η) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C CK CL : ℝ≥0∞, C ≠ ⊤ ∧ CK ≠ ⊤ ∧ CL ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (hwN : D.wN = Λ₁) (hwDec : D.wDec = Λ₂)
    (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k))
    (vK : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (qK : Fin 2 → ℝ) (BK : Set (Fin 2 → ℝ))
    (fK fK' : (Fin 2 → ℝ) → Mom P.d → ℂ) (bK : ℝ≥0∞)
    (hbK : bK ≠ ⊤) (hcK : BK ⊆ cell qK) (iK : BK ⊆ closure (interior BK)) (hcontK : ∀ k, Continuous fun t => fK' t k)
    (haeK : ∀ᵐ t, t ∈ BK → ∀ k, fK t k = fK' t k)
    (hXK : XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ BK Set.univ fK < bK)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK)
    (vL : Fin 2 → D.S.TVar) (hvL : Function.Injective vL) (qL : Fin 2 → ℝ) (BL : Set (Fin 2 → ℝ)) (JL : (Fin 2 → ℝ) → ℂ)
    (βL : ℝ≥0∞) (ML : Mom P.d → Mom P.d → ℂ)
    (hβL : βL ≠ ⊤) (hcL : BL ⊆ cell qL) (iL : BL ⊆ closure (interior BL))
    (hJL : XNorm00Restr (V := Unit) (1 - P.η) BL Set.univ (fun ts _ => JL ts) < βL)
    (hML : (⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v₀)) (ML r)) ≠ ⊤)
    (hind : ∀ r r' k : Mom P.d, ML r k = ML r' k)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ BL),
    ∃ K : RowData D (6 * P.η ^ 6) (Sum.inl v₀), ∃ L : RowData D (6 * P.η ^ 6) (Sum.inr v₀),
      (∀ c r k, K.W c r k = fK ![c 0, c 1] k) ∧ (∀ i, K.slot i = Sum.inl (![vK 0, vK 1, vK 0] i)) ∧
      (∀ c r k, L.W c r k = JL ![c 0, c 1] * ML r k) ∧ (∀ i, L.slot i = Sum.inl (![vL 0, vL 1, vL 0] i)) ∧
      K.Ae hI ∧ L.Ae hI ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ((CK * bK) * (C * βL * ⨆ r : Mom P.d, SNorm D.wN (rowOrder D (Sum.inr v₀)) (ML r)) *
          ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ) := by
  obtain ⟨C, hC, hrow⟩ := sepRow2_exists (d := P.d) hθ hθ'
  obtain ⟨CK, hCK, hremK⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ Λ₂ hΛ
  obtain ⟨CL, hCL, hremL⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ 0 hΛ
  refine ⟨C, CK, CL, hC, hCK, hCL, fun {D} hI Mx hη3 Cph hCph0 hCph hreg hAdm hM hwN hwDec cr₀ M₀ v₀ h0 vK hvK qK BK fK fK' bK hbK hcK iK hcontK haeK hXK hclK vL hvL qL BL JL βL ML hβL hcL iL hJL hML hind hclL => ?_⟩
  obtain ⟨K, hKW, hKs, hKb, hKae⟩ := hremK D hI (Sum.inl v₀) hwN (by simp [rowOrder, hwDec]) vK hvK qK BK fK fK' bK hbK hcK iK
    hcontK haeK hXK hclK
  obtain ⟨L, hLW, hLs, hLb, hLae⟩ := hrow D hI (Sum.inr v₀) vL hvL qL BL JL βL ML hβL hcL iL hJL hML
    (fun w hw => by cases hw; exact hind) hclL
  refine ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, ?_⟩
  have := vineLevel_bound hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ K L hKae hLae h0
  rwa [hKb, hLb] at this

theorem level_RR {A : ℝ} {P : WTParams}
    (hdb : SumintMixParDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    (hθ : (0 : ℝ) ≤ 6 * P.η ^ 6) (hθ' : 6 * P.η ^ 6 ≤ 1 - P.η) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C CK CL : ℝ≥0∞, C ≠ ⊤ ∧ CK ≠ ⊤ ∧ CL ≠ ⊤ ∧ ∀ {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (hwN : D.wN = Λ₁) (hwDec : D.wDec = Λ₂)
    (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k))
    (vK : Fin 2 → D.S.TVar) (hvK : Function.Injective vK) (qK : Fin 2 → ℝ) (BK : Set (Fin 2 → ℝ))
    (fK fK' : (Fin 2 → ℝ) → Mom P.d → ℂ) (bK : ℝ≥0∞)
    (hbK : bK ≠ ⊤) (hcK : BK ⊆ cell qK) (iK : BK ⊆ closure (interior BK)) (hcontK : ∀ k, Continuous fun t => fK' t k)
    (haeK : ∀ᵐ t, t ∈ BK → ∀ k, fK t k = fK' t k)
    (hXK : XNormRestr (6 * P.η ^ 6) Λ₁ Λ₂ BK Set.univ fK < bK)
    (hclK : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vK i)) ∈ BK)
    (vL : Fin 2 → D.S.TVar) (hvL : Function.Injective vL) (qL : Fin 2 → ℝ) (BL : Set (Fin 2 → ℝ))
    (fL fL' : (Fin 2 → ℝ) → Mom P.d → ℂ) (bL : ℝ≥0∞)
    (hbL : bL ≠ ⊤) (hcL : BL ⊆ cell qL) (iL : BL ⊆ closure (interior BL)) (hcontL : ∀ k, Continuous fun t => fL' t k)
    (haeL : ∀ᵐ t, t ∈ BL → ∀ k, fL t k = fL' t k)
    (hXL : XNormRestr (6 * P.η ^ 6) Λ₁ 0 BL Set.univ fL < bL)
    (hclL : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (vL i)) ∈ BL),
    ∃ K : RowData D (6 * P.η ^ 6) (Sum.inl v₀), ∃ L : RowData D (6 * P.η ^ 6) (Sum.inr v₀),
      (∀ c r k, K.W c r k = fK ![c 0, c 1] k) ∧ (∀ i, K.slot i = Sum.inl (![vK 0, vK 1, vK 0] i)) ∧
      (∀ c r k, L.W c r k = fL ![c 0, c 1] k) ∧ (∀ i, L.slot i = Sum.inl (![vL 0, vL 1, vL 0] i)) ∧
      K.Ae hI ∧ L.Ae hI ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
          sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ((CK * bK) * (CL * bL) *
          ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ) := by
  obtain ⟨C, hC, hrow⟩ := sepRow2_exists (d := P.d) hθ hθ'
  obtain ⟨CK, hCK, hremK⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ Λ₂ hΛ
  obtain ⟨CL, hCL, hremL⟩ := remRow_ae_exists (d := P.d) hθ Λ₁ 0 hΛ
  refine ⟨C, CK, CL, hC, hCK, hCL, fun {D} hI Mx hη3 Cph hCph0 hCph hreg hAdm hM hwN hwDec cr₀ M₀ v₀ h0 vK hvK qK BK fK fK' bK hbK hcK iK hcontK haeK hXK hclK vL hvL qL BL fL fL' bL hbL hcL iL hcontL haeL hXL hclL => ?_⟩
  obtain ⟨K, hKW, hKs, hKb, hKae⟩ := hremK D hI (Sum.inl v₀) hwN (by simp [rowOrder, hwDec]) vK hvK qK BK fK fK' bK hbK hcK iK
    hcontK haeK hXK hclK
  obtain ⟨L, hLW, hLs, hLb, hLae⟩ := hremL D hI (Sum.inr v₀) hwN (by simp [rowOrder]) vL hvL qL BL fL fL' bL hbL hcL iL
    hcontL haeL hXL hclL
  refine ⟨K, L, hKW, hKs, hLW, hLs, hKae, hLae, ?_⟩
  have := vineLevel_bound hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ K L hKae hLae h0
  rwa [hKb, hLb] at this

end WaveTurbulence.VineEstS5C.P2
