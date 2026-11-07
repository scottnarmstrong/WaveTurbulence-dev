/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedBound
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain

/-! # The engine from restriction-norm bounds of the clocked weights

If the weight of each row `ρ` is continuous in its clock pair and has `XNormRestr (6η⁶) (30d) N_ρ (B_ρ) univ`
norm `< β_ρ` on a box `B_ρ ⊆ Q_{q_ρ}` containing all clock pairs of the time domain, then the engine bound holds
with `∏_ρ C β_ρ`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS2 Finset
  MeasureTheory
open scoped ENNReal

/-- **The engine from restriction norms.** -/
theorem clockedBound_of_restr {A : ℝ} {P : WTParams} (hdb : SumintDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintDatum P.d} (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ)
    (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
    (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
    (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
    (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
    (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
    (hβ : ∀ ρ, β ρ ≠ ⊤)
    (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ) :
    ∃ Cfs : ℝ≥0∞, Cfs ≠ ⊤ ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExpr cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
            sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) *
          ∏ ρ, (Cfs * β ρ) := by
  classical
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  have hΛ : 30 * P.d ≠ 0 := by omega
  obtain ⟨Ca, hCa, hfa⟩ := fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 30 * P.d) hΛ
  obtain ⟨Cb, hCb, hfb⟩ := fs_expansion (r := 2) (d := P.d) hθfs (Λ₂ := 0) hΛ
  set Cm := max Ca Cb with hCm
  have hCmtop : Cm ≠ ⊤ := by
    rw [hCm]; exact ne_of_lt (max_lt hCa.lt_top hCb.lt_top)
  have hrow : ∀ ρ : Row D, ∃ c : (Fin 2 → ℤ) → Mom P.d → ℂ,
      (∀ t ∈ Bx ρ, ∀ k, HasSum (fun m : Fin 2 → ℤ => c m k * fsPhase m t) (cr.W ρ t k)) ∧
      ∑' m : Fin 2 → ℤ, maxBracketPow (6 * P.η ^ 6) (half m) * SNorm (30 * P.d) (rowOrder D ρ) (c m) ≤
        Cm * β ρ := by
    intro ρ
    cases ρ with
    | inl v =>
      obtain ⟨c, h1, h2⟩ := hfa (qx (Sum.inl v)) (Bx (Sum.inl v)) Set.univ (cr.W (Sum.inl v)) (β (Sum.inl v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left (le_max_left _ _) _)⟩
    | inr v =>
      obtain ⟨c, h1, h2⟩ := hfb (qx (Sum.inr v)) (Bx (Sum.inr v)) Set.univ (cr.W (Sum.inr v)) (β (Sum.inr v))
        (hbox _) (hint _) (fun k _ => hcont _ k) (hres _)
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k),
        h2.trans (mul_le_mul_left (le_max_right _ _) _)⟩
  choose c hc hcb using hrow
  let M : ClockedModes D (6 * P.η ^ 6) :=
    { c := c, b := fun ρ => Cm * β ρ,
      b_ne_top := fun ρ => ENNReal.mul_ne_top hCmtop (hβ ρ),
      fs_bound := hcb }
  refine ⟨Cm, hCmtop, ?_⟩
  exact clockedBound hdb hL hη0 hη1 hC1 hδ hd1 hI cfs cs hno hbad hAdm hM cr M
    (fun tt htt τ hτ ρ k => hc ρ _ (hclock tt htt τ hτ ρ) k)

end WaveTurbulence.VineEstS3.Eng
