/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.ZFixedPoint
/-! TARGET S1: actual b-solutions from the exact fixedpoint gate's contraction clauses. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
universe u

theorem fixedpoint_gate_exists_b (P : WTParams) (hF : FixedpointBody.{u} P)
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (p : ℕ) (hp : p < P.D)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (hA : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) :
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F', (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
        ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ≤
          jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (3 * P.N (p + 1))) ∧
      ∃ b ∈ ZSpace (d := P.d) P.L (5 / 4 * P.Lambda (p + 1)) p,
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) b ≤ ENNReal.ofReal (Real.exp (-(10 * P.N (p + 1) : ℝ))) ∧
        b = (fun (t : ZTime p) n => Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) 0 b t n) +
          (fun (t : ZTime p) n => Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) 1 b t n) +
          (fun (t : ZTime p) n => Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) 2 b t n) +
          (fun (t : ZTime p) n => Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) 3 b t n) := by
  obtain ⟨F', hsub, hmeas, hsym, hprob, hpoint⟩ := hF Ω μ g hG p hp a Fev R E Et hA
  refine ⟨F', hsub, hmeas, hsym, hprob, ?_⟩
  intro ω hω
  have H := hpoint ω hω
  dsimp only at H
  refine ⟨H.1, ?_⟩
  let ℒ := fun (j : ℕ) (b : ZTime p → (Fin P.d → ℤ) → ℂ) (t : ZTime p) n =>
    Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) j b t n
  let Rel := fun b c => c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hm : ∀ b ∈ ZSpace P.L (5 / 4 * P.Lambda (p + 1)) p,
      ZNorm P.L (5 / 4 * P.Lambda (p + 1)) b ≤ ENNReal.ofReal (Real.exp (-(10 * P.N (p + 1) : ℝ))) →
      ∃ c ∈ ZSpace P.L (5 / 4 * P.Lambda (p + 1)) p, Rel b c ∧
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c ≤ ENNReal.ofReal (Real.exp (-(10 * P.N (p + 1) : ℝ))) :=
    H.2.2.2.2.2.1
  obtain ⟨b, hb, hnorm, heq⟩ := exists_Z_fixedPoint P.L (5 / 4 * P.Lambda (p + 1))
    (Real.exp (-(10 * P.N (p + 1) : ℝ))) (Real.exp_nonneg _) Rel hm (by
      intro b hb b' hb' c hc c' hc' hnb hnb' hbc hb'c'
      rw [hhalf]
      exact H.2.2.2.2.2.2 b hb b' hb' c hc c' hc' hnb hnb' hbc hb'c')
  refine ⟨b, hb, hnorm, ?_⟩
  change b = ℒ 0 b + ℒ 1 b + ℒ 2 b + ℒ 3 b
  have h : b = (ℒ 0 b + ℒ 2 b + ℒ 3 b) + ℒ 1 b := (sub_eq_iff_eq_add).mp heq
  exact h.trans (by abel)

end WaveTurbulence.Induct
