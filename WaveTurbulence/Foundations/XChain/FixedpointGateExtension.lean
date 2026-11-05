/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedpointSolution
public import WaveTurbulence.Foundations.XChain.FixedpointGlue
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! Pointwise solution extension on the very same event supplied by the exact fixedpoint gate. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
universe u

theorem fixedpoint_gate_solution_extension (P : WTParams) (hF : FixedpointBody.{u} P)
    (hd : 1 ≤ P.d) (hL : 0 < P.L)
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (p : ℕ) (hp : p < P.D)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (hA : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) :
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F', ∃ a' : ℝ → (Fin P.d → ℤ) → ℂ,
        IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) a' ∧
        (∀ t ∈ Icc (0 : ℝ) p, a' t = a ω t) ∧
        ∀ b, IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) b →
          ∀ t ∈ Icc (0 : ℝ) (p + 1), b t = a' t := by
  obtain ⟨F', hsub, hmeas, hsym, hprob, hpoint⟩ :=
    fixedpoint_gate_exists_b P hF Ω μ g hG p hp a Fev R E Et hA
  refine ⟨F', hsub, hmeas, hsym, hprob, fun ω hω => ?_⟩
  obtain ⟨htr, b, hb, _, hfp⟩ := hpoint ω hω
  have ha := SysAPI.AnsatzAt.isASolution (hA p le_rfl) (hsub hω)
  let a' := fun s => if s ≤ (p : ℝ) then a ω s else
    fun n => aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) s n +
      IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s n
  have hsol : IsASolution P.L P.γ P.δ (p + 1) (initialCoeff P.L P.φin g ω) a' :=
    fixedpoint_glue P.L P.γ P.δ hL (P.N (p + 1)) ha hb (fixedpoint_weight_ge P hd hp)
      (fixedpoint_weight_le_tree_weight P p) htr hfp
  refine ⟨a', hsol, fun t ht => ?_, fun b hb => SysAPI.IsASolution.unique hL hb hsol⟩
  simp only [a', ite_eq_left ht.2]

end WaveTurbulence.Induct
