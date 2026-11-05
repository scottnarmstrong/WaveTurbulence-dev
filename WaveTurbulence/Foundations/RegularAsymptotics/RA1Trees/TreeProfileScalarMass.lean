/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteProfileScalar

/-! # Actual uniform temporal mass of the original Wick-weighted local tree profiles -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh ClassJR ApproxNT WithLp

/-- Actual joint measurability of the source time-frequency lattice profile in both
modulation arrays, with its unchanged arbitrary fixed original lattice weight. -/
theorem stronglyMeasurable_treeProfileArrayScalar_joint {d n : ℕ} (L μ : ℝ)
    (W : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : StronglyMeasurable (Function.uncurry C)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      treeProfileArrayScalar L μ W z p.2.1 p.2.2 J C p.1) := by
  apply Measurable.stronglyMeasurable
  unfold treeProfileArrayScalar treeHalfCellLatticeScalar
  apply Measurable.tsum
  intro g
  have ha : Measurable (fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
      halfCellAmplitude z p.2.1 p.2.2 (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))) :=
    (continuous_halfCellAmplitude_joint z).measurable.comp
      (f := fun p : (ℝ × ℝ) × ((Fin n → Mom d) × (Fin n → Mom d)) =>
        (p.2,((fun j => latticePoint L (g.1 j)),(fun j => latticePoint L (g.2 j)))))
      (measurable_snd.prodMk measurable_const)
  unfold resProfile
  exact ha.mul (measurable_const.mul (measurable_const.mul
    (hC.comp_measurable (measurable_const.prodMk measurable_fst)).measurable))

/-- Original qualitative symbol regularity gives one integrable temporal envelope
uniform over all actual half cells and both modulations. Used only for exact exchanges. -/
theorem treeProfileArrayScalar_uniform_integrable_envelope {d n : ℕ} {L : ℝ}
    (hL : 1 ≤ L) (μ : ℝ)
    (W : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ g, ‖W g‖ ≤ D) (J : Finset (Fin n))
    {C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    ∃ E : (ℝ × ℝ) → ℝ, Measurable E ∧ (∀ lam, 0 ≤ E lam) ∧ Integrable E ∧
      ∀ᵐ lam, ∀ z β γ, ‖treeProfileArrayScalar L μ W z β γ J C lam‖ ≤ E lam := by
  obtain ⟨E,hmE,hpE,hiE,hbE⟩ := tree_regular_resProfile_uniform_integrable_envelope J hC
  let Q := (2^d*L^d)^(2*n)*D
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨fun lam => Q*E lam,measurable_const.mul hmE,
    fun lam => mul_nonneg hQ (hpE lam),hiE.const_mul Q,?_⟩
  filter_upwards [hbE] with lam hlam
  intro z β γ
  have hbound (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :
      ‖W g * resProfile J (fun Ω => C (ofLp Ω) lam)
        (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))‖ ≤ D*E lam := by
    rw [norm_mul]
    exact mul_le_mul (hW g) (hlam _) (norm_nonneg _) hD
  exact (treeHalfCellLatticeScalar_norm_le hL _ (mul_nonneg hD (hpE lam)) hbound z β γ).trans_eq
    (by dsimp only [Q]; ring)

end WaveTurbulence.RegAsymp
