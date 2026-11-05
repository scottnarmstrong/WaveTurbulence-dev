/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The original layer-zero source phase coefficient is uniformly bounded -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set

/-- Every original source phase has modulus one, with no resonance premise. -/
theorem tree_norm_phaseProd {d w : ℕ} (L γ δ : ℝ) (G : Garden w)
    (κ : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    ‖phaseProd L γ δ G κ τ‖ = 1 := by
  simp only [phaseProd, norm_prod, Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one]

/-- In layer zero every integrated source clock lies in the unit interval. The bound
is valid at every endpoint and for the empty tree, independently of all physical data. -/
theorem tree_norm_phaseIntegral_le_one {d w : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (h0 : ∀ a, LG.layer a = 0) (up : GBranch LG.garden.tree → ℝ) (s s' : ℝ)
    (κ : GNode LG.garden.tree → Mom d) :
    ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s' κ‖ ≤ 1 := by
  classical
  let U : Set (LG.garden.FreeBranch → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  have hU : MeasurableSet U := measurableSet_Icc
  have hv : volume U = 1 := by
    simp [U, Real.volume_Icc_pi]
  have hi : Integrable (U.indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hU).mpr
      (integrableOn_const (C := (1:ℝ)) (by rw [hv]; exact ENNReal.one_ne_top))
  have hb (τ : LG.garden.FreeBranch → ℝ) :
      ‖(kDomain LG up s).indicator (phaseProd L γ δ LG.garden κ)
        (LG.garden.extendTime s' τ)‖ ≤ U.indicator (fun _ => (1:ℝ)) τ := by
    by_cases hτ : LG.garden.extendTime s' τ ∈ kDomain LG up s
    · have hτU : τ ∈ U := by
        constructor
        · intro b
          change (0:ℝ) ≤ τ b
          have hh := (hτ b.val).1
          simp only [Garden.extendTime, dite_eq_right b.property, h0, Nat.cast_zero] at hh
          change (0:ℝ) < τ b at hh
          exact hh.le
        · intro b
          change τ b ≤ (1:ℝ)
          have hh := (hτ b.val).2.1
          simp only [Garden.extendTime, dite_eq_right b.property, h0, Nat.cast_zero, zero_add] at hh
          change τ b < (1:ℝ) at hh
          exact hh.le
      rw [indicator_of_mem hτ, indicator_of_mem hτU, tree_norm_phaseProd]
    · rw [indicator_of_notMem hτ, norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  apply (norm_integral_le_of_norm_le hi (ae_of_all _ hb)).trans_eq
  rw [integral_indicator hU, setIntegral_const, Measure.real, hv]
  simp

end WaveTurbulence.RegAsymp
