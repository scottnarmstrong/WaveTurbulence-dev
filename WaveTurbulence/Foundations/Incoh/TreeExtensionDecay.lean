/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreePositiveExtensionBound
public import WaveTurbulence.Foundations.Incoh.TreeInterpolationBound
public import WaveTurbulence.Foundations.Incoh.TreeScaleLoss

/-!
# Incoherence decay for the actual common tree extension

TARGET (incohproof24). The negative and quarter-regularity bounds apply
to one proved global extension. The base constant is dimensional; cutoff
prefactors are absorbed in a threshold independent of the link count.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof24), with the literal source extension and printed `100dηg` loss. -/
theorem exists_treeCausalExtension_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, m ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, 1 ≤ g →
        ∀ Q : Mom d → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ T : (∀ k, TreeClockFibers m (Q k)), ∀ R : RootCoordinates n,
        (∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0) →
        (∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1))) →
        (∀ k, (T k).selection.coordinates.rootLinks = (T 0).selection.coordinates.rootLinks) →
        (∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        (∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        Fourier.mixedFourierNorm00 η
          (R.treeCausalExtension χ L γ δ Q (fun k => (T k).timeDomain)) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * g)) := by
  obtain ⟨Cₙ, hCₙ, hn⟩ := exists_treeCausalExtension_negative_bound d hd
  obtain ⟨Cₚ, hCₚ, hp⟩ := exists_treeCausalExtension_quarter_bound d hd
  let C₀ := max Cₙ Cₚ
  have hC₀ : 0 < C₀ := hCₙ.trans_le (le_max_left _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro m hm η hη hη₁ χ hχ hcχ
  obtain ⟨C₁, hC₁, hn⟩ := hn η hη (by linarith only [hη₁]) χ hχ hcχ
  obtain ⟨C₂, hC₂, hp⟩ := hp m hm χ hχ hcχ
  let C := max C₁ C₂
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold C hη
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨Lₙ, hLₙ, hn⟩ := hn γ hγ hηγ δ hδ D hD
  obtain ⟨Lₚ, hLₚ, hp⟩ := hp γ hγ η hη hηγ δ hδ hδ₁ D hD
  refine ⟨max Lₐ (max Lₙ Lₚ), hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n g hg Q hspan hcount T R hfirst hlast hJ hχroot hχsel
  have hLa : Lₐ ≤ L := (le_max_left _ _).trans hL
  have hLn : Lₙ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLp : Lₚ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLone : 1 ≤ L := hLₐ.trans hLa
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  let A := (C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g)
  let F := R.treeCausalExtension χ L γ δ Q (fun k => (T k).timeDomain)
  let M := ENNReal.ofReal C * ENNReal.ofReal A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcoefₙ : (Cₙ * δ) ^ n ≤ (C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hCₙ.le hδ.le)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le) n
  have hcoefₚ : (Cₚ * δ) ^ n ≤ (C₀ * δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hCₚ.le hδ.le)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le) n
  have hneg : Fourier.mixedFourierNorm00 (-η) F ≤ M := by
    apply (hn L hLn n g Q hspan hcount (fun k => (T k).timeDomain)
      (fun k => (T k).measurableSet_timeDomain) (fun k => (T k).timeDomain_subset_linkBoxes) R).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoefₙ (Real.rpow_nonneg hLpos.le _))
  have hpos : Fourier.mixedFourierNorm00 (1 / 4) F ≤ M * ENNReal.ofReal (L ^ ((d : ℝ) * 2)) := by
    have hbound := hp L hLp n g Q hspan hcount T R hfirst hlast hJ hχroot hχsel
    apply hbound.trans
    have hm : (Cₚ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * 2) ≤
        A * L ^ ((d : ℝ) * 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefₚ (Real.rpow_nonneg hLpos.le _)) (Real.rpow_nonneg hLpos.le _)
    calc
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (A * L ^ ((d : ℝ) * 2)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (ENNReal.ofReal_le_ofReal hm)
      _ = _ := by rw [ENNReal.ofReal_mul hA, ← mul_assoc]
  have hinterp := mixedFourierNorm00_le_of_tree_endpoints (d := d) hη
    (by linarith only [hη₁]) hLone F M hneg hpos
  have hCa : C ≤ L ^ (η * g) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by
      have hgR : 1 ≤ (g : ℝ) := by exact_mod_cast hg
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hgR hη.le))
  apply hinterp.trans
  calc
    _ = ENNReal.ofReal (C * A * L ^ (16 * (d : ℝ) * η)) := by
      dsimp only [M]
      rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (mul_nonneg hC.le hA)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (tree_interpolation_scale_le (by omega) hg (mul_nonneg hC₀.le hδ.le) hη.le hLone hCa)

end WaveTurbulence.Incoh
