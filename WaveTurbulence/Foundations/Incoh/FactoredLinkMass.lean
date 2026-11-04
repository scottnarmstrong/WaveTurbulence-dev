/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LinkMassBounds
public import WaveTurbulence.Foundations.Incoh.ScaleAlgebra

/-!
# Factored full link mass

TARGET (incohproof16): put both contributions over the common kinetic
scale, with the short-time constant still independent of coupling and layers.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The common unnormalized scale of one integrated link. -/
@[expose] def kineticLinkScale (d : ℕ) (γ δ L : ℝ) : ℝ :=
  δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))

/-- The full one-link estimates in factored source exponents. -/
theorem exists_factored_linkMass_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₁ L₀ : ℝ, 0 < C₁ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D →
        (layerLinkMass L (δ * L ^ (2 * γ)) Q ≤
          ENNReal.ofReal (kineticLinkScale d γ δ L *
            (C₀ + C₁ * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)))) ∧
        (Q.IsIncoherent → layerLinkMass L (δ * L ^ (2 * γ)) Q ≤
          ENNReal.ofReal (kineticLinkScale d γ δ L *
            (C₀ * δ⁻¹ * L ^ (-2 * γ) + C₁ * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η)))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_linkMass_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη δ hδ D hD
  obtain ⟨C₁, L₀, hC₁, hL₀, hb⟩ := hb γ hγ η hη δ hδ D hD
  refine ⟨C₁, L₀, hC₁, hL₀, ?_⟩
  intro L hL Q hspan
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hscale : 0 < δ * L ^ (2 * γ) := by positivity
  have hinv : 0 ≤ (δ * L ^ (2 * γ))⁻¹ := (inv_pos.mpr hscale).le
  have hshort : 0 ≤ C₀ * L ^ (2 * d) := by positivity
  have hlong : 0 ≤ C₁ * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) := by positivity
  have hraw := hb L hL Q hspan
  constructor
  · apply hraw.1.trans_eq
    rw [← ENNReal.ofReal_add hshort hlong, ← ENNReal.ofReal_mul hinv]
    congr 1
    rw [← Real.rpow_natCast L (2 * d)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [coherent_scale_identity hLp]
    rw [show 2 * (d : ℝ) - 2 * γ = 2 * ((d : ℝ) - γ) by ring]
    rfl
  · intro hQ
    apply (hraw.2 hQ).trans_eq
    rw [pow_two, ← ENNReal.ofReal_mul hinv, ← ENNReal.ofReal_mul (mul_nonneg hinv hinv),
      ← ENNReal.ofReal_mul hinv, ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hinv hinv) hshort) (mul_nonneg hinv hlong)]
    congr 1
    rw [← pow_two, ← Real.rpow_natCast L (2 * d)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [incoherent_scale_identity hLp]
    rw [show 2 * (d : ℝ) - 2 * γ = 2 * ((d : ℝ) - γ) by ring]
    rfl

end WaveTurbulence.Incoh
