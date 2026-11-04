/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeLocalization

/-!
# Finite tree localization at every fixed positive cell radius

Homogeneity of the actual parent relation transfers the landed unit-ball
cover argument to the radius of the smooth cube partition.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh.LocalizationTree

/-- The same per-branch center count works at every positive localization radius. -/
theorem exists_finite_localization_radius (d : ℕ) : ∃ C : ℕ,
    ∀ R : ℝ, 0 < R → ∀ (t : LocalizationTree) (k0 : Path → Mom d),
      ∃ S : Finset (Path → Mom d), S.card ≤ C ^ t.order ∧
        ∀ k : Path → Mom d, IsDecoration t k → (∀ p ∈ t.leaves, ‖k p - k0 p‖ ≤ R) →
          ∃ c ∈ S, ∀ p ∈ t.nodes, ‖k p - c p‖ ≤ R := by
  classical
  obtain ⟨C, hb⟩ := exists_finite_localization d
  refine ⟨C, ?_⟩
  intro R hR t k0
  obtain ⟨S, hS, hs⟩ := hb t (fun p => R⁻¹ • k0 p)
  refine ⟨S.image (fun c p => R • c p), Finset.card_image_le.trans hS, ?_⟩
  intro k hk hleaf
  let k' : Path → Mom d := fun p => R⁻¹ • k p
  have hk' : IsDecoration t k' := by
    intro p hp
    dsimp only [k']
    rw [hk p hp, smul_add, smul_sub]
  have hleaf' (p : Path) (hp : p ∈ t.leaves) : ‖k' p - R⁻¹ • k0 p‖ ≤ 1 := by
    dsimp only [k']
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_one₀ hR).mpr (hleaf p hp)
  obtain ⟨c, hc, hh⟩ := hs k' hk' hleaf'
  refine ⟨fun p => R • c p, Finset.mem_image_of_mem _ hc, ?_⟩
  intro p hp
  have he : k p - R • c p = R • (k' p - c p) := by
    simp only [k', smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact (mul_le_mul_of_nonneg_left (hh p hp) hR.le).trans_eq (mul_one R)

end WaveTurbulence.Incoh.LocalizationTree
