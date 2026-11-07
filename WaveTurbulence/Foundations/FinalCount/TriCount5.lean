/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCount4
/-! Triangles, part 14 (FINALCOUNT-G2): the triple count when one or both cuts are `α`-cuts (`ΔF = 1, 0`;
DH23 L1794--L1796). The `α` gaps lie in a ball `‖gap - r₀‖ ≤ ρ` (`ρ = 2R`, or `L^{-50η} R` for `ι ≠ 0`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem gap_mem_alphaN (L : ℝ) (hL : 0 < L) (w : Mom d) (j : Fin 3) (r₀ : Mom d) (ρ : ℝ) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x, κ (M.mate x) = κ x) (hb : ‖Molecule.gapAt L w κ (T.a j) (T.b j) - r₀‖ ≤ ρ) :
    T.triZ κ (j - 1) - T.triZ κ j ∈ alphaN d L r₀ ρ := by
  rw [gapAt_eq M T L w κ hκ] at hb
  exact mem_alphaN_of_norm_le L hL r₀ ρ _ hb

theorem nz_vec (L : ℝ) (hL : L ≠ 0) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3)
    (h : Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0) : T.triZ κ j - T.triZ κ (j - 1) ≠ 0 := by
  have := T.gap_ne_zero hL w κ hκ j h
  intro e; apply this; rw [← neg_sub, e, neg_zero]

/-- **`ΔF = 1`, first cut `β`, second cut `α`**. -/
theorem card_βα (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₁ : Mom d) (ρ₁ : ℝ)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0))
    (hnz : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hb1 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 1) (T.b 1) - r₁‖ ≤ ρ₁) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) ∧
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hn0 : T.triZ κs 0 - T.triZ κs 2 ≠ 0 := by
    have h := T.nz_vec L hL.ne' w κs hκs.1.1 0 (hnz κs hκs 0)
    rwa [fin3_zero_sub] at h
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
        if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 0 + p.1 - p.2 else T.triZ κs 2 + p.1) ''
        ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₁ ρ₁ : Finset _) :
          Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hC0, hE0⟩ := T.rel0 hβ0 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    have hC0' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 0).1 hC0
    rw [fin3_zero_sub] at hC0'
    have hu2 : T.triZ κ 2 - T.triZ κs 2 = T.triZ κ 0 - T.triZ κs 0 := by
      funext k; have := congrFun hC0' k; simp only [Pi.sub_apply] at this ⊢; omega
    refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 0 - T.triZ κ 1), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, ?_⟩
      · unfold slabF
        rw [Finset.mem_filter]
        refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
        refine energy_slab_of_rel L γ δ hL w (T.triZ κ 0) (T.triZ κ 2) (T.triZ κs 0) (T.triZ κs 2)
          (T.triZ κ 0 - T.triZ κs 0) (by abel) (by rw [← hu2]; abel) ?_
        have e := hE0
        unfold triG at e
        rw [fin3_zero_sub] at e
        exact e
      · have := T.gap_mem_alphaN L hL w 1 r₁ ρ₁ κ hκ.1.1 (hb1 κ hκ)
        rwa [fin3_one_sub] at this
    · funext j
      fin_cases j
      · simp
      · show (T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) - (T.triZ κ 0 - T.triZ κ 1)) = T.triZ κ 1
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
      · show T.triZ κs 2 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 2
        funext k; have := congrFun hu2 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  have hss : ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₁ ρ₁ : Finset _) :
        Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      ((boxF d ⌊2 * L⌋₊ ×ˢ alphaN d L r₁ ρ₁ : Finset _) : Set ((Fin d → ℤ) × (Fin d → ℤ))) :=
    Finset.coe_subset.mpr (Finset.product_subset_product_left (Finset.filter_subset _ (boxF d ⌊2 * L⌋₊)))
  have h1' := encard_le_of_subset_image _ _ _ (hsub.trans (Set.image_mono hss))
  have h2 := card_alphaN_le L r₁ ρ₁ hL (by
    by_contra h; push Not at h
    have := hb1 κs hκs; have := norm_nonneg (Molecule.gapAt L w κs (T.a 1) (T.b 1) - r₁); linarith)
  refine ⟨h1.trans ?_, h1'.trans ?_⟩
  · rw [Finset.card_product]
    have h3 : ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ)).card * (alphaN d L r₁ ρ₁).card : ℕ) ≤
        (⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d :=
      Nat.mul_le_mul (card_slabF _ hn0 _ _) h2
    exact_mod_cast h3
  · rw [Finset.card_product, card_boxF]
    exact_mod_cast Nat.mul_le_mul le_rfl h2

end TriData
end WaveTurbulence.FinalCount
