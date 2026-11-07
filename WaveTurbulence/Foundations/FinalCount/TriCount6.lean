/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCount5
/-! Triangles, part 15 (FINALCOUNT-G2): the triple count when the first cut is an `α`-cut. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem triG_sum01 (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) :
    TriData.triG L w z 1 + TriData.triG L w z 0 = ‖w + latticePoint L (z 1)‖ ^ 2 - ‖w + latticePoint L (z 2)‖ ^ 2 := by
  unfold TriData.triG TriData.triK
  rw [TriData.fin3_one_sub, TriData.fin3_zero_sub]; ring

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem rho_nonneg (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (j : Fin 3) (r₀ : Mom d) (ρ : ℝ) (κs : D → (Fin d → ℤ))
    (hκs : κs ∈ decSet M L γ δ w Adm c β k0)
    (hb : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a j) (T.b j) - r₀‖ ≤ ρ) : 0 ≤ ρ :=
  (norm_nonneg _).trans (hb κs hκs)

/-- **`ΔF = 1`, first cut `α`, second cut `β`, only the second gap involved.** -/
theorem card_αβ_A (hi : T.idx T.S1 = {1}) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (ρ₀ : ℝ)
    (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hnz : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) ∧
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hball := card_alphaN_le L r₀ ρ₀ hL (T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0)
  have hn1 : T.triZ κs 1 - T.triZ κs 0 ≠ 0 := by
    have h := T.nz_vec L hL.ne' w κs hκs.1.1 1 (hnz κs hκs 1)
    rwa [fin3_one_sub] at h
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
        if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 1 + p.1 else T.triZ κs 0 + p.1 + p.2) ''
        ((slabF d (T.triZ κs 1 - T.triZ κs 0) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₀ ρ₀ : Finset _) :
          Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hC1, hE1⟩ := T.rel1a hi hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    have hC1' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 hC1
    rw [fin3_one_sub] at hC1'
    have hu1 : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 0 - T.triZ κs 0 := by
      funext k; have := congrFun hC1' k; simp only [Pi.sub_apply] at this ⊢; omega
    refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 2 - T.triZ κ 0), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, ?_⟩
      · unfold slabF
        rw [Finset.mem_filter]
        refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
        refine energy_slab_of_rel L γ δ hL w (T.triZ κ 1) (T.triZ κ 0) (T.triZ κs 1) (T.triZ κs 0)
          (T.triZ κ 0 - T.triZ κs 0) (by rw [← hu1]; abel) (by abel) ?_
        have e := hE1
        unfold triG at e
        rw [fin3_one_sub] at e
        exact e
      · have := T.gap_mem_alphaN L hL w 0 r₀ ρ₀ κ hκ.1.1 (hb0 κ hκ)
        rwa [fin3_zero_sub] at this
    · funext j
      fin_cases j
      · simp
      · show T.triZ κs 1 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 1
        funext k; have := congrFun hu1 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
      · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) + (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 2
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  have hss : ((slabF d (T.triZ κs 1 - T.triZ κs 0) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₀ ρ₀ : Finset _) :
        Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      ((boxF d ⌊2 * L⌋₊ ×ˢ alphaN d L r₀ ρ₀ : Finset _) : Set ((Fin d → ℤ) × (Fin d → ℤ))) :=
    Finset.coe_subset.mpr (Finset.product_subset_product_left (Finset.filter_subset _ (boxF d ⌊2 * L⌋₊)))
  have h1' := encard_le_of_subset_image _ _ _ (hsub.trans (Set.image_mono hss))
  refine ⟨h1.trans ?_, h1'.trans ?_⟩
  · rw [Finset.card_product]
    have h3 : ((slabF d (T.triZ κs 1 - T.triZ κs 0) ⌊2 * L⌋₊ (slabR M L γ δ)).card * (alphaN d L r₀ ρ₀).card : ℕ) ≤
        (⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d :=
      Nat.mul_le_mul (card_slabF _ hn1 _ _) hball
    exact_mod_cast h3
  · rw [Finset.card_product, card_boxF]
    exact_mod_cast Nat.mul_le_mul le_rfl hball

/-- **`ΔF = 1`, first cut `α`, second cut `β`, first two gaps involved.** -/
theorem card_αβ_B (hi : T.idx T.S1 = {0, 1}) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (ρ₀ : ℝ)
    (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hnz : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) ∧
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hball := card_alphaN_le L r₀ ρ₀ hL (T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0)
  have hn2 : T.triZ κs 1 - T.triZ κs 2 ≠ 0 := by
    have h := T.nz_vec L hL.ne' w κs hκs.1.1 2 (hnz κs hκs 2)
    rw [fin3_two_sub] at h
    intro e; apply h; rw [← neg_sub, e, neg_zero]
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
        if j = 0 then T.triZ κs 2 + p.1 - p.2 else if j = 1 then T.triZ κs 1 + p.1 else T.triZ κs 2 + p.1) ''
        ((slabF d (T.triZ κs 1 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₀ ρ₀ : Finset _) :
          Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hC, hE⟩ := T.rel1b hi hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    have e1 : ∀ z : Fin 3 → (Fin d → ℤ), triC L w z 1 + triC L w z 0 =
        latticePoint L (z 1 - z 0) + latticePoint L (z 0 - z 2) := by
      intro z; rw [triC_eq, triC_eq, fin3_one_sub, fin3_zero_sub]
    rw [e1, e1, ← latticePoint_add', ← latticePoint_add'] at hC
    have hz := latticePoint_injective L hL.ne' hC
    have hu : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 2 - T.triZ κs 2 := by
      funext k; have := congrFun hz k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
    refine ⟨(T.triZ κ 2 - T.triZ κs 2, T.triZ κ 2 - T.triZ κ 0), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, ?_⟩
      · unfold slabF
        rw [Finset.mem_filter]
        refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 2, ?_⟩
        refine energy_slab_of_rel L γ δ hL w (T.triZ κ 1) (T.triZ κ 2) (T.triZ κs 1) (T.triZ κs 2)
          (T.triZ κ 2 - T.triZ κs 2)
          (by funext k; have := congrFun hu k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega) (by abel) ?_
        have e := hE
        rw [triG_sum01, triG_sum01] at e
        exact e
      · have := T.gap_mem_alphaN L hL w 0 r₀ ρ₀ κ hκ.1.1 (hb0 κ hκ)
        rwa [fin3_zero_sub] at this
    · funext j
      fin_cases j
      · show T.triZ κs 2 + (T.triZ κ 2 - T.triZ κs 2) - (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 0
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
      · show T.triZ κs 1 + (T.triZ κ 2 - T.triZ κs 2) = T.triZ κ 1
        funext k; have := congrFun hu k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
      · show T.triZ κs 2 + (T.triZ κ 2 - T.triZ κs 2) = T.triZ κ 2
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  have hss : ((slabF d (T.triZ κs 1 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ alphaN d L r₀ ρ₀ : Finset _) :
        Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      ((boxF d ⌊2 * L⌋₊ ×ˢ alphaN d L r₀ ρ₀ : Finset _) : Set ((Fin d → ℤ) × (Fin d → ℤ))) :=
    Finset.coe_subset.mpr (Finset.product_subset_product_left (Finset.filter_subset _ (boxF d ⌊2 * L⌋₊)))
  have h1' := encard_le_of_subset_image _ _ _ (hsub.trans (Set.image_mono hss))
  refine ⟨h1.trans ?_, h1'.trans ?_⟩
  · rw [Finset.card_product]
    have h3 : ((slabF d (T.triZ κs 1 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ)).card * (alphaN d L r₀ ρ₀).card : ℕ) ≤
        (⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d :=
      Nat.mul_le_mul (card_slabF _ hn2 _ _) hball
    exact_mod_cast h3
  · rw [Finset.card_product, card_boxF]
    exact_mod_cast Nat.mul_le_mul le_rfl hball

/-- **`ΔF = 1`, first cut `α`, second cut `β`.** -/
theorem card_αβ (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₀ : Mom d) (ρ₀ : ℝ)
    (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hnz : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) ∧
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  rcases T.idx_S1_cases with hi | hi
  · exact T.card_αβ_A hi L γ δ hL hδ w Adm c β k0 r₀ ρ₀ hβ1 hnz hb0
  · exact T.card_αβ_B hi L γ δ hL hδ w Adm c β k0 r₀ ρ₀ hβ1 hnz hb0

/-- **`ΔF = 0`**: both cuts are `α`-cuts. -/
theorem card_αα (L γ δ : ℝ) (hL : 0 < L) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (r₀ : Mom d) (ρ₀ : ℝ) (r₁ : Mom d) (ρ₁ : ℝ)
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀)
    (hb1 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 1) (T.b 1) - r₁‖ ≤ ρ₁) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hball0 := card_alphaN_le L r₀ ρ₀ hL (T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0)
  have hball1 := card_alphaN_le L r₁ ρ₁ hL (T.rho_nonneg L γ δ w Adm c β k0 1 r₁ ρ₁ κs hκs hb1)
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
        if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 0 + p.1 - p.2.2 else T.triZ κs 0 + p.1 + p.2.1) ''
        ((boxF d ⌊2 * L⌋₊ ×ˢ (alphaN d L r₀ ρ₀ ×ˢ alphaN d L r₁ ρ₁) : Finset _) :
          Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) := by
    rintro _ ⟨κ, hκ, rfl⟩
    refine ⟨(T.triZ κ 0 - T.triZ κs 0, T.triZ κ 2 - T.triZ κ 0, T.triZ κ 0 - T.triZ κ 1), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product]
      refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_, ?_⟩
      · have := T.gap_mem_alphaN L hL w 0 r₀ ρ₀ κ hκ.1.1 (hb0 κ hκ)
        rwa [fin3_zero_sub] at this
      · have := T.gap_mem_alphaN L hL w 1 r₁ ρ₁ κ hκ.1.1 (hb1 κ hκ)
        rwa [fin3_one_sub] at this
    · funext j
      fin_cases j
      · simp
      · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) - (T.triZ κ 0 - T.triZ κ 1) = T.triZ κ 1
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
      · show T.triZ κs 0 + (T.triZ κ 0 - T.triZ κs 0) + (T.triZ κ 2 - T.triZ κ 0) = T.triZ κ 2
        funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine h1.trans ?_
  rw [Finset.card_product, Finset.card_product, card_boxF]
  have h3 : (2 * ⌊2 * L⌋₊ + 1) ^ d * ((alphaN d L r₀ ρ₀).card * (alphaN d L r₁ ρ₁).card) ≤
      (2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) :=
    Nat.mul_le_mul le_rfl (Nat.mul_le_mul hball0 hball1)
  exact_mod_cast h3

end TriData
end WaveTurbulence.FinalCount
