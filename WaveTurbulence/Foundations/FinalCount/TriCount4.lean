/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCount3
/-! Triangles, part 13 (FINALCOUNT-G2): the triple count for two `β`-cuts (`ΔF = 2`; DH23 L1792--L1793). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The slab radius. -/
noncomputable def slabR (M : Molecule V D) (L γ δ : ℝ) : ℝ :=
  (M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2

theorem energy_slab_of_rel (L γ δ : ℝ) (hL : 0 < L) (w : Mom d) (zi zj zi' zj' u : Fin d → ℤ) (hi : zi = zi' + u)
    (hj : zj = zj' + u)
    (hE : |(‖w + latticePoint L zi‖ ^ 2 - ‖w + latticePoint L zj‖ ^ 2) -
        (‖w + latticePoint L zi'‖ ^ 2 - ‖w + latticePoint L zj'‖ ^ 2)| ≤ 2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)))) :
    |∑ k, (((zi' - zj' : Fin d → ℤ) k : ℤ) : ℝ) * (u k : ℝ)| ≤ slabR M L γ δ := by
  refine slab_of_energy L hL w zi zj zi' zj' u hi hj _ ?_
  have : slabR M L γ δ / L ^ 2 = (M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) := by
    unfold slabR; field_simp
  rw [this]; exact hE

theorem fin3_zero_sub : ((0 : Fin 3) - 1) = 2 := by decide
theorem fin3_one_sub : ((1 : Fin 3) - 1) = 0 := by decide
theorem fin3_two_sub : ((2 : Fin 3) - 1) = 1 := by decide

theorem tripleSet_empty (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (hne : ¬ (decSet M L γ δ w Adm c β k0).Nonempty) :
    T.tripleSet L γ δ w Adm c β k0 = ∅ := by
  unfold tripleSet; rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp

/-- **`ΔF = 2`**: both cuts are `β`-cuts (DH23 L1792--L1793). -/
theorem card_ββ (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hnz : ∀ κ ∈ decSet M L γ δ w Adm c β k0, Molecule.gapAt L w κ (T.a 0) (T.b 0) ≠ 0) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℕ∞) ∧
    (T.tripleSet L γ δ w Adm c β k0).encard ≤ (((2 * ⌊2 * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hn0 : T.triZ κs 0 - T.triZ κs 2 ≠ 0 := by
    have h := T.gap_ne_zero hL.ne' w κs hκs.1.1 0 (hnz κs hκs)
    rw [fin3_zero_sub] at h
    intro e; apply h
    rw [← neg_sub, e, neg_zero]
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun u : Fin d → ℤ => fun j : Fin 3 => T.triZ κs j + u) ''
        (slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) : Finset _) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hC0, hE0⟩ := T.rel0 hβ0 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    have hC0' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 0).1 hC0
    rw [fin3_zero_sub] at hC0'
    have hu2 : T.triZ κ 2 - T.triZ κs 2 = T.triZ κ 0 - T.triZ κs 0 := by
      funext k; have := congrFun hC0' k; simp only [Pi.sub_apply] at this ⊢; omega
    have hC1 : T.triZ κ 1 - T.triZ κ 0 = T.triZ κs 1 - T.triZ κs 0 := by
      have := T.rel1 hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
      rcases this with h | h
      · have := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 h.1
        rwa [fin3_one_sub] at this
      · have h1 := h.1
        rw [hC0] at h1
        have h3 := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 (add_right_cancel h1)
        rwa [fin3_one_sub] at h3
    have hu1 : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 0 - T.triZ κs 0 := by
      funext k; have := congrFun hC1 k; simp only [Pi.sub_apply] at this ⊢; omega
    refine ⟨T.triZ κ 0 - T.triZ κs 0, ?_, ?_⟩
    · rw [Finset.mem_coe]
      unfold slabF
      rw [Finset.mem_filter]
      refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
      refine energy_slab_of_rel L γ δ hL w (T.triZ κ 0) (T.triZ κ 2) (T.triZ κs 0) (T.triZ κs 2)
        (T.triZ κ 0 - T.triZ κs 0) (by abel) (by rw [← hu2]; abel) ?_
      have e := hE0
      unfold triG at e
      rw [fin3_zero_sub] at e
      exact e
    · funext j
      fin_cases j
      · simp
      · show T.triZ κs 1 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 1
        funext k; have := congrFun hu1 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
      · show T.triZ κs 2 + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ 2
        funext k; have := congrFun hu2 k; simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  have h1' := encard_le_of_subset_image _ _ _ (hsub.trans (Set.image_mono
    (Finset.coe_subset.mpr (Finset.filter_subset _ (boxF d ⌊2 * L⌋₊)) :
      ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) : Finset _) : Set (Fin d → ℤ)) ⊆
        ((boxF d ⌊2 * L⌋₊ : Finset _) : Set (Fin d → ℤ)))))
  refine ⟨h1.trans ?_, h1'.trans ?_⟩
  · exact_mod_cast card_slabF _ hn0 _ _
  · rw [card_boxF]

end TriData
end WaveTurbulence.FinalCount
