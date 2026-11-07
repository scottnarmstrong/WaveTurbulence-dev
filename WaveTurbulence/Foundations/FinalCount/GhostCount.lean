/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostStruct
/-! G2-GHOST part 3: the triple count when all three cuts are `β`-type (the partition `{0|1|2}`), with the slab
thickness read off the size of a chosen gap (a ghost's label). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem triG_sum_zero (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) :
    triG L w z 0 + triG L w z 1 + triG L w z 2 = 0 := by
  unfold triG triK
  rw [fin3_zero_sub, fin3_one_sub, fin3_two_sub]; ring

/-- The relations of the partition `{0|1|2}`: all three gaps are fixed, and every energy is in a window. -/
theorem P5_rel (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ κs : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) (hκs : κs ∈ decSet M L γ δ w Adm c β k0) :
    (∀ j : Fin 3, T.triZ κ j - T.triZ κs j = T.triZ κ 0 - T.triZ κs 0) ∧
    (∀ k : Fin 3, |triG L w (T.triZ κ) k - triG L w (T.triZ κs) k| ≤
      4 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)))) := by
  obtain ⟨hC0, hE0⟩ := T.rel0 hβ0 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have hC0' := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 0).1 hC0
  rw [fin3_zero_sub] at hC0'
  have hu2 : T.triZ κ 2 - T.triZ κs 2 = T.triZ κ 0 - T.triZ κs 0 := by
    funext k; have := congrFun hC0' k; simp only [Pi.sub_apply] at this ⊢; omega
  have hrel1 := T.rel1 hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
  have hC1 : T.triZ κ 1 - T.triZ κ 0 = T.triZ κs 1 - T.triZ κs 0 := by
    rcases hrel1 with h | h
    · have := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 h.1
      rwa [fin3_one_sub] at this
    · have h1 := h.1
      rw [hC0] at h1
      have h3 := (triC_eq_iff L hL.ne' w (T.triZ κ) (T.triZ κs) 1).1 (add_right_cancel h1)
      rwa [fin3_one_sub] at h3
  have hu1 : T.triZ κ 1 - T.triZ κs 1 = T.triZ κ 0 - T.triZ κs 0 := by
    funext k; have := congrFun hC1 k; simp only [Pi.sub_apply] at this ⊢; omega
  refine ⟨fun j => ?_, fun k => ?_⟩
  · fin_cases j
    · rfl
    · exact hu1
    · exact hu2
  · have hW : (0 : ℝ) ≤ (M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) := by positivity
    have hsum := triG_sum_zero L w (T.triZ κ)
    have hsum' := triG_sum_zero L w (T.triZ κs)
    have e0 := hE0
    rcases hrel1 with h | h
    · have e1 := h.2
      fin_cases k
      · show |triG L w (T.triZ κ) 0 - triG L w (T.triZ κs) 0| ≤ _; linarith [abs_nonneg (triG L w (T.triZ κ) 0 - triG L w (T.triZ κs) 0)]
      · show |triG L w (T.triZ κ) 1 - triG L w (T.triZ κs) 1| ≤ _
        linarith [abs_nonneg (triG L w (T.triZ κ) 1 - triG L w (T.triZ κs) 1)]
      · show |triG L w (T.triZ κ) 2 - triG L w (T.triZ κs) 2| ≤ _
        have : triG L w (T.triZ κ) 2 - triG L w (T.triZ κs) 2 =
          -((triG L w (T.triZ κ) 0 - triG L w (T.triZ κs) 0) + (triG L w (T.triZ κ) 1 - triG L w (T.triZ κs) 1)) := by
          linarith
        rw [this, abs_neg]
        refine (abs_add_le _ _).trans ?_
        linarith
    · have e1 := h.2
      fin_cases k
      · show |triG L w (T.triZ κ) 0 - triG L w (T.triZ κs) 0| ≤ _; linarith
      · show |triG L w (T.triZ κ) 1 - triG L w (T.triZ κs) 1| ≤ _
        have : triG L w (T.triZ κ) 1 - triG L w (T.triZ κs) 1 =
          ((triG L w (T.triZ κ) 1 + triG L w (T.triZ κ) 0) - (triG L w (T.triZ κs) 1 + triG L w (T.triZ κs) 0)) -
            (triG L w (T.triZ κ) 0 - triG L w (T.triZ κs) 0) := by ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        linarith
      · show |triG L w (T.triZ κ) 2 - triG L w (T.triZ κs) 2| ≤ _
        have : triG L w (T.triZ κ) 2 - triG L w (T.triZ κs) 2 =
          -((triG L w (T.triZ κ) 1 + triG L w (T.triZ κ) 0) - (triG L w (T.triZ κs) 1 + triG L w (T.triZ κs) 0)) := by
          linarith
        rw [this, abs_neg]
        linarith

/-- **The triple count for the partition `{0|1|2}`, slab of the gap at `k`** (`‖gap_k‖ ≥ ρ`). -/
theorem card_P5_nu (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (k : Fin 3) (ρ : ℝ) (hρ : 0 < ρ)
    (hk : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρ ≤ ‖Molecule.gapAt L w κ (T.a k) (T.b k)‖) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * (2 * slabR M L γ δ) / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have := hk κs hκs
      have h1 : latticePoint L (T.triZ κs (k - 1) - T.triZ κs k) = 0 := Subsingleton.elim _ _
      rw [gapAt_eq M T L w κs hκs.1.1 k, h1] at this
      simp at this; linarith
    · exact h0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  set n : Fin d → ℤ := T.triZ κs k - T.triZ κs (k - 1) with hn
  have hnorm : ‖latticePoint L n‖ = ‖Molecule.gapAt L w κs (T.a k) (T.b k)‖ := by
    rw [gapAt_eq M T L w κs hκs.1.1 k, hn, latticePoint_sub, latticePoint_sub, ← norm_neg]
    congr 1; abel
  obtain ⟨i0, hi0⟩ := exists_coord_ge L hL n ρ hρ (by rw [hnorm]; exact hk κs hκs)
  have hν : 0 < ρ * L / d := by positivity
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun u : Fin d → ℤ => fun j : Fin 3 => T.triZ κs j + u) ''
        (slabF d n ⌊2 * L⌋₊ (2 * slabR M L γ δ) : Finset _) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hshift, hwin⟩ := T.P5_rel hβ0 hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    refine ⟨T.triZ κ 0 - T.triZ κs 0, ?_, ?_⟩
    · rw [Finset.mem_coe]
      unfold slabF
      rw [Finset.mem_filter]
      refine ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, ?_⟩
      have hzk : T.triZ κ k = T.triZ κs k + (T.triZ κ 0 - T.triZ κs 0) := by
        have := hshift k; funext i; have := congrFun this i
        simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
      have hzk1 : T.triZ κ (k - 1) = T.triZ κs (k - 1) + (T.triZ κ 0 - T.triZ κs 0) := by
        have := hshift (k - 1); funext i; have := congrFun this i
        simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
      refine slab_of_energy L hL w (T.triZ κ k) (T.triZ κ (k - 1)) (T.triZ κs k) (T.triZ κs (k - 1))
        (T.triZ κ 0 - T.triZ κs 0) hzk hzk1 (2 * slabR M L γ δ) ?_
      have e := hwin k
      unfold triG at e
      simp only [triK] at e
      have : 2 * ((2 * slabR M L γ δ) / L ^ 2) = 4 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ))) := by
        unfold slabR; field_simp; ring
      rw [this]; exact e
    · funext j
      have := hshift j
      show T.triZ κs j + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ j
      funext i; have := congrFun this i
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine h1.trans ?_
  have hr : 0 ≤ 2 * slabR M L γ δ := by unfold slabR; positivity
  exact_mod_cast card_slabF_nu n i0 (ρ * L / d) hν (by
    rw [mul_div_assoc] at hi0 ⊢; exact hi0) ⌊2 * L⌋₊ (2 * slabR M L γ δ) hr

end TriData
end WaveTurbulence.FinalCount
