/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostMain4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Lattice
/-! **L6E GHOST, part 2: triangle counts for the repair** (M1-R2 NOTES §6 (b), §10.1; REF-M1R2 R2).

* **The ghost-label slab for two blocks** (`card_αβ_A_nu`, `card_αβ_B_nu`, `card_βα_nu`): main's two-block triple counts
  (`card_αβ_A`, `card_αβ_B`, `card_βα`, FINALCOUNT-G2) slab along the gap of the ghost of the triangle; here the slab
  width is read off the ghost's label (`card_slabF_nu`), as `arith_B2_alpha` needs for every `γ` (REF-M1R2 R2).
  `idx_S1_of_ghost1`, `idx_S1_of_ghost2` say which of main's two `α β` shapes a ghost at `v₂` / `v₃` produces.
* **Two slabs for three singleton blocks** (`card_P5_two`, Theorem 6.1 (b)): the energy windows of two `α`-ghosts
  `j₁ ≠ j₂` whose gaps are transverse (`θ² |g₁|²|g₂|² ≤ |g₁|²|g₂|² - ⟨g₁,g₂⟩²`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem sum_sq_latticePoint (L : ℝ) (hL : 0 < L) (n : Fin d → ℤ) :
    ∑ i, (n i : ℝ) ^ 2 = L ^ 2 * ‖latticePoint L n‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_latticePoint]
  field_simp

theorem sum_mul_latticePoint (L : ℝ) (hL : 0 < L) (n n' : Fin d → ℤ) :
    ∑ i, (n i : ℝ) * (n' i : ℝ) = L ^ 2 * inner ℝ (latticePoint L n) (latticePoint L n') := by
  rw [inner_latticePoint]
  field_simp

/-! ### The ghost-label slab for two blocks -/

/-- A set covered by `slab × ball`, with the slab normal of length `≥ ρ`. -/
theorem encard_slab_ball_nu (L : ℝ) (hL : 0 < L) {X : Type*} (Z : Set X)
    (f : (Fin d → ℤ) × (Fin d → ℤ) → X) (n : Fin d → ℤ) (r : ℝ) (hr : 0 ≤ r) (r₀ : Mom d) (ρ₀ : ℝ)
    (hρ₀ : 0 ≤ ρ₀) (ρ : ℝ) (hρ : 0 < ρ) (hn : ρ ≤ ‖latticePoint L n‖)
    (hsub : Z ⊆ f '' ((slabF d n ⌊2 * L⌋₊ r ×ˢ alphaN d L r₀ ρ₀ : Finset _) : Set _)) :
    Z.encard ≤ (((⌊2 * r / (ρ * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have : latticePoint L n = 0 := Subsingleton.elim _ _
      rw [this, norm_zero] at hn; linarith
    · exact h0
  obtain ⟨i0, hi0⟩ := exists_coord_ge L hL n ρ hρ hn
  have hν : 0 < ρ * L / d := by positivity
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine h1.trans ?_
  rw [Finset.card_product]
  have h2 := card_slabF_nu n i0 (ρ * L / d) hν (by rw [mul_div_assoc] at hi0 ⊢; exact hi0) ⌊2 * L⌋₊ r hr
  have h3 := card_alphaN_le L r₀ ρ₀ hL hρ₀
  exact_mod_cast Nat.mul_le_mul h2 h3

/-- A ghost at `v₂` isolates the second fresh atom: main's first `α β` shape (`idx S1 = {1}`). -/
theorem idx_S1_of_ghost1 {M : Molecule V D} (T : TriData M) (hd : M.deg (T.t 1) ≤ 2) : T.idx T.S1 = {1} := by
  ext j
  simp only [idx, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hj⟩
    exact T.f_inj (sc_isolated (T.m2_dartless1 hd) hj)
  · rintro rfl
    exact ⟨by rw [m2_atoms]; exact Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩

/-- A ghost at `v₃` after an `α`-cut at `v₁`: main's second `α β` shape (`idx S1 = {0, 1}`). -/
theorem idx_S1_of_ghost2 {M : Molecule V D} (T : TriData M) (hd2 : M.deg (T.t 2) ≤ 2) (hA0 : T.IsA0) :
    T.idx T.S1 = {0, 1} := by
  rcases T.idx_S1_cases with h | h
  · exfalso
    have h0 : (0 : Fin 3) ∈ T.idx T.S1 := by
      simp only [idx, S1, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [m2_atoms]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        T.sc_f0_f1_of_ghost2 hd2 hA0⟩
    rw [h] at h0
    exact absurd (Finset.mem_singleton.1 h0) (by decide)
  · exact h

/-- **`α β`, ghost at `v₂`** (copy of main's `card_αβ_A`, slab width from the ghost's gap `‖gap₁‖ ≥ ρg`). -/
theorem card_αβ_A_nu {M : Molecule V D} (T : TriData M) (hi : T.idx T.S1 = {1}) (L γ δ : ℝ) (hL : 0 < L)
    (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (r₀ : Mom d) (ρ₀ : ℝ) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀)
    (ρg : ℝ) (hρg : 0 < ρg) (hg : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρg ≤ ‖Molecule.gapAt L w κ (T.a 1) (T.b 1)‖) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ / (ρg * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hρ₀ := T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0
  have hn : ρg ≤ ‖latticePoint L (T.triZ κs 1 - T.triZ κs 0)‖ := by
    have := hg κs hκs
    rw [gapAt_eq M T L w κs hκs.1.1 1, fin3_one_sub] at this
    rw [latticePoint_sub, norm_sub_rev, ← latticePoint_sub]
    exact this
  refine encard_slab_ball_nu L hL _ (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
      if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 1 + p.1 else T.triZ κs 0 + p.1 + p.2)
    (T.triZ κs 1 - T.triZ κs 0) (slabR M L γ δ) (by unfold slabR; positivity) r₀ ρ₀ hρ₀ ρg hρg hn ?_
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

/-- **`α β`, ghost at `v₃`** (copy of main's `card_αβ_B`, slab width from the ghost's gap `‖gap₂‖ ≥ ρg`). -/
theorem card_αβ_B_nu {M : Molecule V D} (T : TriData M) (hi : T.idx T.S1 = {0, 1}) (L γ δ : ℝ) (hL : 0 < L)
    (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (r₀ : Mom d) (ρ₀ : ℝ) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (hb0 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 0) (T.b 0) - r₀‖ ≤ ρ₀)
    (ρg : ℝ) (hρg : 0 < ρg) (hg : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρg ≤ ‖Molecule.gapAt L w κ (T.a 2) (T.b 2)‖) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ / (ρg * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hρ₀ := T.rho_nonneg L γ δ w Adm c β k0 0 r₀ ρ₀ κs hκs hb0
  have hn : ρg ≤ ‖latticePoint L (T.triZ κs 1 - T.triZ κs 2)‖ := by
    have := hg κs hκs
    rw [gapAt_eq M T L w κs hκs.1.1 2, fin3_two_sub] at this
    exact this
  refine encard_slab_ball_nu L hL _ (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
      if j = 0 then T.triZ κs 2 + p.1 - p.2 else if j = 1 then T.triZ κs 1 + p.1 else T.triZ κs 2 + p.1)
    (T.triZ κs 1 - T.triZ κs 2) (slabR M L γ δ) (by unfold slabR; positivity) r₀ ρ₀ hρ₀ ρg hρg hn ?_
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

/-- **`β α`, ghost at `v₁`** (copy of main's `card_βα`, slab width from the ghost's gap `‖gap₀‖ ≥ ρg`). -/
theorem card_βα_nu {M : Molecule V D} (T : TriData M) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (r₁ : Mom d) (ρ₁ : ℝ)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0))
    (hb1 : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ (T.a 1) (T.b 1) - r₁‖ ≤ ρ₁)
    (ρg : ℝ) (hρg : 0 < ρg) (hg : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρg ≤ ‖Molecule.gapAt L w κ (T.a 0) (T.b 0)‖) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      (((⌊2 * slabR M L γ δ / (ρg * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  have hρ₁ := T.rho_nonneg L γ δ w Adm c β k0 1 r₁ ρ₁ κs hκs hb1
  have hn : ρg ≤ ‖latticePoint L (T.triZ κs 0 - T.triZ κs 2)‖ := by
    have := hg κs hκs
    rw [gapAt_eq M T L w κs hκs.1.1 0, fin3_zero_sub] at this
    rw [latticePoint_sub, norm_sub_rev, ← latticePoint_sub]
    exact this
  refine encard_slab_ball_nu L hL _ (fun p : (Fin d → ℤ) × (Fin d → ℤ) => fun j : Fin 3 =>
      if j = 0 then T.triZ κs 0 + p.1 else if j = 1 then T.triZ κs 0 + p.1 - p.2 else T.triZ κs 2 + p.1)
    (T.triZ κs 0 - T.triZ κs 2) (slabR M L γ δ) (by unfold slabR; positivity) r₁ ρ₁ hρ₁ ρg hρg hn ?_
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

end WaveTurbulence.GammaLow.FinalCount.Ghost
