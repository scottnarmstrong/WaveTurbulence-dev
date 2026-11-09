/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone6
/-! **L6E GHOST, part 17: the creating cut patterns with providers, in the triangle-bound form.**

`cone_ab`, `cone_ba`, `cone_aa`: for the cut patterns `α β` (ghost-free or one ghost at `v₂`/`v₃`), `β α` (ghost-free or
one ghost at `v₁`) and `α α` (no ghost), the triangle bound `X · triRHS0` with providers for the new gaps (ratio `X`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace Tri
variable {M : Molecule V D} (T : TriData M)

/-- **Cut pattern `α β` with a provider for the new gap `gap₀`.** -/
theorem cone_ab {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η))
    (hR₁ : 0 ≤ R₁)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (N₀ : ℕ) (P₀ : GapProv T L γ δ w Adm 0 N₀) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N₀ : ℝ) ≤ X * ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hα0 : T.IsA0) (hα1 : ¬ T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀)] := by simp [alphaLabels, hα0, hα1]
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by rw [hΔ]; norm_num
  have hR₀ : 0 ≤ R₀ := (inv_pos.2 hL0).le.trans hR₀l
  by_cases hg : ∀ j, ¬ gh j
  · have leaf := leaf_ab_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ κ₀ hκ₀ hR₀l hR₀u N₀ P₀ X hX
      hratio hα0 hα1
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hX))
    exact triConst_le_triRHS0 T hL0 H.hη H.hδ0 c R₀ R₁ κ₀ κ₁ gh ag hag Qg kg hg _ hlab 1 hΔ
      (by intro p hp; simp at hp; rw [hp]; exact hR₀)
  push Not at hg
  obtain ⟨j0, hj0⟩ := hg
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
  have hg0 : ¬ gh 0 := fun h => T.not_isA0_of_ghost (hgd 0 h) hα0
  have hnot12 : ¬ (gh 1 ∧ gh 2) := by
    rintro ⟨h1, h2⟩
    have hsc := T.sc_f0_f1_of_ghost2 (hgd 2 h2) hα0
    exact T.f_ne (by decide : (0 : Fin 3) ≠ 1) (sc_isolated (T.m2_dartless1 (hgd 1 h1)) hsc)
  have hs : ∃ s : Fin 3, (s = 1 ∨ s = 2) ∧ ∀ j, gh j ↔ j = s := by
    rcases h012 with rfl | rfl | rfl
    · exact absurd hj0 hg0
    · refine ⟨1, Or.inl rfl, fun j => ?_⟩
      have h2 : ¬ gh 2 := fun h => hnot12 ⟨hj0, h⟩
      constructor
      · intro h
        rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
        · exact absurd h hg0
        · rfl
        · exact absurd h h2
      · rintro rfl; exact hj0
    · refine ⟨2, Or.inr rfl, fun j => ?_⟩
      have h1 : ¬ gh 1 := fun h => hnot12 ⟨h, hj0⟩
      constructor
      · intro h
        rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
        · exact absurd h hg0
        · exact absurd h h1
        · rfl
      · rintro rfl; exact hj0
  obtain ⟨s, hs12, hs⟩ := hs
  set ρ₀ : ℝ := if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀ with hρ₀
  have hr : 0 ≤ slabR M L γ δ := by unfold slabR; have := H.hδ0; positivity
  have hNb : ¬ ag s → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) * N₀ : ℕ) : ℕ∞) := by
    intro _ c' β k0 hP
    obtain ⟨A, hA, hmem⟩ := P₀ c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    have hA' : ∀ κ ∈ decSet M L γ δ w Adm c' β k0, T.triZ κ 2 - T.triZ κ 0 ∈ A := fun κ hκ => by
      have := hmem κ hκ; rwa [fin3_zero_sub] at this
    have key : ∀ (n : Fin d → ℤ) (f : (Fin d → ℤ) × (Fin d → ℤ) → (Fin 3 → (Fin d → ℤ))), n ≠ 0 →
        T.tripleSet L γ δ w Adm c' β k0 ⊆ f '' ((slabF d n ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) →
        (T.tripleSet L γ δ w Adm c' β k0).encard ≤
          ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) * N₀ : ℕ) : ℕ∞) := by
      intro n f hn hsub
      obtain ⟨h1, h2, -⟩ := encard_slab_prod L hL0 _ f n _ hr A hsub
      refine (encard_le_min_mul _ _ _ (h1 hn) h2).trans ?_
      exact_mod_cast Nat.mul_le_mul le_rfl hA
    rcases T.idx_S1_cases with hi | hi
    · refine key _ _ ?_ (sub_αβ_A_gen T hi L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta1 hα1) A hA' κs hκs)
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 1 (hnz κs hκs.2.2 1)
      rwa [fin3_one_sub] at h
    · refine key _ _ ?_ (sub_αβ_B_gen T hi L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta1 hα1) A hA' κs hκs)
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 2 (hnz κs hκs.2.2 2)
      rw [fin3_two_sub] at h
      intro e; apply h; rw [← neg_sub, e, neg_zero]
  have hNa : ag s → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg s / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * N₀ : ℕ) : ℕ∞) := by
    intro hags c' β k0 hP
    obtain ⟨A, hA, hmem⟩ := P₀ c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    have hA' : ∀ κ ∈ decSet M L γ δ w Adm c' β k0, T.triZ κ 2 - T.triZ κ 0 ∈ A := fun κ hκ => by
      have := hmem κ hκ; rwa [fin3_zero_sub] at this
    have hQ0 : 0 < Qg s / 2 := by have := lt_of_lt_of_le (inv_pos.2 hL0) (hQl s hags); positivity
    have hgs := hlow s hags κs hκs.2.2
    have key : ∀ (n : Fin d → ℤ) (f : (Fin d → ℤ) × (Fin d → ℤ) → (Fin 3 → (Fin d → ℤ))),
        Qg s / 2 ≤ ‖latticePoint L n‖ →
        T.tripleSet L γ δ w Adm c' β k0 ⊆ f '' ((slabF d n ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) →
        (T.tripleSet L γ δ w Adm c' β k0).encard ≤
          (((⌊2 * slabR M L γ δ / (Qg s / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * N₀ : ℕ) : ℕ∞) := by
      intro n f hn hsub
      obtain ⟨-, -, h3⟩ := encard_slab_prod L hL0 _ f n _ hr A hsub
      refine (h3 _ hQ0 hn).trans ?_
      exact_mod_cast Nat.mul_le_mul le_rfl hA
    rcases hs12 with rfl | rfl
    · refine key _ _ ?_ (sub_αβ_A_gen T (idx_S1_of_ghost1 T (hgd 1 (hag 1 hags))) L γ δ hL0 H.hδ0 w Adm c' β k0
        (T.hbeta1 hα1) A hA' κs hκs)
      rw [gapAt_eq M T L w κs hκs.1.1 1, fin3_one_sub] at hgs
      rw [latticePoint_sub, norm_sub_rev, ← latticePoint_sub]; exact hgs
    · refine key _ _ ?_ (sub_αβ_B_gen T (idx_S1_of_ghost2 T (hgd 2 (hag 2 hags)) hα0) L γ δ hL0 H.hδ0 w Adm c' β k0
        (T.hbeta1 hα1) A hA' κs hκs)
      rw [gapAt_eq M T L w κs hκs.1.1 2, fin3_two_sub] at hgs
      exact hgs
  exact final_B2_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₀ κ₀ hR₀l hR₀u ρ₀
    (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀) hlab hk gh ag hag s hs Qg kg hQl hQu N₀ X hX hratio hNa hNb

/-- **Cut pattern `β α` with a provider for the new gap `gap₁`.** -/
theorem cone_ba {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hR₀ : 0 ≤ R₀)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (N₁ : ℕ) (P₁ : GapProv T L γ δ w Adm 1 N₁) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N₁ : ℝ) ≤ X * ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hα0 : ¬ T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₁, κ₁)] := by simp [alphaLabels, hα0, hα1]
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by rw [hΔ]; norm_num
  have hR₁ : 0 ≤ R₁ := (inv_pos.2 hL0).le.trans hR₁l
  by_cases hg : ∀ j, ¬ gh j
  · have leaf := leaf_ba_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₁ κ₁ hκ₁ hR₁l hR₁u N₁ P₁ X hX
      hratio hα0 hα1
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hX))
    exact triConst_le_triRHS0 T hL0 H.hη H.hδ0 c R₀ R₁ κ₀ κ₁ gh ag hag Qg kg hg _ hlab 1 hΔ
      (by intro p hp; simp at hp; rw [hp]; exact hR₁)
  push Not at hg
  obtain ⟨j0, hj0⟩ := hg
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
  have hs : ∀ j, gh j ↔ j = 0 := by
    have hj00 : j0 = 0 := by
      rcases h012 with h | rfl | rfl
      · exact h
      · exact absurd hα1 (T.not_isA1_of_ghost1 (hgd _ hj0))
      · exact absurd hα1 (T.not_isA1_of_ghost2 (hgd _ hj0))
    subst hj00
    intro j
    constructor
    · intro h
      rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rfl
      · exact absurd hα1 (T.not_isA1_of_ghost1 (hgd _ h))
      · exact absurd hα1 (T.not_isA1_of_ghost2 (hgd _ h))
    · rintro rfl; exact hj0
  set ρ₁ : ℝ := if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁ with hρ₁
  have hr : 0 ≤ slabR M L γ δ := by unfold slabR; have := H.hδ0; positivity
  have hcov : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      ∀ κs ∈ decSet M L γ δ w Adm c' β k0, ∃ A : Finset (Fin d → ℤ), A.card ≤ N₁ ∧
        T.tripleSet L γ δ w Adm c' β k0 ⊆ fβα (T.triZ κs) ''
          ((slabF d (T.triZ κs 0 - T.triZ κs 2) ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) := by
    intro c' β k0 hP κs hκs
    obtain ⟨A, hA, hmem⟩ := P₁ c' β k0 hP
    refine ⟨A, hA, sub_βα_gen T L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) A (fun κ hκ => ?_) κs hκs⟩
    have := hmem κ hκ; rwa [fin3_one_sub] at this
  have hNb : ¬ ag 0 → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) * N₁ : ℕ) : ℕ∞) := by
    intro _ c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    obtain ⟨A, hA, hsub⟩ := hcov c' β k0 hP κs hκs
    obtain ⟨h1, h2, -⟩ := encard_slab_prod L hL0 _ _ _ _ hr A hsub
    have hn0 : T.triZ κs 0 - T.triZ κs 2 ≠ 0 := by
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 0 (hnz κs hκs.2.2 0)
      rwa [fin3_zero_sub] at h
    refine (encard_le_min_mul _ _ _ (h1 hn0) h2).trans ?_
    exact_mod_cast Nat.mul_le_mul le_rfl hA
  have hNa : ag 0 → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg 0 / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * N₁ : ℕ) : ℕ∞) := by
    intro hag0 c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    obtain ⟨A, hA, hsub⟩ := hcov c' β k0 hP κs hκs
    obtain ⟨-, -, h3⟩ := encard_slab_prod L hL0 _ _ _ _ hr A hsub
    have hQ0 : 0 < Qg 0 / 2 := by have := lt_of_lt_of_le (inv_pos.2 hL0) (hQl 0 hag0); positivity
    have hgs := hlow 0 hag0 κs hκs.2.2
    rw [gapAt_eq M T L w κs hκs.1.1 0, fin3_zero_sub] at hgs
    have hn : Qg 0 / 2 ≤ ‖latticePoint L (T.triZ κs 0 - T.triZ κs 2)‖ := by
      rw [latticePoint_sub, norm_sub_rev, ← latticePoint_sub]; exact hgs
    refine (h3 _ hQ0 hn).trans ?_
    exact_mod_cast Nat.mul_le_mul le_rfl hA
  exact final_B2_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₁ κ₁ hR₁l hR₁u ρ₁
    (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁) hlab hk gh ag hag 0 hs Qg kg hQl hQu N₁ X hX hratio hNa hNb

/-- **Cut pattern `α α` with a pair provider** (no ghost is possible). -/
theorem cone_aa {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2) (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ)
    (N : ℕ) (PP : PairProv T L γ δ w Adm N) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N : ℝ) ≤ X * (((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1 : ℕ) : ℝ) ^ d *
      ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ + 1 : ℕ) : ℝ) ^ d))
    (hα0 : T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀), (R₁, κ₁)] := by simp [alphaLabels, hα0, hα1]
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 0 := by rw [T.deltaF_eq]; simp [hα0, hα1]
  have hg : ∀ j, ¬ gh j := by
    intro j h
    rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact T.not_isA0_of_ghost (hgd _ h) hα0
    · exact T.not_isA1_of_ghost1 (hgd _ h) hα1
    · exact T.not_isA1_of_ghost2 (hgd _ h) hα1
  have leaf := leaf_aa_prov T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ hκ₀ hκ₁ hR₀l hR₀u hR₁l hR₁u
    N PP X hX hratio hα0 hα1
  refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hX))
  have h := triConst_le_triRHS0 (d := d) (γ := γ) T hL0 H.hη H.hδ0 c R₀ R₁ κ₀ κ₁ gh ag hag Qg kg hg _ hlab 0 hΔ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (inv_pos.2 hL0).le.trans hR₀l
    · exact (inv_pos.2 hL0).le.trans hR₁l)
  simpa using h

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
