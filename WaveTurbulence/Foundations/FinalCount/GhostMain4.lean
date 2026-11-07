/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostMain3
/-! G2-GHOST part 10: **`triangle_excess_ghost`**, the charged ghost-aware triangle deviation. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The tail of the two-block cases: one new `α`-atom `(R, κ)`, one ghost (at some index `s`). -/
theorem final_B2 {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hH : 8 * η ≤ 2 * γ - 1)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R, κ)])
    (hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1)
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ))
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) (s : Fin 3) (hs : ∀ j, gh j ↔ j = s)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (ghostConst d c η δ *
        (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
          ghostCharge L γ η ag Qg kg))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hR0 : 0 ≤ R := (inv_pos.2 hL0).le.trans hRl
  have hfgh : Finset.univ.filter gh = {s} := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]; exact hs j
  have hc1 : (Finset.univ.filter gh).card = 1 := by rw [hfgh]; simp
  have hlen : (T.alphaLabels R₀ R₁ κ₀ κ₁).length = 1 := by rw [hlab]; rfl
  by_cases hags : ag s
  · have hfa : Finset.univ.filter ag = {s} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (hs j).1 (hag j h)
      · rintro rfl; exact hags
    have hgbf : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      have := (hs j).1 h.1
      subst this; exact h.2 hags
    have hch : ghostCharge L γ η ag Qg kg = L ^ ((γ + 3 * η) / 2 - (kg s : ℝ) * η) * Qg s := by
      unfold ghostCharge; rw [hfa]; simp
    have leaf := T.leaf_B2_alpha H hH hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ (Qg s) (kg s)
      (hQl s hags) (hQu s hags) hk hN
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 1 := by
      rw [hlab, hgbf]
      congr 1
      · omega
      · simp only [List.length_singleton, Finset.card_empty]; omega
    rw [hex, hch]
    have hT : 0 < L ^ ((γ + 3 * η) / 2 - (kg s : ℝ) * η) * Qg s :=
      mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl s hags))
    refine excess_mono_const (ghostConst_ge_S4 d c H.hη H.hδ0) (div_nonneg ?_ hT.le)
    exact excessRHS_nonneg L γ η hL0 _ (by simpa using hR0) _ _
  · have hfa : Finset.univ.filter ag = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j _ h
      have := (hs j).1 (hag j h)
      subst this; exact hags h
    have hgbf : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = {s} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (hs j).1 h.1
      · rintro rfl; exact ⟨(hs j).2 rfl, hags⟩
    have hch : ghostCharge L γ η ag Qg kg = 1 := by
      unfold ghostCharge; rw [hfa]; simp
    have leaf := T.leaf_B2_beta H hH hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ hk hN
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 0 := by
      rw [hlab, hgbf]
      congr 1
      · omega
      · simp only [List.length_singleton, Finset.card_singleton]; omega
    rw [hex, hch, div_one]
    exact excess_mono_const (ghostConst_ge_S4 d c H.hη H.hδ0) (excessRHS_nonneg L γ η hL0 _ (by simpa using hR0) _ _)

/-- **Charged ghost-aware triangle deviation** (R38 item 1). -/
theorem triangle_excess_ghost {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hH : 8 * η ≤ 2 * γ - 1)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hb1 : κ₁ = 50 → (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁) ∨
      T.SiblingReading L w Adm (L ^ (-50 * η) * R₁))
    -- the ghosts: `gh j` (the atom `v_{j+1}` is an already cut atom of degree `2`), `ag j` (an `α`-ghost, label `(Qg j, kg j)`)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (hnot3 : ¬ (ag 0 ∧ ag 1 ∧ ag 2)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (ghostConst d c η δ *
        (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
          ghostCharge L γ η ag Qg kg))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hD0 : 0 < ghostConst d c η δ := by
    have := ghostConst_ge_S2 d c H.hη H.hδ0
    have h9 : 0 < 9 * (d : ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by
      have : (0 : ℝ) < d := by exact_mod_cast (by have := H.hd; omega : 0 < d)
      have := H.hη; have := H.hδ0; positivity
    linarith
  -- ghost-free case
  by_cases hg : ∀ j, ¬ gh j
  · have hf1 : Finset.univ.filter gh = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _; exact hg j
    have hf2 : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j h.1
    have hf3 : Finset.univ.filter ag = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j (hag j h)
    have hch : ghostCharge L γ η ag Qg kg = 1 := by
      unfold ghostCharge; rw [hf3]; simp
    rw [hf1, hf2, hch]
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, div_one]
    have key := T.triangle_excess_sibling H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ hκ₀ hκ₁
      hR₀l hR₀u hR₁l hR₁u hgap0 hball0 hgap1 hb1
    refine isDeviation_mono key (ENNReal.ofReal_le_ofReal ?_)
    refine excess_mono_const (ghostConst_ge_triConst d c H.hη H.hδ0) (excessRHS_nonneg L γ η hL0 _ ?_ _ _)
    intro p hp
    unfold alphaLabels at hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp <;> (split_ifs at hp <;> simp at hp)
    · rcases hp with rfl; exact (inv_pos.2 hL0).le.trans hR₀l
    · rcases hp with rfl; exact (inv_pos.2 hL0).le.trans hR₁l
  push Not at hg
  obtain ⟨j0, hj0⟩ := hg
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
  have hgc3 : (Finset.univ.filter gh).card ≤ 3 := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin 3)) gh
    simpa using this
  by_cases hα0 : T.IsA0 <;> by_cases hα1 : T.IsA1
  · -- `α, α`: no ghost is possible
    exfalso
    rcases h012 with rfl | rfl | rfl
    · exact T.not_isA0_of_ghost (hgd _ hj0) hα0
    · exact T.not_isA1_of_ghost1 (hgd _ hj0) hα1
    · exact T.not_isA1_of_ghost2 (hgd _ hj0) hα1
  · -- `α, β`: one ghost, at `v₂` or `v₃`
    have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀)] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by rw [hΔ]; norm_num
    have hg0 : ¬ gh 0 := fun h => T.not_isA0_of_ghost (hgd 0 h) hα0
    have hnot12 : ¬ (gh 1 ∧ gh 2) := by
      rintro ⟨h1, h2⟩
      have hsc := T.sc_f0_f1_of_ghost2 (hgd 2 h2) hα0
      exact T.f_ne (by decide : (0 : Fin 3) ≠ 1) (sc_isolated (T.m2_dartless1 (hgd 1 h1)) hsc)
    have hs : ∃ s : Fin 3, ∀ j, gh j ↔ j = s := by
      rcases h012 with rfl | rfl | rfl
      · exact absurd hj0 hg0
      · refine ⟨1, fun j => ?_⟩
        have h2 : ¬ gh 2 := fun h => hnot12 ⟨hj0, h⟩
        constructor
        · intro h
          rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
          · exact absurd h hg0
          · rfl
          · exact absurd h h2
        · rintro rfl; exact hj0
      · refine ⟨2, fun j => ?_⟩
        have h1 : ¬ gh 1 := fun h => hnot12 ⟨h, hj0⟩
        constructor
        · intro h
          rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
          · exact absurd h hg0
          · exact absurd h h1
          · rfl
        · rintro rfl; exact hj0
    obtain ⟨s, hs⟩ := hs
    set ρ₀ : ℝ := if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀ with hρ₀
    have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
        (T.tripleSet L γ δ w Adm c' β k0).encard ≤
          ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
            (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
      intro c' β k0 hP
      obtain ⟨r₀, hr₀⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 0 R₀ κ₀ hgap0 hball0 hκ₀ c' β k0 hP
      have h := T.card_αβ L γ δ hL0 H.hδ0 w Adm c' β k0 r₀ ρ₀ (T.hbeta1 hα1)
        (fun κ hκ => hnz κ hκ.2.2) hr₀
      exact encard_le_min_mul _ _ _ h.1 h.2
    exact T.final_B2 H hH hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₀ κ₀ hR₀l hR₀u ρ₀
      (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀) hlab hΔ hk hN gh ag hag s hs Qg kg hQl hQu
  · -- `β, α`: one ghost, at `v₁`
    have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₁, κ₁)] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by rw [hΔ]; norm_num
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
    have hball1 : κ₁ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
        ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
          ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁ := by
      intro h50
      rcases hb1 h50 with hf | hsb
      · exact hf
      · exact fun c β k0 _ => T.ball1_of_sib_beta hL0 H.hδ0 w Adm (T.hbeta0 hα0) hsb c β k0
    have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
        (T.tripleSet L γ δ w Adm c' β k0).encard ≤
          ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
            (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
      intro c' β k0 hP
      obtain ⟨r₁, hr₁⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 1 R₁ κ₁ hgap1 hball1 hκ₁ c' β k0 hP
      have h := T.card_βα L γ δ hL0 H.hδ0 w Adm c' β k0 r₁ ρ₁ (T.hbeta0 hα0)
        (fun κ hκ => hnz κ hκ.2.2) hr₁
      exact encard_le_min_mul _ _ _ h.1 h.2
    exact T.final_B2 H hH hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₁ κ₁ hR₁l hR₁u ρ₁
      (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁) hlab hΔ hk hN gh ag hag 0 hs Qg kg hQl hQu
  · -- `β, β`: three singleton blocks
    have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [] := by simp [alphaLabels, hα0, hα1]
    have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 2 := by rw [T.deltaF_eq]; simp [hα0, hα1]
    have hsum := card_ghost_split gh ag hag
    have hna3 : (Finset.univ.filter ag).card ≤ 3 := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin 3)) ag
    have hna2 : (Finset.univ.filter ag).card ≠ 3 := by
      intro h3
      apply hnot3
      have hall : Finset.univ.filter ag = Finset.univ := Finset.eq_univ_of_card _ (by simpa using h3)
      have h : ∀ j, ag j := fun j => by
        have : j ∈ Finset.univ.filter ag := by rw [hall]; exact Finset.mem_univ j
        simpa using this
      exact ⟨h 0, h 1, h 2⟩
    rcases (by omega : (Finset.univ.filter ag).card = 0 ∨ (Finset.univ.filter ag).card = 1 ∨
        (Finset.univ.filter ag).card = 2) with h0 | h1 | h2
    · -- no `α`-ghost
      have hfa : Finset.univ.filter ag = ∅ := Finset.card_eq_zero.1 h0
      have hch : ghostCharge L γ η ag Qg kg = 1 := by unfold ghostCharge; rw [hfa]; simp
      have leaf := T.leaf_P5_beta H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz hα0 hα1
        (Finset.univ.filter gh).card hgc3
      refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
      have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) =
          excessRHS L γ η [] (2 - ((Finset.univ.filter gh).card : ℤ)) (3 - 2 * ((Finset.univ.filter gh).card : ℤ)) := by
        rw [hlab]
        congr 1
        · omega
        · simp only [List.length_nil, Nat.cast_zero]; omega
      rw [hex, hch, div_one]
      exact excess_mono_const (ghostConst_ge_S1 d c H.hη H.hδ0) (excessRHS_nonneg L γ η hL0 [] (by simp) _ _)
    · -- one `α`-ghost
      obtain ⟨k, hk⟩ := Finset.card_eq_one.1 h1
      have hkag : ag k := by
        have : k ∈ Finset.univ.filter ag := by rw [hk]; simp
        simpa using this
      have hch : ghostCharge L γ η ag Qg kg = L ^ ((γ + 3 * η) / 2 - (kg k : ℝ) * η) * Qg k := by
        unfold ghostCharge; rw [hk]; simp
      have hgb : (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card ≤ 2 := by omega
      have leaf := T.leaf_P5_alpha1 H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hα0 hα1 k (Qg k) (kg k)
        (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card hgb (hQl k hkag) (hQu k hkag) (hlow k hkag)
      refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
      have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) =
          excessRHS L γ η [] (1 - ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ))
            (2 - 2 * ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) := by
        rw [hlab]
        congr 1
        · omega
        · simp only [List.length_nil, Nat.cast_zero]; omega
      rw [hex, hch]
      have hT : 0 < L ^ ((γ + 3 * η) / 2 - (kg k : ℝ) * η) * Qg k :=
        mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl k hkag))
      exact excess_mono_const (ghostConst_ge_S2 d c H.hη H.hδ0)
        (div_nonneg (excessRHS_nonneg L γ η hL0 [] (by simp) _ _) hT.le)
    · -- two `α`-ghosts
      obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.1 h2
      have hxag : ag x := by
        have : x ∈ Finset.univ.filter ag := by rw [hxy']; simp
        simpa using this
      have hyag : ag y := by
        have : y ∈ Finset.univ.filter ag := by rw [hxy']; simp
        simpa using this
      have hch : ghostCharge L γ η ag Qg kg = (L ^ ((γ + 3 * η) / 2 - (kg x : ℝ) * η) * Qg x) *
          (L ^ ((γ + 3 * η) / 2 - (kg y : ℝ) * η) * Qg y) := by
        unfold ghostCharge; rw [hxy', Finset.prod_pair hxy]
      have hgb : (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card ≤ 1 := by omega
      have leaf := T.leaf_P5_alpha2 H hH hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hα0 hα1 y (Qg x) (Qg y)
        (kg x) (kg y) (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card hgb (hQl x hxag) (hQu x hxag)
        (hQl y hyag) (hQu y hyag) (hlow y hyag)
      refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
      have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) =
          excessRHS L γ η [] (-((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ))
            (1 - 2 * ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) := by
        rw [hlab]
        congr 1
        · omega
        · simp only [List.length_nil, Nat.cast_zero]; omega
      rw [hex, hch]
      have hTx : 0 < L ^ ((γ + 3 * η) / 2 - (kg x : ℝ) * η) * Qg x :=
        mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl x hxag))
      have hTy : 0 < L ^ ((γ + 3 * η) / 2 - (kg y : ℝ) * η) * Qg y :=
        mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl y hyag))
      exact excess_mono_const (ghostConst_ge_S2 d c H.hη H.hδ0)
        (div_nonneg (excessRHS_nonneg L γ η hL0 [] (by simp) _ _) (mul_pos hTx hTy).le)

end TriData
end WaveTurbulence.FinalCount
