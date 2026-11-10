/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Triangle
/-! **L6E GHOST, part 8: `triangle_excess_ghost_low`** (the cut pattern `β β` and the assembly).

**Export.** `Tri.triangle_excess_ghost_low`: main's `triangle_excess_ghost` with `8η ≤ 2γ - 1` replaced by the transfer
exponent `ν ∈ {0, 1}` (right-hand side `× L^{5ην}`), `ν = 0` under `PairOK` for every pair of `α`-ghosts. -/
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

/-- **Cut pattern `β β`**: three singleton blocks, `≤ 2` `α`-ghosts. -/
theorem tri_low_bb {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (hnot3 : ¬ (ag 0 ∧ ag 1 ∧ ag 2)) (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1)
    (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    (hok : ν = 0 → ∀ j₁ j₂, j₁ ≠ j₂ → ag j₁ → ag j₂ → PairOK T L γ η w Adm j₁ j₂ (Qg j₁) (Qg j₂) (kg j₁) (kg j₂)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triRHSLow T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg ν)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [] := by simp [alphaLabels, hα0, hα1]
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 2 := by rw [T.deltaF_eq]; simp [hα0, hα1]
  have hgc3 : (Finset.univ.filter gh).card ≤ 3 := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin 3)) gh
    simpa using this
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
  unfold triRHSLow
  rcases (by omega : (Finset.univ.filter ag).card = 0 ∨ (Finset.univ.filter ag).card = 1 ∨
      (Finset.univ.filter ag).card = 2) with h0 | h1 | h2
  · -- no `α`-ghost
    have hfa : Finset.univ.filter ag = ∅ := Finset.card_eq_zero.1 h0
    have hch : ghostCharge L γ η ag Qg kg = 1 := by unfold ghostCharge; rw [hfa]; simp
    have leaf := T.leaf_P5_beta H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz hα0 hα1
      (Finset.univ.filter gh).card hgc3
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
    have hE := excessRHS_nonneg L γ η hL0 [] (by simp) (2 - ((Finset.univ.filter gh).card : ℤ))
      (3 - 2 * ((Finset.univ.filter gh).card : ℤ))
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    exact le_mul_transfer ((ghostConst_ge_S1 d c H.hη H.hδ0).trans (ghostConst_le_low d c H.hδ0))
      (by have := H.hδ0; have := H.hη; positivity) hE hL1 H.hη ν
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
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    exact le_mul_transfer (ghostConstLow_ge_S2 d c H.hη H.hδ0) (by have := H.hδ0; have := H.hη; positivity)
      (div_nonneg (excessRHS_nonneg L γ η hL0 [] (by simp) _ _) hT.le) hL1 H.hη ν
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
    have leaf := leaf_P5_two_low T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hα0 hα1 x y (Qg x) (Qg y)
      (kg x) (kg y) (Finset.univ.filter fun j => gh j ∧ ¬ ag j).card hgb (hQl x hxag) (hQu x hxag)
      (hQl y hyag) (hQu y hyag) (hlow x hxag) (hlow y hyag) ν hν (fun h0 => hok h0 x y hxy hxag hyag)
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
    exact leaf

/-- **The repaired charged ghost-aware triangle deviation** (M1-R2 Theorem 6.1 at a triangle step, all `0 < γ < 1`,
`TriReal` only). Hypotheses of main's `triangle_excess_ghost` minus `8η ≤ 2γ - 1`, plus the transfer exponent `ν`:
`ν = 1` (NC class) is unconditional; `ν = 0` needs `PairOK` ((T-crit-free) or (T-TR)) for every pair of `α`-ghosts. -/
theorem triangle_excess_ghost_low {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
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
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (hnot3 : ¬ (ag 0 ∧ ag 1 ∧ ag 2))
    (ν : ℕ) (hν : ν = 0 ∨ ν = 1)
    (hok : ν = 0 → ∀ j₁ j₂, j₁ ≠ j₂ → ag j₁ → ag j₂ → PairOK T L γ η w Adm j₁ j₂ (Qg j₁) (Qg j₂) (kg j₁) (kg j₂)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (ghostConstLow d c η δ *
        (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
          ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
          (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
            ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
          ghostCharge L γ η ag Qg kg) * L ^ (5 * η * (ν : ℝ)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  show IsDeviation _ _ (ENNReal.ofReal (triRHSLow T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg ν))
  by_cases hg : ∀ j, ¬ gh j
  · -- ghost-free: main's sibling-aware triangle deviation
    have hf1 : Finset.univ.filter gh = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _; exact hg j
    have hf2 : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j h.1
    have hf3 : Finset.univ.filter ag = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j (hag j h)
    have hch : ghostCharge L γ η ag Qg kg = 1 := by
      unfold ghostCharge; rw [hf3]; simp
    unfold triRHSLow
    rw [hf1, hf2, hch]
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, div_one]
    have key := T.triangle_excess_sibling H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ hκ₀ hκ₁
      hR₀l hR₀u hR₁l hR₁u hgap0 hball0 hgap1 hb1
    refine isDeviation_mono key (ENNReal.ofReal_le_ofReal ?_)
    refine le_mul_transfer ((ghostConst_ge_triConst d c H.hη H.hδ0).trans (ghostConst_le_low d c H.hδ0))
      (triConst_nonneg d c H.hη H.hδ0) (excessRHS_nonneg L γ η hL0 _ ?_ _ _) hL1 H.hη ν
    intro p hp
    unfold alphaLabels at hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp <;> (split_ifs at hp <;> simp at hp)
    · rcases hp with rfl; exact (inv_pos.2 hL0).le.trans hR₀l
    · rcases hp with rfl; exact (inv_pos.2 hL0).le.trans hR₁l
  push Not at hg
  obtain ⟨j0, hj0⟩ := hg
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
  by_cases hα0 : T.IsA0 <;> by_cases hα1 : T.IsA1
  · -- `α, α`: no ghost is possible
    exfalso
    rcases h012 with rfl | rfl | rfl
    · exact T.not_isA0_of_ghost (hgd _ hj0) hα0
    · exact T.not_isA1_of_ghost1 (hgd _ hj0) hα1
    · exact T.not_isA1_of_ghost2 (hgd _ hj0) hα1
  · exact tri_low_ab T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ hκ₀ hR₀l hR₀u hgap0 hball0
      gh ag hag hgd Qg kg hQl hQu hlow hα0 hα1 j0 hj0 ν
  · exact tri_low_ba T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ hκ₁ hR₁l hR₁u hgap1 hb1
      gh ag hag hgd Qg kg hQl hQu hlow hα0 hα1 j0 hj0 ν
  · exact tri_low_bb T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ κ₁ gh ag hag Qg kg hQl hQu hlow
      hnot3 hα0 hα1 ν hν hok

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
