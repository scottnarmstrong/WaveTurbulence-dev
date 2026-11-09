/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone5
/-! **L6E GHOST, part 16: the creating cut patterns, assembled** (`final_B2_prov`, `cone_ab`, `cone_ba`, `cone_aa`). -/
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

/-- **The two-block tail with a provider** (cf. `final_B2_low`). -/
theorem final_B2_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R, κ)])
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) (s : Fin 3)
    (hs : ∀ j, gh j ↔ j = s)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (N : ℕ) (X : ℝ) (hX : 0 ≤ X) (hratio : (N : ℝ) ≤ X * ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hNa : ag s → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg s / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * N : ℕ) : ℕ∞))
    (hNb : ¬ ag s → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) * N : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hR0 : 0 ≤ R := (inv_pos.2 hL0).le.trans hRl
  have hfgh : Finset.univ.filter gh = {s} := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]; exact hs j
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by omega
  unfold triRHS0
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
    have leaf := leaf_B2_alpha_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ (Qg s) (kg s)
      (hQl s hags) (hQu s hags) hk N X hX hratio (hNa hags)
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 1 := by
      rw [hlab, hgbf, hfgh]
      congr 1
      all_goals (try simp only [List.length_singleton, Finset.card_empty, Finset.card_singleton])
      all_goals omega
    rw [hex, hch]
    have hT : 0 < L ^ ((γ + 3 * η) / 2 - (kg s : ℝ) * η) * Qg s :=
      mul_pos (Real.rpow_pos_of_pos hL0 _) (lt_of_lt_of_le (inv_pos.2 hL0) (hQl s hags))
    refine mul_le_mul_of_nonneg_left (excess_mono_const (constB2_le_low d c H.hη H.hδ0) (div_nonneg ?_ hT.le)) hX
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
    have leaf := leaf_B2_beta_prov T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R κ hRl hRu ρ hρ hk N X hX hratio
      (hNb hags)
    refine isDeviation_mono leaf (ENNReal.ofReal_le_ofReal ?_)
    have hex : excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
        ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
        (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
          ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) = excessRHS L γ η [(R, κ)] 0 0 := by
      rw [hlab, hgbf, hfgh]
      congr 1
      all_goals (try simp only [List.length_singleton, Finset.card_singleton])
      all_goals omega
    rw [hex, hch, div_one]
    exact mul_le_mul_of_nonneg_left (excess_mono_const (ghostConstLow_ge_S4 d c H.hη H.hδ0)
      (excessRHS_nonneg L γ η hL0 _ (by simpa using hR0) _ _)) hX

/-- The ghost-free conversion: main's target `triConst · excessRHS(new α, ΔF, 3 - #α)` is below `triRHS0`. -/
theorem triConst_le_triRHS0 {L γ η δ : ℝ} (hL : 0 < L) (hη : 0 < η) (hδ : 0 < δ) (c : ℕ) (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j) (Qg : Fin 3 → ℝ)
    (kg : Fin 3 → ℕ) (hg : ∀ j, ¬ gh j) (l : List (ℝ × ℕ)) (hl : T.alphaLabels R₀ R₁ κ₀ κ₁ = l) (ΔF : ℤ)
    (hF : (T.kept.numComponents : ℤ) - M.numComponents = ΔF) (hl0 : ∀ p ∈ l, 0 ≤ p.1) :
    triConst d c η δ * excessRHS L γ η l ΔF (3 - (l.length : ℤ)) ≤ triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg := by
  have hf1 : Finset.univ.filter gh = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro j _; exact hg j
  have hf2 : (Finset.univ.filter fun j => gh j ∧ ¬ ag j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j h.1
  have hf3 : Finset.univ.filter ag = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro j _ h; exact hg j (hag j h)
  have hch : ghostCharge L γ η ag Qg kg = 1 := by
    unfold ghostCharge; rw [hf3]; simp
  unfold triRHS0
  rw [hf1, hf2, hch, hl, hF]
  simp only [Finset.card_empty, Nat.cast_zero, sub_zero, div_one]
  exact excess_mono_const ((ghostConst_ge_triConst d c hη hδ).trans (ghostConst_le_low d c hδ))
    (excessRHS_nonneg L γ η hL _ hl0 _ _)

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
