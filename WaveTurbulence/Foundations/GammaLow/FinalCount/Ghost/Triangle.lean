/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Leaves
/-! **L6E GHOST, part 7: `triangle_excess_ghost_low`**, the charged ghost-aware triangle deviation for every
`0 < γ < 1` (M1-R2 Theorem 6.1 at a triangle step; §10.1; REF-M1R2 R2).

Main's `triangle_excess_ghost` (G2-GHOST) with its hypothesis `8η ≤ 2γ - 1` replaced by a **transfer exponent**
`ν ∈ {0, 1}`: the right-hand side is multiplied by `L^{5ην}`. `ν = 1` is always allowed (the NC class, Theorem 6.1 (c));
`ν = 0` needs, for every pair of `α`-ghosts of the triangle, (T-crit-free) or (T-TR) (`PairOK`). Copy of main's proof
(sha256 in COPIED-SHA256SUMS), split into one lemma per cut pattern. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The right-hand side of the repaired charged triangle bound. -/
noncomputable def triRHSLow {M : Molecule V D} (T : TriData M) (d c : ℕ) (L γ η δ : ℝ) (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (ν : ℕ) : ℝ :=
  ghostConstLow d c η δ *
    (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
      ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
      (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
        ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
      ghostCharge L γ η ag Qg kg) * L ^ (5 * η * (ν : ℝ))

theorem isDeviation_transfer {A A' : ℝ≥0∞} {Z L η : ℝ} (h : IsDeviation A A' (ENNReal.ofReal Z)) (hZ : 0 ≤ Z)
    (hL : 1 ≤ L) (hη : 0 < η) (ν : ℕ) : IsDeviation A A' (ENNReal.ofReal (Z * L ^ (5 * η * (ν : ℝ)))) := by
  refine isDeviation_mono h (ENNReal.ofReal_le_ofReal ?_)
  have := one_le_rpow_transfer hL hη ν
  nlinarith

theorem ghostCharge_pos {L γ η : ℝ} (hL : 0 < L) (ag : Fin 3 → Prop) [DecidablePred ag] (Qg : Fin 3 → ℝ)
    (kg : Fin 3 → ℕ) (hQ : ∀ j, ag j → 0 < Qg j) : 0 < ghostCharge L γ η ag Qg kg := by
  unfold ghostCharge
  exact Finset.prod_pos fun j hj => mul_pos (Real.rpow_pos_of_pos hL _) (hQ j (by simpa using hj))

theorem ghostConstLow_nonneg (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : 0 ≤ ghostConstLow d c η δ :=
  (constB2_nonneg d c η).trans (constB2_le_low d c hη hδ)

namespace Tri
variable {M : Molecule V D} (T : TriData M)

/-- **Cut pattern `α β`**: one ghost, at `v₂` or `v₃`. -/
theorem tri_low_ab {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (hα0 : T.IsA0) (hα1 : ¬ T.IsA1) (j0 : Fin 3) (hj0 : gh j0) (ν : ℕ) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triRHSLow T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg ν)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
  have hlab : T.alphaLabels R₀ R₁ κ₀ κ₁ = [(R₀, κ₀)] := by simp [alphaLabels, hα0, hα1]
  have hΔ : ((T.kept.numComponents : ℤ) - M.numComponents) = 1 := by rw [T.deltaF_eq]; simp [hα0, hα1]
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by rw [hΔ]; norm_num
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
  have hNb : ¬ ag s → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
    intro _ c' β k0 hP
    obtain ⟨r₀, hr₀⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 0 R₀ κ₀ hgap0 hball0 hκ₀ c' β k0 hP
    have h := T.card_αβ L γ δ hL0 H.hδ0 w Adm c' β k0 r₀ ρ₀ (T.hbeta1 hα1) (fun κ hκ => hnz κ hκ.2.2) hr₀
    exact encard_le_min_mul _ _ _ h.1 h.2
  have hNa : ag s → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg s / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
          (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
    intro hags c' β k0 hP
    obtain ⟨r₀, hr₀⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 0 R₀ κ₀ hgap0 hball0 hκ₀ c' β k0 hP
    have hQ0 : 0 < Qg s / 2 := by have := lt_of_lt_of_le (inv_pos.2 hL0) (hQl s hags); positivity
    rcases hs12 with rfl | rfl
    · exact card_αβ_A_nu T (idx_S1_of_ghost1 T (hgd 1 (hag 1 hags))) L γ δ hL0 H.hδ0 w Adm c' β k0 r₀ ρ₀
        (T.hbeta1 hα1) hr₀ (Qg 1 / 2) hQ0 (fun κ hκ => hlow 1 hags κ hκ.2.2)
    · exact card_αβ_B_nu T (idx_S1_of_ghost2 T (hgd 2 (hag 2 hags)) hα0) L γ δ hL0 H.hδ0 w Adm c' β k0 r₀ ρ₀
        (T.hbeta1 hα1) hr₀ (Qg 2 / 2) hQ0 (fun κ hκ => hlow 2 hags κ hκ.2.2)
  have key := final_B2_low T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₀ κ₀ hR₀l hR₀u ρ₀
    (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀) hlab hk gh ag hag s hs Qg kg hQl hQu hNa hNb
  unfold triRHSLow
  refine isDeviation_transfer key ?_ hL1 H.hη ν
  refine mul_nonneg (ghostConstLow_nonneg d c H.hη H.hδ0)
    (div_nonneg (excessRHS_nonneg L γ η hL0 _ ?_ _ _)
      (ghostCharge_pos hL0 ag Qg kg fun j h => lt_of_lt_of_le (inv_pos.2 hL0) (hQl j h)).le)
  rw [hlab]; intro p hp; simp at hp; rw [hp]; exact (inv_pos.2 hL0).le.trans hR₀l

/-- **Cut pattern `β α`**: one ghost, at `v₁`. -/
theorem tri_low_ba {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hb1 : κ₁ = 50 → (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁) ∨
      T.SiblingReading L w Adm (L ^ (-50 * η) * R₁))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (hα0 : ¬ T.IsA0) (hα1 : T.IsA1) (j0 : Fin 3) (hj0 : gh j0) (ν : ℕ) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triRHSLow T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg ν)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have h012 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
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
  have hNb : ¬ ag 0 → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
    intro _ c' β k0 hP
    obtain ⟨r₁, hr₁⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 1 R₁ κ₁ hgap1 hball1 hκ₁ c' β k0 hP
    have h := T.card_βα L γ δ hL0 H.hδ0 w Adm c' β k0 r₁ ρ₁ (T.hbeta0 hα0) (fun κ hκ => hnz κ hκ.2.2) hr₁
    exact encard_le_min_mul _ _ _ h.1 h.2
  have hNa : ag 0 → ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg 0 / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) *
          (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
    intro hag0 c' β k0 hP
    obtain ⟨r₁, hr₁⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 1 R₁ κ₁ hgap1 hball1 hκ₁ c' β k0 hP
    have hQ0 : 0 < Qg 0 / 2 := by have := lt_of_lt_of_le (inv_pos.2 hL0) (hQl 0 hag0); positivity
    exact card_βα_nu T L γ δ hL0 H.hδ0 w Adm c' β k0 r₁ ρ₁ (T.hbeta0 hα0) hr₁ (Qg 0 / 2) hQ0
      (fun κ hκ => hlow 0 hag0 κ hκ.2.2)
  have key := final_B2_low T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ κ₁ R₁ κ₁ hR₁l hR₁u ρ₁
    (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁) hlab hk gh ag hag 0 hs Qg kg hQl hQu hNa hNb
  unfold triRHSLow
  refine isDeviation_transfer key ?_ hL1 H.hη ν
  refine mul_nonneg (ghostConstLow_nonneg d c H.hη H.hδ0)
    (div_nonneg (excessRHS_nonneg L γ η hL0 _ ?_ _ _)
      (ghostCharge_pos hL0 ag Qg kg fun j h => lt_of_lt_of_le (inv_pos.2 hL0) (hQl j h)).le)
  rw [hlab]; intro p hp; simp at hp; rw [hp]; exact (inv_pos.2 hL0).le.trans hR₁l

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
