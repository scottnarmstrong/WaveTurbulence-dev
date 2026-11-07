/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriDev2
/-! Triangles, part 22 (FINALCOUNT-G2): DH23 Prop 9.4 for the triangle step (L1777--L1779, L1793--L1796). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- The constant of Prop 9.4 for a triangle (depends on `d, c, η, δ` only). -/
noncomputable def triConst (d c : ℕ) (η δ : ℝ) : ℝ :=
  3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) +
    3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) +
    5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12

theorem dev_finish {A A' : ℝ≥0∞} {N : ℕ} {x y : ℝ} (h : IsDeviation A A' ((N : ℝ≥0∞) * ENNReal.ofReal x))
    (hxy : (N : ℝ) * x ≤ y) : IsDeviation A A' (ENNReal.ofReal y) := by
  refine isDeviation_mono h ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hxy

theorem encard_le_min_mul {e : ℕ∞} (a b c : ℕ) (h1 : e ≤ ((a * c : ℕ) : ℕ∞)) (h2 : e ≤ ((b * c : ℕ) : ℕ∞)) :
    e ≤ ((min a b * c : ℕ) : ℕ∞) := by
  rcases min_choice a b with h | h <;> rw [h]
  · exact h1
  · exact h2

theorem encard_le_min {e : ℕ∞} (a b : ℕ) (h1 : e ≤ (a : ℕ∞)) (h2 : e ≤ (b : ℕ∞)) : e ≤ ((min a b : ℕ) : ℕ∞) := by
  rcases min_choice a b with h | h <;> rw [h]
  · exact h1
  · exact h2

theorem triConst_ge_bb (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ triConst d c η δ := by
  unfold triConst
  have : 0 ≤ 3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have : 0 ≤ 5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12 := by positivity
  linarith

theorem triConst_ge_ba (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ triConst d c η δ := by
  unfold triConst
  have : 0 ≤ 3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have : 0 ≤ 5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12 := by positivity
  linarith

theorem triConst_ge_aa (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    5 ^ d * 5 ^ d * 5 ^ d * ((((12 : ℕ)) : ℝ) / η ^ 2) ^ 12 ≤ triConst d c η δ := by
  unfold triConst
  have : 0 ≤ 3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have : 0 ≤ 3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  linarith

/-- The standing real parameters of Prop 9.4. -/
structure TriReal (d : ℕ) (L γ η δ C₁ : ℝ) : Prop where
  hd : 3 ≤ d
  hγ0 : 0 < γ
  hγ1 : γ < 1
  hη : 0 < η
  hη1 : 200 * η ≤ γ
  hη2 : 200 * η ≤ 1 - γ
  hL : Real.exp 1 ≤ L
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1
  hC : 1 ≤ C₁

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The labelled `α`-atoms created by the triangle step (L1779). -/
noncomputable def alphaLabels (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) : List (ℝ × ℕ) :=
  (if T.IsA0 then [(R₀, κ₀)] else []) ++ (if T.IsA1 then [(R₁, κ₁)] else [])


theorem hbeta0 (hα0 : ¬ T.IsA0) : ¬ T.m1.SameComponent (T.t 0) (T.f 0) :=
  fun hs => hα0 ((isAlphaCut_iff M T.cd1).2 hs)

theorem hbeta1 (hα1 : ¬ T.IsA1) : ¬ T.m2.SameComponent (T.t 1) (T.f 1) :=
  fun hs => hα1 ((isAlphaCut_iff T.m1 T.cd2).2 hs)

/-- `ΔF = 2`: both cuts are `β`-cuts. -/
theorem tri_bb {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (hα0 : ¬ T.IsA0) (hα1 : ¬ T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ * excessRHS L γ η [] 2 3)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hL0 : 0 < L := by linarith
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    have h := T.card_ββ L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) (T.hbeta1 hα1)
      (fun κ hκ => hnz κ hκ.2.2 0)
    exact encard_le_min _ _ h.1 h.2
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 _ hN
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((1 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  rw [hk] at dev
  refine dev_finish dev ?_
  have h := arith_bb d c H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn
  have hex : 0 ≤ excessRHS L γ η [] 2 3 := by rw [excessRHS_bb L γ η hL0]; positivity
  unfold slabR
  calc _ = (((min ((⌊2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((1 : ℕ) : ℤ) * Real.log L ^ 12 := by ring
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_bb d c H.hη H.hδ0) hex

theorem ball_of {d : ℕ} {L γ η δ : ℝ} (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (j : Fin 3) (R : ℝ) (κ : ℕ)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖ ≤ 2 * R)
    (hball : κ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a j) (T.b j) - r₀‖ ≤ L ^ (-50 * η) * R)
    (hκ : κ = 0 ∨ κ = 50) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (hP : ParamOK M c k0) :
    ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
      ‖Molecule.gapAt L w κ' (T.a j) (T.b j) - r₀‖ ≤ (if κ = 0 then 2 * R else L ^ (-50 * η) * R) := by
  by_cases h0 : κ = 0
  · refine ⟨0, fun κ' hκ' => ?_⟩
    rw [if_pos h0, sub_zero]; exact hgap κ' hκ'.2.2
  · have h50 : κ = 50 := hκ.resolve_left h0
    obtain ⟨r₀, hr⟩ := hball h50 c β k0 hP
    exact ⟨r₀, fun κ' hκ' => by rw [if_neg h0]; exact hr κ' hκ'⟩

theorem rho_cases {L η R : ℝ} (κ : ℕ) (hκ : κ = 0 ∨ κ = 50) :
    (κ = 0 ∧ (if κ = 0 then 2 * R else L ^ (-50 * η) * R) = 2 * R) ∨
      (κ = 50 ∧ (if κ = 0 then 2 * R else L ^ (-50 * η) * R) = L ^ (-50 * η) * R) := by
  rcases hκ with h | h
  · left; exact ⟨h, by rw [if_pos h]⟩
  · right; refine ⟨h, ?_⟩; rw [if_neg (by omega)]

/-- `ΔF = 1`: the first cut is a `β`-cut, the second an `α`-cut. -/
theorem tri_ba {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₁ : ℝ) (κ₁ : ℕ) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hball1 : κ₁ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁)
    (hα0 : ¬ T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ * excessRHS L γ η [(R₁, κ₁)] 1 2)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hL0 : 0 < L := by linarith
  set ρ₁ : ℝ := if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁ with hρ₁
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
          (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    obtain ⟨r₁, hr₁⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 1 R₁ κ₁ hgap1 hball1 hκ₁ c' β k0 hP
    have h := T.card_βα L γ δ hL0 H.hδ0 w Adm c' β k0 r₁ ρ₁ (T.hbeta0 hα0)
      (fun κ hκ => hnz κ hκ.2.2) hr₁
    exact encard_le_min_mul _ _ _ h.1 h.2
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 _ hN
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  rw [hk] at dev
  refine dev_finish dev ?_
  have h := arith_ba d c κ₁ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn
    hR₁l hR₁u (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁)
  have hRp : 0 < R₁ := lt_of_lt_of_le (inv_pos.2 hL0) hR₁l
  have hex : 0 ≤ excessRHS L γ η [(R₁, κ₁)] 1 2 := by rw [excessRHS_ba L γ η R₁ κ₁ hL0]; positivity
  unfold slabR
  calc _ = (((min ((⌊2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) * Real.log L ^ 12 := by ring
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_ba d c H.hη H.hδ0) hex

/-- `ΔF = 1`: the first cut is an `α`-cut, the second a `β`-cut. -/
theorem tri_ab {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ : ℝ) (κ₀ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hα0 : T.IsA0) (hα1 : ¬ T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ * excessRHS L γ η [(R₀, κ₀)] 1 2)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hL0 : 0 < L := by linarith
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
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 _ hN
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  rw [hk] at dev
  refine dev_finish dev ?_
  have h := arith_ba d c κ₀ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn
    hR₀l hR₀u (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀)
  have hRp : 0 < R₀ := lt_of_lt_of_le (inv_pos.2 hL0) hR₀l
  have hex : 0 ≤ excessRHS L γ η [(R₀, κ₀)] 1 2 := by rw [excessRHS_ba L γ η R₀ κ₀ hL0]; positivity
  unfold slabR
  calc _ = (((min ((⌊2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) * Real.log L ^ 12 := by ring
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_ba d c H.hη H.hδ0) hex

/-- `ΔF = 0`: both cuts are `α`-cuts. -/
theorem tri_aa {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hball1 : κ₁ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁)
    (hα0 : T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triConst d c η δ * excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hL0 : 0 < L := by linarith
  set ρ₀ : ℝ := if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀ with hρ₀
  set ρ₁ : ℝ := if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁ with hρ₁
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤
        (((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    obtain ⟨r₀, hr₀⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 0 R₀ κ₀ hgap0 hball0 hκ₀ c' β k0 hP
    obtain ⟨r₁, hr₁⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm 1 R₁ κ₁ hgap1 hball1 hκ₁ c' β k0 hP
    exact T.card_αα L γ δ hL0 w Adm c' β k0 r₀ ρ₀ r₁ ρ₁ hr₀ hr₁
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 _ hN
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((3 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  rw [hk] at dev
  refine dev_finish dev ?_
  have h := arith_aa d κ₀ κ₁ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hC H.hδ1
    hR₀l hR₀u (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀)
    hR₁l hR₁u (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁)
  have hRp₀ : 0 < R₀ := lt_of_lt_of_le (inv_pos.2 hL0) hR₀l
  have hRp₁ : 0 < R₁ := lt_of_lt_of_le (inv_pos.2 hL0) hR₁l
  have hex : 0 ≤ excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1 := by
    rw [excessRHS_aa L γ η R₀ R₁ κ₀ κ₁ hL0]; positivity
  calc _ = (((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) : ℕ) : ℝ) *
        rankFactor d L γ δ C₁ ((3 : ℕ) : ℤ) * Real.log L ^ 12 := by ring
    _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_aa d c H.hη H.hδ0) hex

end TriData
end WaveTurbulence.FinalCount
