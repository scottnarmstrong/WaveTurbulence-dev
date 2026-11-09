/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Triangle2
/-! **L6E GHOST, part 14: the creation leaves with gap providers** (Theorem 6.1 (e) at an Op-2 step).

Each leaf is main's (or L6E's) leaf of the triangle step creating `α`-atoms, with the `α`-gap ball replaced by a
provider of size `N` and a ratio `N ≤ X · (ball count)`: the deviation bound is main's times `X`. With the ball
provider `X = 1`; with the cone provider `X = 3·5^{d-1} θ₀^{d-1} ≤ 3·5^d L^{-12η}` (`coneSet_ratio`, `coneFactor_le`).
* `dev_ratio`: the combinator (from main's `tri_dev_of_arith`);
* `leaf_ab_prov`, `leaf_ba_prov`, `leaf_aa_prov`: ghost-free triangles creating one or two `α`-atoms;
* `final_B2_prov`: the two-block tail (one new `α`-atom, one ghost), cf. `final_B2_low`. -/
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

/-- **The ratio combinator.** A count `Nc ≤ X · Nb` and main's arithmetic for `Nb` give the deviation `X · target`. -/
theorem dev_ratio {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (Nc Nb k : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤ Nc)
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = (k : ℤ)) (X target : ℝ) (hX : 0 ≤ X)
    (hratio : (Nc : ℝ) ≤ X * Nb)
    (harith : (Nb : ℝ) * rankFactor d L γ δ C₁ (k : ℤ) * Real.log L ^ 12 ≤ target) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P) (ENNReal.ofReal (X * target)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  refine T.tri_dev_of_arith H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 Nc k hN hk _ ?_
  have hrf : 0 ≤ rankFactor d L γ δ C₁ (k : ℤ) := by
    rw [rankFactor_nat d L γ δ C₁ hL0 k]
    have := qq_nonneg H.hδ0.le (zero_le_one.trans H.hC)
    positivity
  have hlog : 0 ≤ Real.log L ^ 12 := pow_nonneg (Real.log_nonneg hL1) _
  calc (Nc : ℝ) * rankFactor d L γ δ C₁ (k : ℤ) * Real.log L ^ 12
      ≤ (X * Nb) * rankFactor d L γ δ C₁ (k : ℤ) * Real.log L ^ 12 := by gcongr
    _ = X * ((Nb : ℝ) * rankFactor d L γ δ C₁ (k : ℤ) * Real.log L ^ 12) := by ring
    _ ≤ X * target := mul_le_mul_of_nonneg_left harith hX

/-- **Ghost-free `α β` with a provider for `gap₀`** (main's `tri_ab`). -/
theorem leaf_ab_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ : ℝ) (κ₀ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η))
    (N₀ : ℕ) (P₀ : GapProv T L γ δ w Adm 0 N₀) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N₀ : ℝ) ≤ X * ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hα0 : T.IsA0) (hα1 : ¬ T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * (triConst d c η δ * excessRHS L γ η [(R₀, κ₀)] 1 2))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  set ρ₀ : ℝ := if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀ with hρ₀
  set F : ℕ := min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) with hF
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤ ((F * N₀ : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    obtain ⟨A, hA, hmem⟩ := P₀ c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    have hA' : ∀ κ ∈ decSet M L γ δ w Adm c' β k0, T.triZ κ 2 - T.triZ κ 0 ∈ A := fun κ hκ => by
      have := hmem κ hκ; rwa [fin3_zero_sub] at this
    have hr : 0 ≤ slabR M L γ δ := by unfold slabR; have := H.hδ0; positivity
    have key : ∀ (n : Fin d → ℤ) (f : (Fin d → ℤ) × (Fin d → ℤ) → (Fin 3 → (Fin d → ℤ))), n ≠ 0 →
        T.tripleSet L γ δ w Adm c' β k0 ⊆ f '' ((slabF d n ⌊2 * L⌋₊ (slabR M L γ δ) ×ˢ A : Finset _) : Set _) →
        (T.tripleSet L γ δ w Adm c' β k0).encard ≤ ((F * N₀ : ℕ) : ℕ∞) := by
      intro n f hn hsub
      obtain ⟨h1, h2, -⟩ := encard_slab_prod L hL0 _ f n _ hr A hsub
      have h1' := h1 hn
      have hA0 : (A.card : ℕ∞) ≤ N₀ := by exact_mod_cast hA
      rw [hF]
      refine (encard_le_min_mul _ _ _ h1' h2).trans ?_
      exact_mod_cast Nat.mul_le_mul le_rfl hA
    rcases T.idx_S1_cases with hi | hi
    · refine key _ _ ?_ (sub_αβ_A_gen T hi L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta1 hα1) A hA' κs hκs)
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 1 (hnz κs hκs.2.2 1)
      rwa [fin3_one_sub] at h
    · refine key _ _ ?_ (sub_αβ_B_gen T hi L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta1 hα1) A hA' κs hκs)
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 2 (hnz κs hκs.2.2 2)
      rw [fin3_two_sub] at h
      intro e; apply h; rw [← neg_sub, e, neg_zero]
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  refine dev_ratio T H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ (F * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d) 2 hN hk X _ hX
    ?_ ?_
  · push_cast
    calc (F : ℝ) * N₀ ≤ F * (X * ((⌊2 * ρ₀ * L⌋₊ + 1 : ℕ) : ℝ) ^ d) := by gcongr
      _ = X * (F * ((⌊2 * ρ₀ * L⌋₊ : ℝ) + 1) ^ d) := by push_cast; ring
  · have h := arith_ba d c κ₀ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn
      hR₀l hR₀u (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀)
    have hRp : 0 < R₀ := lt_of_lt_of_le (inv_pos.2 hL0) hR₀l
    have hex : 0 ≤ excessRHS L γ η [(R₀, κ₀)] 1 2 := by rw [excessRHS_ba L γ η R₀ κ₀ hL0]; positivity
    rw [hF]; unfold slabR
    calc _ = (((min ((⌊2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
          ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ₀ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
            Real.log L ^ 12 := by push_cast; ring
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_ba d c H.hη H.hδ0) hex

/-- **Ghost-free `β α` with a provider for `gap₁`** (main's `tri_ba`). -/
theorem leaf_ba_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₁ : ℝ) (κ₁ : ℕ) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (N₁ : ℕ) (P₁ : GapProv T L γ δ w Adm 1 N₁) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N₁ : ℝ) ≤ X * ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hα0 : ¬ T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * (triConst d c η δ * excessRHS L γ η [(R₁, κ₁)] 1 2))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  set ρ₁ : ℝ := if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁ with hρ₁
  set F : ℕ := min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) with hF
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤ ((F * N₁ : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    obtain ⟨A, hA, hmem⟩ := P₁ c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    have hA' : ∀ κ ∈ decSet M L γ δ w Adm c' β k0, T.triZ κ 0 - T.triZ κ 1 ∈ A := fun κ hκ => by
      have := hmem κ hκ; rwa [fin3_one_sub] at this
    have hr : 0 ≤ slabR M L γ δ := by unfold slabR; have := H.hδ0; positivity
    have hsub := sub_βα_gen T L γ δ hL0 H.hδ0 w Adm c' β k0 (T.hbeta0 hα0) A hA' κs hκs
    obtain ⟨h1, h2, -⟩ := encard_slab_prod L hL0 _ _ _ _ hr A hsub
    have hn0 : T.triZ κs 0 - T.triZ κs 2 ≠ 0 := by
      have h := T.nz_vec L hL0.ne' w κs hκs.1.1 0 (hnz κs hκs.2.2 0)
      rwa [fin3_zero_sub] at h
    rw [hF]
    refine (encard_le_min_mul _ _ _ (h1 hn0) h2).trans ?_
    exact_mod_cast Nat.mul_le_mul le_rfl hA
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  refine dev_ratio T H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _ (F * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) 2 hN hk X _ hX
    ?_ ?_
  · push_cast
    calc (F : ℝ) * N₁ ≤ F * (X * ((⌊2 * ρ₁ * L⌋₊ + 1 : ℕ) : ℝ) ^ d) := by gcongr
      _ = X * (F * ((⌊2 * ρ₁ * L⌋₊ : ℝ) + 1) ^ d) := by push_cast; ring
  · have h := arith_ba d c κ₁ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1 H.hC (Nat.cast_nonneg _) hn
      hR₁l hR₁u (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁)
    have hRp : 0 < R₁ := lt_of_lt_of_le (inv_pos.2 hL0) hR₁l
    have hex : 0 ≤ excessRHS L γ η [(R₁, κ₁)] 1 2 := by rw [excessRHS_ba L γ η R₁ κ₁ hL0]; positivity
    rw [hF]; unfold slabR
    calc _ = (((min ((⌊2 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
          ((2 * ⌊2 * L⌋₊ + 1) ^ d) * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d : ℕ)) : ℝ) * rankFactor d L γ δ C₁ ((2 : ℕ) : ℤ) *
            Real.log L ^ 12 := by push_cast; ring
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (triConst_ge_ba d c H.hη H.hδ0) hex

/-- **`α α` with a pair provider** (main's `tri_aa`, `tri_aa_sib`). -/
theorem leaf_aa_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (N : ℕ) (PP : PairProv T L γ δ w Adm N) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N : ℝ) ≤ X * (((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1 : ℕ) : ℝ) ^ d *
      ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ + 1 : ℕ) : ℝ) ^ d))
    (hα0 : T.IsA0) (hα1 : T.IsA1) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * (triConst d c η δ * excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  set ρ₀ : ℝ := if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀ with hρ₀
  set ρ₁ : ℝ := if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁ with hρ₁
  have hN : ∀ (c' : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c' k0 →
      (T.tripleSet L γ δ w Adm c' β k0).encard ≤ (((2 * ⌊2 * L⌋₊ + 1) ^ d * N : ℕ) : ℕ∞) := by
    intro c' β k0 hP
    obtain ⟨B, hB, hmem⟩ := PP c' β k0 hP
    by_cases hne : (decSet M L γ δ w Adm c' β k0).Nonempty
    swap
    · rw [T.tripleSet_empty L γ δ w Adm c' β k0 hne]; simp
    obtain ⟨κs, hκs⟩ := hne
    have h := encard_box_prod L _ _ B (sub_αα_gen T L γ δ hL0 w Adm c' β k0 B hmem κs hκs)
    refine h.trans ?_
    exact_mod_cast Nat.mul_le_mul le_rfl hB
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((3 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  refine dev_ratio T H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _
    ((2 * ⌊2 * L⌋₊ + 1) ^ d * ((⌊2 * ρ₀ * L⌋₊ + 1) ^ d * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d)) 3 hN hk X _ hX ?_ ?_
  · push_cast
    have hb : (0 : ℝ) ≤ (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d := by positivity
    calc (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d * N
        ≤ (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ d * (X * (((⌊2 * ρ₀ * L⌋₊ + 1 : ℕ) : ℝ) ^ d *
            ((⌊2 * ρ₁ * L⌋₊ + 1 : ℕ) : ℝ) ^ d)) := mul_le_mul_of_nonneg_left hratio hb
      _ = _ := by push_cast; ring
  · have h := arith_aa d κ₀ κ₁ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hC H.hδ1
      hR₀l hR₀u (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀)
      hR₁l hR₁u (rho_cases (L := L) (η := η) (R := R₁) κ₁ hκ₁)
    have hRp₀ : 0 < R₀ := lt_of_lt_of_le (inv_pos.2 hL0) hR₀l
    have hRp₁ : 0 < R₁ := lt_of_lt_of_le (inv_pos.2 hL0) hR₁l
    have hex : 0 ≤ excessRHS L γ η [(R₀, κ₀), (R₁, κ₁)] 0 1 := by
      rw [excessRHS_aa L γ η R₀ R₁ κ₀ κ₁ hL0]; positivity
    exact h.trans (mul_le_mul_of_nonneg_right (triConst_ge_aa d c H.hη H.hδ0) hex)

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
