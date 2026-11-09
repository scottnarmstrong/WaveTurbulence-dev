/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone2
/-! **L6E GHOST, part 13: gap providers** (the `α`-gap sets of the creation counts, ball or cone).

A *gap provider* for the gap `j` of a triangle gives, in every parameter class, a finset of size `≤ N` containing the
`α` gap vectors of the class; a *pair provider* does the same for the pair `(gap₀, gap₁)`.
* balls (main's counts): `gapProv_ball`;
* the creation cone (Theorem 6.1 (e)): `ConeAt` (the cone hypothesis of the (f′) class NC around a centre fixed in the
  parameter class: a present atom's parameter `c_x`), `gapProv_cone`;
* pairs: `pairProv_prod`, `pairProv_sib` (main's sibling reading), `ConeRel` and `pairProv_rel` (both ghosts created by
  the same Op-2 step: the second free gap in the cone around the first). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- A gap provider of size `N` for the gap `j` of `T` on the class `Adm`. -/
def GapProv {M : Molecule V D} (T : TriData M) (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (j : Fin 3) (N : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ A : Finset (Fin d → ℤ), A.card ≤ N ∧ ∀ κ ∈ decSet M L γ δ w Adm c β k0, T.triZ κ (j - 1) - T.triZ κ j ∈ A

/-- A pair provider of size `N` for `(gap₀, gap₁)`. -/
def PairProv {M : Molecule V D} (T : TriData M) (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (N : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ B : Finset ((Fin d → ℤ) × (Fin d → ℤ)), B.card ≤ N ∧
      ∀ κ ∈ decSet M L γ δ w Adm c β k0, (T.triZ κ 2 - T.triZ κ 0, T.triZ κ 0 - T.triZ κ 1) ∈ B

/-- **The creation cone at the gap `j`** (the (f′) class NC at the creation step of the later ghost, Lemma 6.2): in
every parameter class the gap lies in the cone of aperture `θ₀ = L^{-6η}` around a fixed nonzero centre. -/
def ConeAt {M : Molecule V D} (T : TriData M) (L γ δ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (j : Fin 3) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ ctr : Mom d, ctr ≠ 0 ∧ ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
      InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ' (T.a j) (T.b j)) ctr

/-- **The relative creation cone** (both ghosts new at the same Op-2 step): `gap₁` in the cone around `gap₀`. -/
def ConeRel {M : Molecule V D} (T : TriData M) (L η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ κ', Adm κ' → InCone (L ^ (-6 * η)) (Molecule.gapAt L w κ' (T.a 1) (T.b 1)) (Molecule.gapAt L w κ' (T.a 0) (T.b 0))

/-- The cone count of a gap ball of radius `2R`. -/
noncomputable def coneCount (d : ℕ) (L η R : ℝ) : ℕ :=
  (2 * ⌊2 * R * L⌋₊ + 1) * (⌊4 * L ^ (-6 * η) * (2 * R * L)⌋₊ + 1) ^ (d - 1)

namespace Tri
variable {M : Molecule V D} (T : TriData M)

theorem gapvec_eq (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3) :
    Molecule.gapAt L w κ (T.a j) (T.b j) = latticePoint L (T.triZ κ (j - 1) - T.triZ κ j) :=
  gapAt_eq M T L w κ hκ j

/-- **The ball provider** (main's counts): radius `2R` for `κ = 0`, `L^{-50η} R` (around the fixed centre) for `κ = 50`. -/
theorem gapProv_ball {L γ η δ : ℝ} (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (j : Fin 3) (R : ℝ)
    (κ : ℕ) (hκ : κ = 0 ∨ κ = 50)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖ ≤ 2 * R)
    (hball : κ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a j) (T.b j) - r₀‖ ≤ L ^ (-50 * η) * R) :
    GapProv T L γ δ w Adm j ((⌊2 * (if κ = 0 then 2 * R else L ^ (-50 * η) * R) * L⌋₊ + 1) ^ d) := by
  intro c β k0 hP
  obtain ⟨r₀, hr₀⟩ := T.ball_of (L := L) (η := η) (δ := δ) w Adm j R κ hgap hball hκ c β k0 hP
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  · obtain ⟨κs, hκs⟩ := hne
    have hρ := T.rho_nonneg L γ δ w Adm c β k0 j r₀ _ κs hκs hr₀
    exact ⟨alphaN d L r₀ (if κ = 0 then 2 * R else L ^ (-50 * η) * R), card_alphaN_le L r₀ _ hL hρ,
      fun κ' hκ' => T.gap_mem_alphaN L hL w j r₀ _ κ' hκ'.1.1 (hr₀ κ' hκ')⟩
  · exact ⟨∅, by simp, fun κ' hκ' => absurd ⟨κ', hκ'⟩ hne⟩

/-- **The cone provider** (Theorem 6.1 (e)): a gap of size `≤ 2R` in the creation cone. -/
theorem gapProv_cone {L γ η δ : ℝ} (hL : 0 < L) (hη : 0 < η) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (j : Fin 3)
    (R : ℝ) (hR : 0 ≤ R) (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖ ≤ 2 * R)
    (hcone : ConeAt T L γ δ η w Adm j) :
    GapProv T L γ δ w Adm j (coneCount d L η R) := by
  intro c β k0 hP
  obtain ⟨ctr, hctr, hc⟩ := hcone c β k0 hP
  refine ⟨coneSet d L (2 * R) (L ^ (-6 * η)) ctr, ?_, fun κ' hκ' => ?_⟩
  · have h := card_coneSet L hL (2 * R) (L ^ (-6 * η)) (by positivity) (by positivity) ctr hctr
    unfold coneCount
    have e : 2 * R * L = 2 * R * L := rfl
    simpa [mul_assoc] using h
  · have hg := gapvec_eq T L w κ' hκ'.1.1 j
    refine mem_coneSet_of L hL _ _ ctr _ ?_ ?_
    · rw [← hg]; exact hgap κ' hκ'.2.2
    · rw [← hg]; exact hc κ' hκ'

/-- Product of two gap providers. -/
theorem pairProv_prod {L γ δ : ℝ} (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (N₀ N₁ : ℕ)
    (P0 : GapProv T L γ δ w Adm 0 N₀) (P1 : GapProv T L γ δ w Adm 1 N₁) :
    PairProv T L γ δ w Adm (N₀ * N₁) := by
  intro c β k0 hP
  obtain ⟨A₀, hA₀, h₀⟩ := P0 c β k0 hP
  obtain ⟨A₁, hA₁, h₁⟩ := P1 c β k0 hP
  refine ⟨A₀ ×ˢ A₁, by rw [Finset.card_product]; exact Nat.mul_le_mul hA₀ hA₁, fun κ hκ => ?_⟩
  rw [Finset.mem_product]
  have a0 := h₀ κ hκ; rw [fin3_zero_sub] at a0
  have a1 := h₁ κ hκ; rw [fin3_one_sub] at a1
  exact ⟨a0, a1⟩

/-- **The sibling pair provider** (main's `card_αα_sib`): `gap₁` within `ρ₁` of `s · gap₀`. -/
theorem pairProv_sib {L γ δ : ℝ} (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (N₀ : ℕ)
    (P0 : GapProv T L γ δ w Adm 0 N₀) (ρ₁ : ℝ) (hρ₁ : 0 ≤ ρ₁) (s : ℤ)
    (hs : ∀ κ', Adm κ' →
      ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - (s : ℝ) • Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ ρ₁) :
    PairProv T L γ δ w Adm (N₀ * (⌊2 * ρ₁ * L⌋₊ + 1) ^ d) := by
  intro c β k0 hP
  obtain ⟨A₀, hA₀, h₀⟩ := P0 c β k0 hP
  refine ⟨(A₀ ×ˢ alphaN d L (0 : Mom d) ρ₁).image (fun p => (p.1, p.2 + s • p.1)), ?_, fun κ hκ => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product]
    exact Nat.mul_le_mul hA₀ (card_alphaN_le L 0 ρ₁ hL hρ₁)
  · rw [Finset.mem_image]
    have a0 := h₀ κ hκ; rw [fin3_zero_sub] at a0
    refine ⟨(T.triZ κ 2 - T.triZ κ 0, (T.triZ κ 0 - T.triZ κ 1) - s • (T.triZ κ 2 - T.triZ κ 0)), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨a0, mem_alphaN_of_norm_le L hL _ _ _ ?_⟩
      have h := hs κ hκ.2.2
      have hg0 := gapAt_eq M T L w κ hκ.1.1 0
      have hg1 := gapAt_eq M T L w κ hκ.1.1 1
      rw [fin3_zero_sub] at hg0
      rw [fin3_one_sub] at hg1
      rw [hg0, hg1, ← latticePoint_sub_smul] at h
      simpa using h
    · simp only [Prod.mk.injEq, true_and]
      funext k; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **The relative cone pair provider**: `gap₀` from a provider (nonzero), `gap₁` of size `≤ 2R₁` in the cone around
`gap₀`. -/
theorem pairProv_rel {L γ η δ : ℝ} (hL : 0 < L) (hη : 0 < η) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (N₀ : ℕ)
    (P0 : GapProv T L γ δ w Adm 0 N₀) (R₁ : ℝ) (hR₁ : 0 ≤ R₁)
    (hnz0 : ∀ κ', Adm κ' → Molecule.gapAt L w κ' (T.a 0) (T.b 0) ≠ 0)
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hrel : ConeRel T L η w Adm) :
    PairProv T L γ δ w Adm (N₀ * coneCount d L η R₁) := by
  intro c β k0 hP
  obtain ⟨A₀, hA₀, h₀⟩ := P0 c β k0 hP
  refine ⟨(A₀.filter fun n => n ≠ 0).biUnion fun n₀ =>
      (coneSet d L (2 * R₁) (L ^ (-6 * η)) (latticePoint L n₀)).image fun n₁ => (n₀, n₁), ?_, fun κ hκ => ?_⟩
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ n₀ ∈ A₀.filter (fun n => n ≠ 0), ((coneSet d L (2 * R₁) (L ^ (-6 * η)) (latticePoint L n₀)).image
          fun n₁ => (n₀, n₁)).card
        ≤ ∑ _n₀ ∈ A₀.filter (fun n => n ≠ 0), coneCount d L η R₁ := by
          refine Finset.sum_le_sum fun n₀ hn₀ => Finset.card_image_le.trans ?_
          have hne : latticePoint L n₀ ≠ 0 := by
            intro h0
            exact (Finset.mem_filter.1 hn₀).2 (latticePoint_injective L hL.ne' (h0.trans (latticePoint_zero' L).symm))
          have h := card_coneSet L hL (2 * R₁) (L ^ (-6 * η)) (by positivity) (by positivity) _ hne
          unfold coneCount
          simpa [mul_assoc] using h
      _ ≤ N₀ * coneCount d L η R₁ := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul ((Finset.card_filter_le _ _).trans hA₀) le_rfl
  · have a0 := h₀ κ hκ; rw [fin3_zero_sub] at a0
    have hg0 := gapAt_eq M T L w κ hκ.1.1 0
    have hg1 := gapAt_eq M T L w κ hκ.1.1 1
    rw [fin3_zero_sub] at hg0
    rw [fin3_one_sub] at hg1
    rw [Finset.mem_biUnion]
    refine ⟨T.triZ κ 2 - T.triZ κ 0, Finset.mem_filter.2 ⟨a0, fun h => ?_⟩, ?_⟩
    · apply hnz0 κ hκ.2.2; rw [hg0, h, latticePoint_zero']
    · rw [Finset.mem_image]
      refine ⟨T.triZ κ 0 - T.triZ κ 1, mem_coneSet_of L hL _ _ _ _ ?_ ?_, rfl⟩
      · rw [← hg1]; exact hgap1 κ hκ.2.2
      · have := hrel κ hκ.2.2; rwa [hg0, hg1] at this

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
