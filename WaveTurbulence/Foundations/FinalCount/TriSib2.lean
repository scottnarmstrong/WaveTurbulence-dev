/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriSib1
/-! Triangles, sibling part 2 (G2-SIBLING): the `ΔF = 0` deviation and the `ΔF = 1` ball reduction with a
sibling-centred `ι` ball (see `TriSib1`). -/
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

/-- **The sibling `ι` reading** (DH23 L1782 with `r'` the gap of the first cut of the same triangle): for every
admissible decoration, the gap at `v₂` is within `ρ` of `± ` the gap at `v₁`. -/
def SiblingReading (L : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (ρ : ℝ) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ κ', Adm κ' →
    ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - (s : ℝ) • Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ ρ

/-- For a first `β`-cut the first gap is a function of the parameters, so a sibling ball is a fixed ball. -/
theorem ball1_of_sib_beta {L γ δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) {ρ : ℝ} (h : T.SiblingReading L w Adm ρ)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) :
    ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ ρ := by
  obtain ⟨s, -, hs⟩ := h
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  · obtain ⟨κs, hκs⟩ := hne
    refine ⟨(s : ℝ) • Molecule.gapAt L w κs (T.a 0) (T.b 0), fun κ' hκ' => ?_⟩
    rw [← T.gap0_const_of_beta hβ0 L γ δ hL hδ w Adm c β k0 κ' κs hκ' hκs]
    exact hs κ' hκ'.2.2
  · refine ⟨0, fun κ' hκ' => absurd ⟨κ', hκ'⟩ hne⟩

/-- `ΔF = 0`, both cuts `α`-cuts, the second ball (`κ₁ = 50`) centred relative to the first gap (sibling hit). -/
theorem tri_aa_sib {d : ℕ} {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hsib1 : T.SiblingReading L w Adm (L ^ (-50 * η) * R₁))
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
    obtain ⟨s, -, hs⟩ := hsib1
    have hρ₁' : ρ₁ = L ^ (-50 * η) * R₁ := by rw [hρ₁]; simp [show κ₁ ≠ 0 by omega]
    exact T.card_αα_sib L γ δ hL0 w Adm c' β k0 r₀ ρ₀ s ρ₁ hr₀ (fun κ hκ => by rw [hρ₁']; exact hs κ hκ.2.2)
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 _ hN
  have hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((3 : ℕ) : ℤ) := by
    rw [T.deltaF_eq]; simp [hα0, hα1]
  rw [hk] at dev
  refine dev_finish dev ?_
  have h := arith_aa d κ₀ κ₁ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hC H.hδ1
    hR₀l hR₀u (rho_cases (L := L) (η := η) (R := R₀) κ₀ hκ₀)
    hR₁l hR₁u (rho_cases (L := L) (η := η) (R := R₁) κ₁ (Or.inr hκ₁))
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
