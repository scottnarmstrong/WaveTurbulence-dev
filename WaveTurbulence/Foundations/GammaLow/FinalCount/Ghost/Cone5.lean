/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone4
/-! **L6E GHOST, part 15: the creating cut patterns with gap providers, in the triangle-bound form.**

For a triangle step creating `α`-atoms (cut patterns `α β`, `β α`, `α α`; at most one ghost, which is never an `α`-ghost
pair, so no `PairOK` is needed), the charged bound of `triangle_excess_ghost_low` (with `ν = 0`) holds with the gap balls
replaced by providers, multiplied by the providers' ratio `X`.
* `leaf_B2_alpha_prov`, `leaf_B2_beta_prov`, `final_B2_prov`: the two-block tail (cf. `final_B2_low`);
* `cone_ab`, `cone_ba`, `cone_aa`: the right-hand side `X · ghostConstLow · excessRHS(…) / ghostCharge`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The triangle right-hand side without transfer (`triRHSLow … 0` without its last factor). -/
noncomputable def triRHS0 {M : Molecule V D} (T : TriData M) (d c : ℕ) (L γ η δ : ℝ) (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) : ℝ :=
  ghostConstLow d c η δ *
    (excessRHS L γ η (T.alphaLabels R₀ R₁ κ₀ κ₁)
      ((T.kept.numComponents : ℤ) - M.numComponents - ((Finset.univ.filter gh).card : ℤ))
      (3 - ((T.alphaLabels R₀ R₁ κ₀ κ₁).length : ℤ) - ((Finset.univ.filter gh).card : ℤ) -
        ((Finset.univ.filter fun j => gh j ∧ ¬ ag j).card : ℤ)) /
      ghostCharge L γ η ag Qg kg)

namespace Tri
variable {M : Molecule V D} (T : TriData M)

theorem triRHS0_nonneg {L γ η δ : ℝ} (hL : 0 < L) (hη : 0 < η) (hδ : 0 < δ) (c : ℕ) (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁) (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag]
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQ : ∀ j, ag j → 0 < Qg j) :
    0 ≤ triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg := by
  unfold triRHS0
  refine mul_nonneg (ghostConstLow_nonneg d c hη hδ)
    (div_nonneg (excessRHS_nonneg L γ η hL _ ?_ _ _) (ghostCharge_pos hL ag Qg kg hQ).le)
  intro p hp
  unfold alphaLabels at hp
  simp only [List.mem_append] at hp
  rcases hp with hp | hp <;> (split_ifs at hp <;> simp at hp)
  · rcases hp with rfl; exact hR₀
  · rcases hp with rfl; exact hR₁

/-- Two blocks, `α`-ghost, provider `N` for the new gap (ghost-label slab). -/
theorem leaf_B2_alpha_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (Qg : ℝ) (κg : ℕ) (hQl : L⁻¹ ≤ Qg) (hQu : Qg ≤ L ^ (-γ + η))
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ)) (N : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N : ℝ) ≤ X * ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        (((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * N : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * (constB2 d c η *
        (excessRHS L γ η [(R, κ)] 0 1 / (L ^ ((γ + 3 * η) / 2 - (κg : ℝ) * η) * Qg))))) := by
  refine dev_ratio T H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _
    ((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1) * (⌊2 * ρ * L⌋₊ + 1) ^ d) 2 hN hk
    X _ hX ?_ ?_
  · push_cast
    have h0 : (0 : ℝ) ≤ ((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ : ℝ) + 1) * (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 1) := by
      positivity
    push_cast at hratio
    calc ((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ : ℝ) + 1) * (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 1) * N
        ≤ ((⌊2 * slabR M L γ δ / (Qg / 2 * L / d)⌋₊ : ℝ) + 1) * (2 * (⌊2 * L⌋₊ : ℝ) + 1) ^ (d - 1) *
          (X * ((⌊2 * ρ * L⌋₊ : ℝ) + 1) ^ d) := mul_le_mul_of_nonneg_left hratio h0
      _ = _ := by ring
  · have h := arith_B2_alpha_low d (na := (M.atoms.card : ℝ)) c κ κg H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0
      H.hδ1 H.hC (Nat.cast_nonneg _) hn hRl hRu hρ hQl hQu
    unfold slabR
    exact h

/-- Two blocks, `β`-ghost, provider `N` for the new gap (main's count). -/
theorem leaf_B2_beta_prov {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (κ : ℕ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = ((2 : ℕ) : ℤ)) (N : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hratio : (N : ℝ) ≤ X * ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) ^ d)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤
        ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) * N : ℕ) : ℕ∞)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (X * ((3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12)) *
        excessRHS L γ η [(R, κ)] 0 0))) := by
  refine dev_ratio T H hM w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 _
    (min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) *
      (⌊2 * ρ * L⌋₊ + 1) ^ d) 2 hN hk X _ hX ?_ ?_
  · have h0 : (0 : ℝ) ≤ ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1))
        ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Nat.cast_mul, Nat.cast_mul]
    calc ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) * N
        ≤ ((min ((⌊2 * slabR M L γ δ⌋₊ + 1) * (2 * ⌊2 * L⌋₊ + 1) ^ (d - 1)) ((2 * ⌊2 * L⌋₊ + 1) ^ d) : ℕ) : ℝ) *
          (X * ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) ^ d) := mul_le_mul_of_nonneg_left hratio h0
      _ = _ := by push_cast; ring
  · have h := arith_B2_beta_low d (na := (M.atoms.card : ℝ)) c κ H.hd H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 H.hL H.hδ0 H.hδ1
      H.hC (Nat.cast_nonneg _) hn hRl hRu hρ
    unfold slabR
    exact h

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
