/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GhostArith3
/-! G2-GHOST part 7: the combinators of the charged triangle bound. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The constant of the charged ghost-aware triangle bound (depends on `d, c, η, δ` only). -/
noncomputable def ghostConst (d c : ℕ) (η δ : ℝ) : ℝ :=
  3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) +
    9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) +
    3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) + triConst d c η δ

theorem triConst_nonneg (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : 0 ≤ triConst d c η δ := by
  unfold triConst; positivity

theorem ghostConst_ge_triConst (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    triConst d c η δ ≤ ghostConst d c η δ := by
  unfold ghostConst
  have : 0 ≤ 3 * (5:ℝ) ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) := by positivity
  have : 0 ≤ 9 * (d:ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have : 0 ≤ 3 * (5:ℝ) ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  linarith

theorem ghostConst_ge_S1 (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    3 * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) ≤ ghostConst d c η δ := by
  unfold ghostConst
  have := triConst_nonneg d c hη hδ
  have : 0 ≤ 9 * (d:ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  have : 0 ≤ 3 * (5:ℝ) ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  linarith

theorem ghostConst_ge_S2 (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    9 * d * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ ghostConst d c η δ := by
  unfold ghostConst
  have := triConst_nonneg d c hη hδ
  have : 0 ≤ 3 * (5:ℝ) ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) := by positivity
  have : 0 ≤ 3 * (5:ℝ) ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  linarith

theorem ghostConst_ge_S4 (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    3 * 5 ^ d * 5 ^ d * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) ≤ ghostConst d c η δ := by
  unfold ghostConst
  have := triConst_nonneg d c hη hδ
  have : 0 ≤ 3 * (5:ℝ) ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / (η ^ 2 / 2)) ^ (c + 12) := by positivity
  have : 0 ≤ 9 * (d:ℝ) * 5 ^ d * δ ^ (-(1 / 2 : ℝ)) * (((c + 12 : ℕ) : ℝ) / η ^ 2) ^ (c + 12) := by positivity
  linarith

/-- The charge of the `α`-ghosts: `∏ T(Q_g, κ_g)`. -/
noncomputable def ghostCharge (L γ η : ℝ) (ag : Fin 3 → Prop) [DecidablePred ag] (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) :
    ℝ :=
  ∏ j ∈ Finset.univ.filter ag, (L ^ ((γ + 3 * η) / 2 - (kg j : ℝ) * η) * Qg j)

theorem excessRHS_nonneg (L γ η : ℝ) (hL : 0 < L) (αs : List (ℝ × ℕ)) (hαs : ∀ p ∈ αs, 0 ≤ p.1)
    (ΔF ΔVβ : ℤ) : 0 ≤ excessRHS L γ η αs ΔF ΔVβ := by
  unfold excessRHS
  have : 0 ≤ (αs.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact mul_nonneg (Real.rpow_nonneg hL.le _) (hαs p hp)
  positivity

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- **Combinator.** A bound `N` on the triples and the arithmetic inequality give the deviation. -/
theorem tri_dev_of_arith {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (N k : ℕ)
    (hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (T.tripleSet L γ δ w Adm c β k0).encard ≤ N)
    (hk : (3 - ((T.kept.numComponents : ℤ) - M.numComponents)) = (k : ℤ)) (target : ℝ)
    (harith : (N : ℝ) * rankFactor d L γ δ C₁ (k : ℤ) * Real.log L ^ 12 ≤ target) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P) (ENNReal.ofReal target) := by
  have dev := T.tri_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P H.hL H.hδ0 H.hC hP0 hP1 hP2 hP3 N hN
  rw [hk] at dev
  exact dev_finish dev (by rw [← mul_assoc]; exact harith)

end TriData
end WaveTurbulence.FinalCount
