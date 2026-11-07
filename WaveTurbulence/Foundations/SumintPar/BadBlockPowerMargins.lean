/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExponentMargins
public import WaveTurbulence.Foundations.SumintPar.BadMultiplicity

/-!
# Bad-block reserves and the final source weight budget

The small first-pair term uses the trivial linear bound. The Weyl term
uses the better linear branch, losing only gammaBase relative to the
ordinary linear scale. A 9/10--1/10 comparison with the incoherence
bound retains a strict bad reserve and beta/20. Case-(d) costs are paid
by the actual source weight multiplicity, including gamma close to one.
These are numerical inequalities; the source mass bounds are separate.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- The first-pair Weyl contribution has at least three basic gains before eta loss. -/
theorem bad_pair_weyl_reserve {d : ℕ} (hd : 3 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) :
    3*gammaBase γ ≤ 2*((d:ℝ)-1)*(1-γ)-gammaBase γ := by
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hb : gammaBase γ ≤ 1-γ := min_le_right _ _
  have hm := mul_nonneg (show 0 ≤ 2*((d:ℝ)-1)-4 by linarith only [hdR])
    (show 0 ≤ 1-γ by linarith [hγ.2])
  nlinarith only [hb,hm]

/-- The fractional first-pair stationary term retains half a basic bad-block gain. -/
theorem case_c_stationary_reserve {γ η : ℝ} (hγ : γ ∈ Set.Ioo (0:ℝ) 1)
    (hη : η ≤ 1/12) : gammaBase γ / 2 ≤ γ*(1-6*η) := by
  have hb : gammaBase γ ≤ γ := min_le_left _ _
  have hm := mul_nonneg hγ.1.le (show 0 ≤ 1/2-6*η by linarith only [hη])
  nlinarith only [hb,hm]

/-- Comparing a strong bad estimate and the pair incoherence estimate keeps both gains. -/
theorem bad_incoherence_comparison_reserve (γ β : ℝ) :
    (9/10:ℝ)*(gammaBase γ/2)+(1/10:ℝ)*(-gammaBase γ+β/2) ≥
      gammaBase γ/4+β/20+gammaBase γ/10 := by ring_nf; exact le_rfl

/-- The numerical source weight budget pays every case-(d) block and still decays in both counts. -/
theorem bad_weight_total_reserve {d : ℕ} (hd : 2 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hs : Real.sqrt η ≤ gammaBase γ/8)
    (B D W : ℕ) (hDW : D ≤ W) :
    -(gammaBase γ/4)*((B:ℝ)-(D:ℝ))+(3*gammaBase γ/2)*(D:ℝ)-
        (gammaWeight d γ-Real.sqrt η)*(W:ℝ) ≤
      -(gammaBase γ/8)*((B:ℝ)+(W:ℝ)) := by
  have hb := (gammaBase_pos hγ).le
  have hw := two_gammaBase_le_gammaWeight hd hγ
  have hDW' : (D:ℝ) ≤ W := by exact_mod_cast hDW
  have hB : 0 ≤ (B:ℝ) := Nat.cast_nonneg _
  have hW : 0 ≤ (W:ℝ) := Nat.cast_nonneg _
  have hmD := mul_nonneg hb (sub_nonneg.mpr hDW')
  have hmW := mul_nonneg hW (sub_nonneg.mpr hw)
  have hmS := mul_nonneg hW (sub_nonneg.mpr hs)
  have hmB := mul_nonneg hb hB
  nlinarith only [hmD,hmW,hmS,hmB]

/-- The count used to pay the case-(d) budget is extracted from the actual admissible datum. -/
theorem source_case_d_weight_reserve {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    (hd : 2 ≤ d) (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hs : Real.sqrt η ≤ gammaBase γ/8) :
    let B := (Finset.univ.filter (fun i => D.S.nor i = false)).card;
    let C := (Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 3)).card;
    -(gammaBase γ/4)*((B:ℝ)-(C:ℝ))+(3*gammaBase γ/2)*(C:ℝ)-
        (gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ) ≤
      -(gammaBase γ/8)*((B:ℝ)+(D.M₁:ℝ)) := by
  apply bad_weight_total_reserve hd hγ hs
  exact card_case_d_le_M₁ D hD

end WaveTurbulence.SumintPar
