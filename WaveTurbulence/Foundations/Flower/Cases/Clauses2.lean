/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Clauses
/-! # The cut1 and cut2 clauses at a fixed parameter set. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem mul4_le {A B B' D M : ℝ} (hA : 0 ≤ A) (hB : B ≤ B') (hD : 0 ≤ D) (hM : 0 ≤ M) :
    A * B * D * M ≤ A * B' * D * M :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hA) hD) hM

theorem cut1_clause_of_filt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAt C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCaseAt CaseCut1 Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc _
  obtain ⟨hs1, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := Option.isSome_iff_exists.mp hs1
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := filt_cut1 C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j
    (fun _ => none) (fun h => absurd h (by simp))
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j) none ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun _ => none) k * LG.cutWeight1P p P.L j k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp [stemFilter_none]
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim, mul_one]
  rw [Sw_eq] at hb
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hb
  unfold flowerRootBudget at hroot
  refine hb.trans ?_
  exact mul4_le hroot (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [(Nat.cast_nonneg Pm : (0 : ℝ) ≤ Pm)]))
    (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (by positivity) _)

theorem cut2zero_clause_of_filt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAt C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCaseAt CaseCut2Zero Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  subst hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut 0 rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := filt_cut1 C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j₁
    (fun _ => some 0) (fun _ => hj₁)
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j₁) (some 0) ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun _ => some 0) k * LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp only [Option.elim, cutWeight2P_zero]
      ring
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim]
  rw [Sw_eq] at hb
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hb
  unfold flowerRootBudget at hroot
  have hPm : (0 : ℝ) ≤ Pm := Nat.cast_nonneg Pm
  have hD : 0 ≤ P.δ ^ (2 * P.ν * N) := Real.rpow_nonneg hδ.le _
  have hM : 0 ≤ ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) := Real.rpow_nonneg (by positivity) _
  by_cases hpl : ∀ j, pat j = .plain
  · simp only [if_pos hpl] at hb ⊢
    have hB : P.L ^ ((1 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm - Pm) ≤
        P.L ^ ((1 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm) * ((2 : ℝ) ^ 0 * P.L) ^ (-(Pm / 9 : ℝ)) := by
      simp only [pow_zero, one_mul]
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < P.L)]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact hb.trans ((mul4_le hroot hB hD hM).trans (le_of_eq (by ring)))
  · simp only [if_neg hpl, mul_one] at hb ⊢
    have hB : P.L ^ ((2 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm - Pm) ≤
        P.L ^ ((2 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact hb.trans (mul4_le hroot hB hD hM)

end WaveTurbulence.Flower.Cases
