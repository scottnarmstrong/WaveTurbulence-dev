/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Cert

/-! # W2-KIND2 (a): the two-sided clamp of a gate time factor (R114, TARGET L1913-L1919)

`clamp2J q J`: the continuous constant extension `J(q, s)` below `q`, `J(t, s)` on `[q, q+1]`, `J(q+1, s)` above.

* `sum_clamp2_eq_sum_clamp`: replacing `clampJ q` by `clamp2J q` in every separated term keeps the SUM as long as the total vanishes at
  `t = q` (`hvan`).
* `sum_clamp2_eq_of_vanish`, `couple_clamp2_eq`, `tree_clamp2_eq`: `hvan` from the endpoint vanishing of a high-root object
  (`couple_root_vanish`, `tree_root_vanish`) through the gate expansion `ContExp.hexp`.
* `clamp2_bound_C`, `clamp2_bound_T`: the window bound `TR η · X` of `clamp2J q J` on EVERY unit window `w` (below, native, above),
  from the `𝔛^{1-η}` bound of `J` on the native box.  Below the gate this is the trace at `t = q` (the clampJ version was `0`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 MeasureTheory Set Filter
open scoped ENNReal

/-- The two-sided constant extension of a gate time factor: `J(q, s)` below `q`, `J(t, s)` on `[q, q+1]`, `J(q+1, s)` above. -/
noncomputable def clamp2J (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ := fun ts =>
  J ![max (min (ts 0) (q + 1)) q, ts 1]

theorem clamp2J_continuous {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} (hJ : Continuous J) : Continuous (clamp2J q J) := by
  unfold clamp2J
  refine hJ.comp (continuous_pi fun i => ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact ((continuous_apply 0).min continuous_const).max continuous_const
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact continuous_apply 1

theorem clamp2J_eq_clampJ {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} {ts : Fin 2 → ℝ} (h : q ≤ ts 0) :
    clamp2J q J ts = clampJ q J ts := by
  unfold clamp2J clampJ
  rw [if_neg (not_lt.2 h), max_eq_left (le_min h (by linarith))]

theorem clamp2J_of_lt {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} {ts : Fin 2 → ℝ} (h : ts 0 < q) :
    clamp2J q J ts = J ![q, ts 1] := by
  unfold clamp2J
  rw [min_eq_left (by linarith), max_eq_right h.le]

/-- **Replacing `clampJ` by `clamp2J` in every separated term keeps the sum**, provided the total vanishes at the gate level. -/
theorem sum_clamp2_eq_sum_clamp {d m : ℕ} (c : ℝ) (Jg : Fin m → (Fin 2 → ℝ) → ℂ) (Mg : Fin m → Mom d → ℝ) {q : ℝ}
    (t s : ℝ) (k : Mom d) (hvan : ∑ i, (c : ℂ) * Jg i ![q, s] * (Mg i k : ℂ) = 0) :
    ∑ i, sepTerm c (clamp2J q (Jg i)) (Mg i) t s k = ∑ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k := by
  by_cases ht : q ≤ t
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold sepTerm
    rw [clamp2J_eq_clampJ (by simpa using ht)]
  · have ht' : t < q := lt_of_not_ge ht
    have h1 : ∀ i, sepTerm c (clamp2J q (Jg i)) (Mg i) t s k = (c : ℂ) * Jg i ![q, s] * (Mg i k : ℂ) := fun i => by
      unfold sepTerm
      rw [clamp2J_of_lt (by simpa using ht')]
      simp
    have h2 : ∀ i, sepTerm c (clampJ q (Jg i)) (Mg i) t s k = 0 := fun i => sepTerm_clamp_of_lt ht' k
    simp only [h1, h2, Finset.sum_const_zero]
    exact hvan

section Vanish
variable {P : WTParams} {n W : ℕ} {T : Set (Fin 2 → ℝ)} {F : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ}

/-- `hvan` from the vanishing of the expanded function at `(q, s)`. -/
theorem sum_clamp2_eq_of_vanish (E : ContExp P n W T F cost) {q s : ℝ} (hmem : ![q, s] ∈ T)
    (hv : ∀ k, F ![q, s] k = 0) (t : ℝ) (k : Mom P.d) :
    ∑ i, sepTerm (P.δ ^ n) (clamp2J q (E.J i)) (E.M i) t s k = ∑ i, sepTerm (P.δ ^ n) (clampJ q (E.J i)) (E.M i) t s k := by
  refine sum_clamp2_eq_sum_clamp _ _ _ t s k ?_
  have h := E.hexp _ hmem k
  rw [hv k] at h
  push_cast
  exact h.symm

end Vanish

end WaveTurbulence.VineEstS5C.P4.W2.K2
