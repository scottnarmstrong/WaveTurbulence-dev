/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LatticeEnvelopeSize
/-! Explicit fixed-data thresholds make every logarithmic stage size large simultaneously. -/
@[expose] public section
namespace WaveTurbulence.Induct

theorem lambda_le_zero (P : WTParams) (hd : 1 ≤ P.d) (p : ℕ) : P.Lambda p ≤ P.Lambda 0 := by
  unfold WTParams.Lambda
  simp only [Nat.sub_zero]
  exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)

noncomputable def stageSizeThreshold (P : WTParams) (C K : ℝ) : ℝ :=
  max 2 (max C (max (baseLatticeSum P.d)
    (Real.exp (max 2 (max K (P.Lambda 0 : ℝ))))))

theorem stage_sizes_of_threshold (P : WTParams) (hd : 1 ≤ P.d) (C K : ℝ)
    (hL : stageSizeThreshold P C K ≤ P.L) :
    Real.exp 2 ≤ P.L ∧ C ≤ P.L ∧ baseLatticeSum P.d ≤ P.L ∧
      ∀ p : ℕ, K ≤ (P.R p : ℝ) ∧ K ≤ (P.N p : ℝ) ∧
        (P.Lambda p : ℝ) / 4 ≤ P.N p := by
  have heL : Real.exp (max 2 (max K (P.Lambda 0 : ℝ))) ≤ P.L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLexp : Real.exp 2 ≤ P.L :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans heL
  have hL0 : 0 < P.L := (Real.exp_pos 2).trans_le hLexp
  have hlog : max 2 (max K (P.Lambda 0 : ℝ)) ≤ Real.log P.L := (Real.le_log_iff_exp_le hL0).mpr heL
  have hC : C ≤ P.L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hbase : baseLatticeSum P.d ≤ P.L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  refine ⟨hLexp, hC, hbase, fun p => ?_⟩
  have hr : Real.log P.L ≤ (P.R p : ℝ) := log_le_Rdown P hd hLexp (P.D - p)
  have hn := log_le_N P hd hLexp p
  have hKlog : K ≤ Real.log P.L := (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have hΛlog : (P.Lambda 0 : ℝ) ≤ Real.log P.L := (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  have hΛ : (P.Lambda p : ℝ) ≤ P.Lambda 0 := by exact_mod_cast lambda_le_zero P hd p
  have hΛ0 : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
  exact ⟨hKlog.trans hr, hKlog.trans hn, by linarith⟩

end WaveTurbulence.Induct
