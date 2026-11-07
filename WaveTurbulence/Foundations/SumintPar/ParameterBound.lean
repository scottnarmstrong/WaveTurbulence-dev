/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ShapeFacts
public import WaveTurbulence.Foundations.SumintPar.WeightBounds
public import WaveTurbulence.Foundations.SumintPar.PairKernels
import Mathlib.Tactic

/-!
# The total time modulation is controlled by the drafted maximum

Simultaneous translation sums every time parameter exactly once.
There are `M` of these parameters. The harmless factor `M+1` will be
absorbed into an exponential constant in `M` after interpolation.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The maximum parameter bracket in the exact drafted conclusion. -/
@[expose] noncomputable def parameterMaximum {d : ℕ} (D : SumintDatum d) : ℝ :=
  ⨆ v, jbr (d := 1) (WithLp.toLp 2 (fun _ : Fin 1 => D.param v))

/-- Each parameter is dominated by its one-dimensional Japanese bracket. -/
theorem abs_le_parameter_bracket (a : ℝ) :
    |a| ≤ jbr (d := 1) (WithLp.toLp 2 (fun _ : Fin 1 => a)) := by
  have hcoord : |a| ≤ ‖WithLp.toLp 2 (fun _ : Fin 1 => a)‖ := by
    simpa only [PiLp.toLp_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (WithLp.toLp 2 (fun _ : Fin 1 => a)) 0
  have hn : ‖WithLp.toLp 2 (fun _ : Fin 1 => a)‖ ≤
      jbr (d := 1) (WithLp.toLp 2 (fun _ : Fin 1 => a)) := by
    unfold jbr
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    linarith
  exact hcoord.trans hn

/-- The finite source maximum dominates every parameter in absolute value. -/
theorem abs_parameter_le_maximum {d : ℕ} (D : SumintDatum d) (v : D.S.TVar) :
    |D.param v| ≤ parameterMaximum D := by
  unfold parameterMaximum
  apply (abs_le_parameter_bracket _).trans
  have hb : BddAbove (Set.range (fun u : D.S.TVar =>
      jbr (d := 1) (WithLp.toLp 2 (fun _ : Fin 1 => D.param u)))) := Finite.bddAbove_range _
  exact le_ciSup hb v

/-- At least one block supplies a parameter, so its bracket maximum is at least one. -/
theorem one_le_parameterMaximum {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    1 ≤ parameterMaximum D := by
  let v : D.S.TVar := .inl ⟨⟨0, hI⟩, 0⟩
  unfold parameterMaximum
  apply (one_le_jbr (WithLp.toLp 2 (fun _ : Fin 1 => D.param v))).trans
  have hb : BddAbove (Set.range (fun u : D.S.TVar =>
      jbr (d := 1) (WithLp.toLp 2 (fun _ : Fin 1 => D.param u)))) := Finite.bddAbove_range _
  exact le_ciSup hb v

/-- The total modulation has only a factor `M+1` beyond the exact drafted maximum. -/
theorem scalarBracket_sum_parameters_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I) :
    scalarBracket (∑ v, D.param v) ≤ ((D.S.M : ℝ)+1) * parameterMaximum D := by
  have hsum : |∑ v, D.param v| ≤ (D.S.M : ℝ) * parameterMaximum D := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _v : D.S.TVar, parameterMaximum D :=
        Finset.sum_le_sum (fun v _ => abs_parameter_le_maximum D v)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, card_time_index,
        nsmul_eq_mul]
  have hb : scalarBracket (∑ v, D.param v) ≤ 1 + |∑ v, D.param v| := by
    unfold scalarBracket
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [abs_nonneg (∑ v, D.param v), sq_abs (∑ v, D.param v)]
  have hm := one_le_parameterMaximum D hI
  nlinarith only [hsum, hb, hm]

end WaveTurbulence.SumintPar
