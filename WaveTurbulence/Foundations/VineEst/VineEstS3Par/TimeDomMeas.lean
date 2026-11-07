/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot
public import WaveTurbulence.Foundations.SumintPar.Data

/-! # The `sumint` time domain is measurable and has volume at most one -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem measurableSet_timeDom (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (t t' t'' : ℝ) :
    MeasurableSet (D.timeDom hI t t' t'') := by
  unfold SumintPar.SumintDatum.timeDom
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · refine MeasurableSet.iInter fun v => ?_
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const (measurable_pi_apply v)
    · exact measurableSet_le (measurable_pi_apply v) measurable_const
    · exact measurableSet_lt (measurable_pi_apply v) measurable_const
  · exact measurableSet_lt measurable_const (measurable_pi_apply _)
  · refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

theorem volume_timeDom_le (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (t t' t'' : ℝ) :
    volume (D.timeDom hI t t' t'') ≤ 1 := by
  have hsub : D.timeDom hI t t' t'' ⊆ Set.pi univ (fun v => Icc (D.q v : ℝ) (D.q v + 1)) := by
    intro τ hτ v _
    exact ⟨(hτ.1 v).1, (hτ.1 v).2.1⟩
  refine (measure_mono hsub).trans ?_
  rw [Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp

end WaveTurbulence.VineEstS3Par.Eng
