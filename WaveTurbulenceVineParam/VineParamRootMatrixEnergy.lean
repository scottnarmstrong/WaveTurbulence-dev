/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootMatrixDecoder
public import WaveTurbulenceVineParam.VineParamDirectedJointRow
import WaveTurbulenceVineParam.VineParamSpliceEnergyLaw
import Mathlib.Tactic

/-! # Actual normalized source resonances from integer phase certificates -/

public section
namespace WaveTurbulence.Vine.Param.RootIntegerMatrix
open Finset
variable {q : ℕ} (C : RootIntegerMatrix q)

/-- The exact reduced decoder on free coordinates followed by the root gap. -/
@[expose] def reducedInverse : Matrix (Fin (2*q)) (Fin (q+1)) ℤ :=
  reducedDecoder C.gap_lt C.inverse

/-- The exact integer coefficient matrix of one actual source resonance. -/
@[expose] def phaseMatrix (v : Fin (q+1)) : Matrix (Fin (q+1)) (Fin (q+1)) ℤ :=
  energyMatrix C.ends v C.reducedInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform anchor translation changes negative Gamma by the actual source
flow only. No resonance hypothesis is used. -/
theorem energy_add_anchor (k : Fin (2*q) → E) (g : E) (v : Fin (q+1)) :
    directedEnergy C.ends v (fun e => k e+g)=directedEnergy C.ends v k-
      2*inner ℝ (directedFlow C.ends v k) g := by
  have h := directedEnergy_sub_of_balanced C.ends v (fun e => k e+g) g (C.balanced v)
  simp only [add_sub_cancel_right,directedFlow_translate,C.balanced,zero_zsmul,add_zero] at h
  linarith only [h]

/-- The reduced coefficient matrix evaluates to the entire zero-anchor
source resonance on arbitrary vector-valued momenta. -/
theorem phaseMatrix_eval (r : E) (x : Fin q → E) (v : Fin (q+1)) :
    directedEnergy C.ends v (intEval C.inverse (packCoordinates C.gap_lt x r))=
      quadraticEval (C.phaseMatrix v) (attachGap x r) := by
  rw [intEval_pack C.gap_lt C.inverse x r]
  exact (energyMatrix_eval C.ends v C.reducedInverse (attachGap x r)).symm

/-- Exact source energy, with its only possible anchor correction explicit. -/
theorem affineChart_energy_eq (g r : E) (x : Fin q → E) (v : Fin (q+1)) :
    directedEnergy C.ends v ((C.affineChart g r).symm x).1=
      quadraticEval (C.phaseMatrix v) (attachGap x r)-
        2*inner ℝ (rootForcing C.a C.b r v) g := by
  have hk : ((C.affineChart g r).symm x).1=
      fun e => intEval C.inverse (packCoordinates C.gap_lt x r) e+g := by
    funext e
    rw [C.affineChart_decode]
    exact add_comm _ _
  have hf : directedFlow C.ends v (intEval C.inverse (packCoordinates C.gap_lt x r))=
      rootForcing C.a C.b r v := (C.decodeRoot r x).2 v
  rw [hk,C.energy_add_anchor,hf,C.phaseMatrix_eval]

/-- Every interior phase is independent of the uniform anchor. -/
theorem affineChart_energy_interior (g r : E) (x : Fin q → E) (v : Fin (q+1))
    (ha : v ≠ C.a) (hb : v ≠ C.b) :
    directedEnergy C.ends v ((C.affineChart g r).symm x).1=
      quadraticEval (C.phaseMatrix v) (attachGap x r) := by
  rw [C.affineChart_energy_eq]
  simp only [rootForcing,ha,hb,ite_false,inner_zero_left,mul_zero,sub_zero]

/-- The actual boundary-corrected joint phase follows from the physical
source joint row and its checked outgoing-reference encoder row. -/
theorem affineChart_joint_phase (Q : DirectedJointRow C.ends C.b) (ref : Fin q)
    (hrow : ∀ e,C.forward (C.freeIndex ref) e= -(if e=Q.outgoing then 1 else 0))
    (g r : E) (x : Fin q → E) :
    directedEnergy C.ends C.b ((C.affineChart g r).symm x).1+
      ‖g‖^2-‖g-r‖^2=2*inner ℝ r (x ref) := by
  let k := (C.affineChart g r).symm x
  have hf : directedFlow C.ends C.b k.1=r := by
    simpa only [rootForcing,C.distinct.symm,ite_false,ite_true] using k.2 C.b
  have h := Q.boundary_phase g r k.1 hf
  have hr := C.affineChart_reference_of_row ref Q.outgoing hrow g r k
  rw [Equiv.apply_symm_apply] at hr
  rw [← hr] at h
  exact h

end WaveTurbulence.Vine.Param.RootIntegerMatrix
