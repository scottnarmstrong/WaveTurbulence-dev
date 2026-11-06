/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedCertificateChart
import Mathlib.Tactic

/-! # Exact contract phases evaluated from finite normalized certificates -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

/-- A paired x slot is distinct from the reference coordinate. -/
theorem xSlot_ne_reference {X : VineType} (A : Shape X) (j : Fin A.m) : A.xSlot j ≠ A.x0 := by
  intro h
  have he := congrArg Fin.val h
  change j.1+1=0 at he
  omega

/-- A paired y slot is distinct from the reference coordinate. -/
theorem ySlot_ne_reference {X : VineType} (A : Shape X) (j : Fin A.m) : A.ySlot j ≠ A.x0 := by
  intro h
  have he := congrArg Fin.val h
  change A.m+1+j.1=0 at he
  omega

/-- Every normal-core slot is distinct from the reference coordinate. -/
theorem uSlot_ne_reference {X : VineType} (A : Shape X) (hn : X.IsBad=false) (j : Fin 3) :
    A.uSlot hn j ≠ A.x0 := by
  intro h
  have he := congrArg Fin.val h
  change 2*A.m+1+j.1=0 at he
  omega

namespace NormalizedVineCertificate
variable {X : VineType} (C : NormalizedVineCertificate X)

/-- Exact boundary-corrected contract joint phase. -/
theorem joint_phase (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r C.shape.x0=
      2*inner ℝ r (x C.shape.x0) := by
  change energy (graphMolecule C.matrix.ends) univ ((C.chart g r).symm x).1 (C.atom C.shape.x0).1+
    (if C.shape.x0=C.shape.x0 then ‖g‖^2-‖g-r‖^2 else 0)=_
  rw [ite_eq_left rfl,C.lower,C.chart_energy]
  simpa only [add_sub_assoc] using C.matrix.affineChart_joint_phase C.joint C.shape.x0 C.reference_row g r x

/-- Exact negative bilinear s phase at every paired source atom. -/
theorem rung_s_phase (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) (j : Fin C.shape.m) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.ySlot j)=
      -2*inner ℝ (x (C.shape.xSlot j)) (x (C.shape.ySlot j)) := by
  rw [C.nodeResonance_matrix g r x _ (ySlot_ne_reference C.shape j),C.rung_s_matrix,
    quadraticEval_neg,quadraticEval_symmetric,freePhaseRow_eval,freePhaseRow_eval]
  ring

/-- Exact sum of the two paired phases, with their physical gap correction. -/
theorem rung_sum_phase (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) (j : Fin C.shape.m) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.xSlot j)+
      nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.ySlot j)=
        2*inner ℝ r ((C.ζ j 0 : ℝ) • x (C.shape.xSlot j)+
          (C.ζ j 1 : ℝ) • x (C.shape.ySlot j)+(C.ζ j 2 : ℝ) • r) := by
  rw [C.nodeResonance_matrix g r x _ (xSlot_ne_reference C.shape j),
    C.nodeResonance_matrix g r x _ (ySlot_ne_reference C.shape j),← quadraticEval_add,
    C.rung_sum_matrix,quadraticEval_symmetric,gapPhaseRow_eval,pairCorrectionRow_eval]
  simp only [← Int.cast_smul_eq_zsmul ℝ]

/-- Exact positive bilinear t phase, with the contract's ternary correction. -/
theorem rung_t_phase (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) (j : Fin C.shape.m) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.xSlot j)=
      2*inner ℝ (x (C.shape.xSlot j)) (x (C.shape.ySlot j))+
        2*inner ℝ r ((C.ζ j 0 : ℝ) • x (C.shape.xSlot j)+
          (C.ζ j 1 : ℝ) • x (C.shape.ySlot j)+(C.ζ j 2 : ℝ) • r) := by
  have hsum := C.rung_sum_phase d g r x j
  have hs := C.rung_s_phase d g r x j
  linarith only [hsum,hs]

/-- The first normal-core phase retains its actual common scalar sign. -/
theorem core_first_phase (hn : X.IsBad=false) (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.uSlot hn 0)=
      2*((C.coreFirstSign : ℤ) : ℝ)*inner ℝ (x (C.shape.uSlot hn 0)) (x (C.shape.uSlot hn 1)) := by
  rw [C.nodeResonance_matrix g r x _ (uSlot_ne_reference C.shape hn 0),C.core_first_matrix,
    quadraticEval_signed_symmetric,freePhaseRow_eval,freePhaseRow_eval]

/-- The second normal-core phase is the exact owner-approved signed linear
or nonlinear alternative (F79), with the same common sign. -/
theorem core_second_phase (hn : X.IsBad=false) (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) :
    nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.uSlot hn 1)=
      2*((C.coreFirstSign : ℤ) : ℝ)*(if C.coreLinear then
        inner ℝ (x (C.shape.uSlot hn 0)) (x (C.shape.uSlot hn 2)) else
        ((C.coreSign : ℤ) : ℝ)*inner ℝ (x (C.shape.uSlot hn 2))
          (x (C.shape.uSlot hn 0)+x (C.shape.uSlot hn 1)-x (C.shape.uSlot hn 2))) := by
  rw [C.nodeResonance_matrix g r x _ (uSlot_ne_reference C.shape hn 1),C.core_second_matrix,
    quadraticEval_signed_symmetric,freePhaseRow_eval,coreSecondArgumentRow_eval]
  cases C.coreLinear
  · simp only [Bool.false_eq_true,ite_false,Int.cast_mul]
    ring
  · simp only [ite_true,Int.cast_mul,Int.cast_one]
    rw [real_inner_comm (x (C.shape.uSlot hn 2)) (x (C.shape.uSlot hn 0))]
    ring

/-- The three normal-core phases sum to the exact ternary root-gap form. -/
theorem core_sum_phase (hn : X.IsBad=false) (d : ℕ) (g r : Mom d) (x : Fin C.shape.n → Mom d) :
    (∑ c : Fin 3,nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.uSlot hn c))=
      2*inner ℝ r ((C.ξ 0 : ℝ) • x (C.shape.uSlot hn 0)+(C.ξ 1 : ℝ) • x (C.shape.uSlot hn 1)+
        (C.ξ 2 : ℝ) • x (C.shape.uSlot hn 2)+(C.ξ 3 : ℝ) • r) := by
  have he : (∑ c : Fin 3,nodeResonance C.indexing ((C.chart g r).symm x).1 g r (C.shape.uSlot hn c))=
      ∑ c : Fin 3,quadraticEval (C.matrix.phaseMatrix (C.atom (C.shape.uSlot hn c)).1) (attachGap x r) := by
    apply sum_congr rfl
    intro c _
    exact C.nodeResonance_matrix g r x _ (uSlot_ne_reference C.shape hn c)
  rw [he,← quadraticEval_sum,C.core_sum_matrix,quadraticEval_symmetric,gapPhaseRow_eval,coreCorrectionRow_eval]
  simp only [← Int.cast_smul_eq_zsmul ℝ]

end NormalizedVineCertificate
end WaveTurbulence.Vine.Param
