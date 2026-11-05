/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBoundaryGaps
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Opposite orientations at two-bond cuts of balanced groups -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Signed constant flow is outgoing degree minus incoming degree. -/
theorem signed_degree (M : Molecule V D) (v : V) :
    (∑ x ∈ M.dartsAt v,M.dartSign x • (1 : ℝ))=
      (M.outdeg v : ℝ)-(M.indeg v : ℝ) := by
  simp only [Molecule.dartSign,smul_eq_mul,mul_one]
  rw [Finset.sum_ite]
  simp only [sum_const,nsmul_eq_mul,mul_one,mul_neg,sub_eq_add_neg,
    Molecule.outdeg,Molecule.indeg,Bool.not_eq_true]

/-- A two-bond cut of any balanced directed group has opposite directions.
Balance is local degree data and does not depend on a decoration. -/
theorem balanced_two_boundary_opposite (M : Molecule V D)
    (hbal : ∀ v ∈ M.atoms,M.outdeg v=M.indeg v) (A : Finset V) (hA : A ⊆ M.atoms)
    (x y : D) (hxy : x ≠ y) (hcut : boundary M A={x,y}) : M.out x ≠ M.out y := by
  have hc : ∀ v ∈ A,∑ z ∈ M.dartsAt v,M.dartSign z • (1 : ℝ)=0 := by
    intro v hv
    rw [signed_degree,hbal v (hA hv),sub_self]
  have hz := boundary_eq_zero M A (fun _ => (1 : ℝ)) (fun _ => rfl) hc
  rw [hcut,sum_pair hxy] at hz
  intro he
  unfold Molecule.dartSign at hz
  cases hx : M.out x <;> have hy := hx.symm.trans he <;>
    simp only [hx,hy.symm,Bool.false_eq_true,ite_false,ite_true,
      neg_smul,one_smul] at hz <;> norm_num at hz

end WaveTurbulence.Vine
