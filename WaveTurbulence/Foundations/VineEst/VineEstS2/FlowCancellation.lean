/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondDarts
public import Mathlib.Algebra.Module.BigOperators

/-! # Cancellation of internal flow, with loops and multiplicities -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Every actual internal bond has one positive and one negative endpoint
incidence in S. Self-loops cancel at the same vertex. -/
theorem sum_incidence_internal (M : Molecule V D) (S : Finset V) (e : Bond M S) :
    (∑ v ∈ S, incidence M v e.1) = 0 := by
  classical
  have he := internalBond_inGroup M S e
  simp only [Molecule.InGroup] at he
  simp [incidence,Finset.sum_sub_distrib,eq_comm,he.1,he.2]

/-- A purely algebraic identity of the exact M9 flow, with no conservation
or zero-gap premise. -/
theorem sum_flow_zero {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) : (∑ v ∈ S, flow M S k v) = 0 := by
  classical
  unfold flow
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.sum_smul,sum_incidence_internal,zero_smul]

end WaveTurbulence.VineEstS2
