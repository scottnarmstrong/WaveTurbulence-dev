/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulenceVineParam.VineParamActualFlow
import Mathlib.Tactic

/-! # Exact V4 contract bond, flow and energy conventions

The contract uses the same actual outgoing darts, with a differently written
finite filter. This bridge preserves the underlying dart and both endpoints.
The source connected-block adapter is a separate final-context concern.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The contract and the source-directed model use exactly the same bonds. -/
@[expose] noncomputable def contractBondEquiv (M : Molecule V D) (S : Finset V) :
    Bond M S ≃ internalBonds M S := by
  classical
  refine ⟨fun e => ⟨e.1,?_⟩,fun e => ⟨e.1,?_⟩,?_,?_⟩
  · simpa only [internalBondSet,Molecule.bonds,internalBonds,mem_filter,mem_univ,true_and] using e.2
  · simpa only [internalBondSet,Molecule.bonds,internalBonds,mem_filter,mem_univ,true_and] using e.2
  · intro e; rfl
  · intro e; rfl

/-- Compose the actual literal occurrence matching with the exact contract bond set. -/
@[expose] noncomputable def contractEnumeration (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) : Fin m ≃ Bond M S := e.trans (contractBondEquiv M S).symm

/-- Contract incidence is the same source directed-flow sign. -/
theorem contract_incidence (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (v : V) (j : Fin m) :
    incidence M v (contractEnumeration M S e j).1= -energySign (actualEnds M S e) v j := by
  simp only [incidence,energySign,actualEnds,contractEnumeration,Equiv.trans_apply,
    contractBondEquiv,Equiv.coe_fn_symm_mk,neg_sub]
  rfl

/-- The exact contract flow is the same incidence row on literal bond labels. -/
theorem contract_flow {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (k : Bond M S → E) (v : V) :
    flow M S k v=directedFlow (actualEnds M S e) v (fun j => k (contractEnumeration M S e j)) := by
  have hs := Equiv.sum_comp (contractEnumeration M S e) (fun b : Bond M S => incidence M v b.1 • k b)
  simpa only [flow,directedFlow,contract_incidence] using hs.symm

/-- The exact contract energy is the same negative molecular Gamma row. -/
theorem contract_energy {d : ℕ} (M : Molecule V D) (S : Finset V) {m : ℕ}
    (e : Fin m ≃ internalBonds M S) (k : Bond M S → Mom d) (v : V) :
    energy M S k v=directedEnergy (actualEnds M S e) v (fun j => k (contractEnumeration M S e j)) := by
  have hs := Equiv.sum_comp (contractEnumeration M S e)
    (fun b : Bond M S => -(incidence M v b.1 : ℝ)*‖k b‖^2)
  simpa only [energy,directedEnergy,contract_incidence,Int.cast_neg,neg_neg] using hs.symm

end WaveTurbulence.Vine.Param
