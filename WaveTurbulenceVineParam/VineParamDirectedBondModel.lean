/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulenceVineParam.VineParamDirectedTransport
import Mathlib.Tactic

/-! # Exact finite directed models of actual internal vine bonds -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V D A β : Type*} [DecidableEq V] [Fintype D] [DecidableEq A] [Fintype β]

/-- A directed endpoint graph realized by every actual internal bond and
atom, with orientation preserved. The data depend only on the molecule. -/
structure DirectedBondModel (M : Molecule V D) (S : Finset V) (A β : Type*)
    [DecidableEq A] [Fintype β] where
  ends : β → A×A
  atom : A ≃ ↥S
  edge : β ≃ Bond M S
  tail : ∀ e,M.atom (edge e).1=(atom (ends e).1).1
  head : ∀ e,M.atom (M.mate (edge e).1)=(atom (ends e).2).1

namespace DirectedBondModel
variable {M : Molecule V D} {S : Finset V} (Q : DirectedBondModel M S A β)

/-- The actual atom realization is injective on its value carrier. -/
theorem atom_val_eq_iff (u v : A) : (Q.atom u).1=(Q.atom v).1 ↔ u=v := by
  constructor
  · intro h
    exact Q.atom.injective (Subtype.ext h)
  · rintro rfl
    rfl

/-- Actual outgoing-minus-incoming incidence is exactly the directed model row. -/
theorem incidence_eq (v : A) (e : β) :
    incidence M (Q.atom v).1 (Q.edge e).1= -energySign Q.ends v e := by
  simp only [incidence,Q.tail,Q.head,Q.atom_val_eq_iff,energySign,neg_sub]

/-- The entire actual internal source flow is transported without dropping
any bond occurrence, including loops or parallel edges. -/
theorem flow_eq {E : Type*} [AddCommGroup E] (k : Bond M S → E) (v : A) :
    flow M S k (Q.atom v).1=directedFlow Q.ends v (fun e => k (Q.edge e)) := by
  have h := Equiv.sum_comp Q.edge (fun e => incidence M (Q.atom v).1 e.1 • k e)
  simpa only [flow,directedFlow,Q.incidence_eq] using h.symm

/-- Every actual molecular internal energy row is transported exactly. -/
theorem energy_eq {d : ℕ} (k : Bond M S → Mom d) (v : A) :
    energy M S k (Q.atom v).1=directedEnergy Q.ends v (fun e => k (Q.edge e)) := by
  have h := Equiv.sum_comp Q.edge (fun e => -(incidence M (Q.atom v).1 e.1 : ℝ)*‖k e‖^2)
  simpa only [energy,directedEnergy,Q.incidence_eq,Int.cast_neg,neg_neg] using h.symm

end DirectedBondModel
end WaveTurbulence.Vine.Param
