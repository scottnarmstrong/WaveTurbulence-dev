/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulenceVineParam.VineParamDirectedTransport
import Mathlib.Tactic

/-! # A finite directed endpoint model as an actual half-edge molecule

Every edge has two actual darts. This connects the source graph insertion
calculus to the exact FullVineChart interface, retaining loops and parallel
occurrences without any orientation choice depending on a decoration.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β]

/-- The actual half-edge molecule of a finite directed endpoint model. -/
@[expose] def graphMolecule (ends : β → V×V) : Molecule V (β×Bool) where
  atoms := univ
  atom := fun d => if d.2 then (ends d.1).1 else (ends d.1).2
  mate := fun d => (d.1,!d.2)
  out := Prod.snd
  atom_mem := fun _ => mem_univ _
  mate_mate := by intro d; cases d with | mk e b => cases b <;> rfl
  mate_ne := by
    rintro ⟨e,b⟩ h
    cases b <;> cases congrArg Prod.snd h
  out_mate := fun _ => rfl

/-- One actual outgoing internal bond is exactly one original edge occurrence. -/
@[expose] noncomputable def graphBondEquiv (ends : β → V×V) :
    β ≃ Bond (graphMolecule ends) univ := by
  classical
  refine {
    toFun := fun e => ⟨(e,true),?_⟩
    invFun := fun e => e.1.1
    left_inv := fun _ => rfl
    right_inv := ?_ }
  · change (e,true) ∈ ((graphMolecule ends).bonds.filter ((graphMolecule ends).InGroup univ))
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,mem_univ _,mem_univ _⟩
  · intro e
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp := e.2
      change e.1 ∈ ((graphMolecule ends).bonds.filter ((graphMolecule ends).InGroup univ)) at hp
      have hout := (mem_filter.mp (mem_filter.mp hp).1).2
      exact hout.symm

/-- Graph and source incidence signs agree on the actual outgoing representative. -/
theorem graph_incidence (ends : β → V×V) (v : V) (e : β) :
    incidence (graphMolecule ends) v (graphBondEquiv ends e).1= -energySign ends v e := by
  change ((if (ends e).1=v then (1 : ℤ) else 0)-(if (ends e).2=v then 1 else 0))=
    -((if (ends e).2=v then 1 else 0)-(if (ends e).1=v then 1 else 0))
  ring

/-- Generic graph momentum and exact contract flow are the same function. -/
theorem graph_flow {E : Type*} [AddCommGroup E] (ends : β → V×V)
    (k : Bond (graphMolecule ends) univ → E) (v : V) :
    flow (graphMolecule ends) univ k v=directedFlow ends v (fun e => k (graphBondEquiv ends e)) := by
  have hs := Equiv.sum_comp (graphBondEquiv ends)
    (fun e => incidence (graphMolecule ends) v e.1 • k e)
  simpa only [flow,directedFlow,graph_incidence] using hs.symm

/-- Exact graph negative Gamma and the contract energy are the same function. -/
theorem graph_energy {d : ℕ} (ends : β → V×V)
    (k : Bond (graphMolecule ends) univ → Mom d) (v : V) :
    energy (graphMolecule ends) univ k v=directedEnergy ends v (fun e => k (graphBondEquiv ends e)) := by
  have hs := Equiv.sum_comp (graphBondEquiv ends)
    (fun e => -(incidence (graphMolecule ends) v e.1 : ℝ)*‖k e‖^2)
  simpa only [energy,directedEnergy,graph_incidence,Int.cast_neg,neg_neg] using hs.symm

end WaveTurbulence.Vine.Param
