/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBondMatching
public import WaveTurbulence.Foundations.Molecule.VineIncidenceMultiset
import Mathlib.Tactic

/-! # Actual signed dart sums in directed bond coordinates

This bridge retains every parallel occurrence and both incidences of a loop.
Its weight can be a momentum or a squared norm, so the same combinatorial
identity transports conservation and molecular resonance.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D A : Type*} [DecidableEq V] [Fintype D] [AddCommGroup A]

/-- The outgoing-minus-incoming weighted sum of internal darts at an atom. -/
@[expose] def internalSignedSum (M : Molecule V D) (S : Finset V) (v : V) (f : D → A) : A :=
  ∑ d ∈ (M.dartsAt v).filter (M.InGroup S),if M.out d=true then f d else -f d

/-- Each actual outgoing bond contributes at its tail and negatively at its
head, using the actual mate to locate the second endpoint. -/
theorem internalSignedSum_eq_bonds (M : Molecule V D) (S : Finset V) (v : V)
    (f : D → A) (hf : ∀ d,f (M.mate d)=f d) :
    internalSignedSum M S v f=
      ∑ d ∈ internalBonds M S,
        ((if M.atom d=v then f d else 0)-(if M.atom (M.mate d)=v then f d else 0)) := by
  have h := sum_internal_darts M S
    (fun d => if M.atom d=v then (if M.out d=true then f d else -f d) else 0)
  have hl : internalSignedSum M S v f=
      ∑ d ∈ univ.filter (M.InGroup S),
        if M.atom d=v then (if M.out d=true then f d else -f d) else 0 := by
    simp only [internalSignedSum,Molecule.dartsAt,sum_filter]
    apply sum_congr rfl
    intro d _hd
    by_cases ha : M.atom d=v <;> by_cases hg : M.InGroup S d <;>
      simp only [ha,hg,ite_true,ite_false]
  rw [hl,h]
  apply sum_congr rfl
  intro d hd
  have hout := (mem_filter.mp hd).2.1
  simp only [M.out_mate,hout,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,hf,sub_eq_add_neg]
  by_cases ha : M.atom (M.mate d)=v <;> simp only [ha,ite_true,ite_false,neg_zero]

/-- Reindexing by an actual bond bijection preserves the signed sum exactly. -/
theorem internalSignedSum_eq_enumeration (M : Molecule V D) (S : Finset V) (v : V)
    {m : ℕ} (e : Fin m ≃ internalBonds M S) (f : D → A)
    (hf : ∀ d,f (M.mate d)=f d) :
    internalSignedSum M S v f=∑ i : Fin m,
      ((if M.atom (e i).1=v then f (e i).1 else 0)-
        (if M.atom (M.mate (e i).1)=v then f (e i).1 else 0)) := by
  rw [internalSignedSum_eq_bonds M S v f hf]
  let g : D → A := fun d =>
    (if M.atom d=v then f d else 0)-(if M.atom (M.mate d)=v then f d else 0)
  have he := congrArg Multiset.sum (univ_subtype_map (internalBonds M S) g)
  have hs : (∑ d ∈ internalBonds M S,g d)=∑ d : internalBonds M S,g d.1 := he.symm
  rw [hs]
  exact (Equiv.sum_comp e (fun d : internalBonds M S => g d.1)).symm

end WaveTurbulence.Vine.Param
