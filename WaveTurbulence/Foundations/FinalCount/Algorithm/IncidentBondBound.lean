/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
public import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! # Uniform size of the actual outgoing bonds touching a finite atom set -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem incident_bonds_card_le_sum_degrees (M : Molecule V D) (S : Finset V) :
    (appbRemovedBonds M S).card ≤ ∑ v ∈ S,M.deg v := by
  classical
  have he : appbRemovedBonds M S = S.biUnion (Degen.incidentBondsAt M) := by
    ext x
    simp only [appbRemovedBonds,Degen.incidentBondsAt,Degen.bondsOutAt,Degen.bondsInto,
      mem_filter,mem_union,mem_biUnion]
    constructor
    · rintro ⟨hx,ha | hb⟩
      · exact ⟨M.atom x,ha,Or.inl ⟨hx,rfl⟩⟩
      · exact ⟨M.atom (M.mate x),hb,Or.inr ⟨hx,rfl⟩⟩
    · rintro ⟨v,hv,(⟨hx,ha⟩ | ⟨hx,hb⟩)⟩
      · exact ⟨hx,Or.inl (ha.symm ▸ hv)⟩
      · exact ⟨hx,Or.inr (hb.symm ▸ hv)⟩
  rw [he]
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro v hv
  have hh := Degen.card_incident_add_self_eq_deg M v
  omega

theorem incident_bonds_card_le_four_atoms (M : Molecule V D) (hM : M.IsMolecule)
    (S : Finset V) (hS : S ⊆ M.atoms) : (appbRemovedBonds M S).card ≤ 4*S.card := by
  calc
    _ ≤ ∑ v ∈ S,M.deg v := incident_bonds_card_le_sum_degrees M S
    _ ≤ ∑ v ∈ S,4 := sum_le_sum (fun v hv => deg_le_four M hM (hS hv))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]

end WaveTurbulence.Mole.AppbAlgorithm
