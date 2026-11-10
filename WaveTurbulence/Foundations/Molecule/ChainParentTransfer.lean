/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockChains
public import WaveTurbulence.Foundations.Molecule.MoleculeSingleDeficit
import Mathlib.Tactic

/-! # Parent flow through consecutive CL ingredients
TARGET `blockchainprop`: a shared joint has exactly one internal parent
among its adjacent ingredients, and an endpoint's parent is unchanged
when its actual internal degree is unchanged in the whole block.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem internalParent_mono {A B : Finset (GBranch G.tree)} (hAB : A ⊆ B) {v : GBranch G.tree} :
    InternalParent G A v → InternalParent G B v := by
  rintro ⟨hn,hp⟩
  exact ⟨hn,hAB hp⟩

theorem internalParent_eq_of_degree_eq {A B : Finset (GBranch G.tree)}
    (hAB : A ⊆ B) {v : GBranch G.tree} (hv : v ∈ A)
    (hd : G.molecule.degIn A v = G.molecule.degIn B v) :
    InternalParent G A v ↔ InternalParent G B v := by
  constructor
  · exact internalParent_mono G hAB
  · rintro ⟨hn,hp⟩
    let x : GardenDart G := .inl (⟨v,hn⟩,false)
    have hmem : x ∈ (G.molecule.dartsAt v).filter (G.molecule.InGroup B) :=
      mem_filter.mpr ⟨(mem_dartsAt G.molecule v x).mpr rfl,hAB hv,hp⟩
    rw [← internal_darts_eq_of_degree_eq G.molecule hAB v hd] at hmem
    exact ⟨hn,(mem_filter.mp hmem).2.2⟩

end WaveTurbulence.Mole
