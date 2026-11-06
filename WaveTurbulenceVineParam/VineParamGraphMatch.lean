/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedGraphIso
public import WaveTurbulence.Foundations.Molecule.VineFiniteMatching
import Mathlib.Tactic

/-! # Directed graph isomorphisms from matched label multisets

Generic helpers for the expanded-template induction: composition of directed
graph isomorphisms, orientation of a multiset with a prescribed unordered
shadow, and an isomorphism from equal directed label multisets.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

namespace DirectedGraphIso
variable {V W Y β δ γ : Type*}

/-- The identity isomorphism. -/
@[expose] def refl (ends : β → V×V) : DirectedGraphIso ends ends where
  atom := Equiv.refl _
  edge := Equiv.refl _
  endpoints := fun _ => rfl

/-- Inverse of a directed graph isomorphism. -/
@[expose] def symm {ends : β → V×V} {other : δ → W×W} (I : DirectedGraphIso ends other) :
    DirectedGraphIso other ends where
  atom := I.atom.symm
  edge := I.edge.symm
  endpoints := by
    intro e
    have h := I.endpoints (I.edge.symm e)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    simp

/-- Composition of directed graph isomorphisms. -/
@[expose] def trans {ends : β → V×V} {other : δ → W×W} {third : γ → Y×Y}
    (I : DirectedGraphIso ends other) (J : DirectedGraphIso other third) :
    DirectedGraphIso ends third where
  atom := I.atom.trans J.atom
  edge := I.edge.trans J.edge
  endpoints := by
    intro e
    simp only [Equiv.trans_apply]
    rw [J.endpoints,I.endpoints]

end DirectedGraphIso

/-- A multiset of ordered pairs whose unordered shadow is a prescribed list is
an orientation of that list, entry by entry. -/
theorem exists_orientation {α : Type*} [DecidableEq α] (L : List (α×α)) (D : Multiset (α×α))
    (h : D.map (fun e => s(e.1,e.2)) = ((L.map fun e => s(e.1,e.2) : List (Sym2 α)) : Multiset (Sym2 α))) :
    ∃ D' : List (α×α), D = (D' : Multiset (α×α)) ∧
      List.Forall₂ (fun d l => d = l ∨ d = l.swap) D' L := by
  induction L generalizing D with
  | nil =>
    refine ⟨[],?_,List.Forall₂.nil⟩
    simp only [List.map_nil,Multiset.coe_nil,Multiset.map_eq_zero] at h
    simpa using h
  | cons l L ih =>
    have hm : s(l.1,l.2) ∈ D.map (fun e => s(e.1,e.2)) := by
      rw [h]; simp
    obtain ⟨d,hd,hds⟩ := Multiset.mem_map.mp hm
    obtain ⟨D1,rfl⟩ := Multiset.exists_cons_of_mem hd
    simp only [Multiset.map_cons,List.map_cons,← Multiset.cons_coe] at h
    rw [hds] at h
    have h2 := (Multiset.cons_inj_right _).mp h
    obtain ⟨D',hD',hF⟩ := ih D1 h2
    refine ⟨d :: D',?_,List.Forall₂.cons ?_ hF⟩
    · rw [← Multiset.cons_coe,hD']
    · rcases Sym2.eq_iff.mp hds with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)

end WaveTurbulence.Vine.Param
