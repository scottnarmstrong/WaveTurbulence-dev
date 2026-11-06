/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRealizedOrientation
public import WaveTurbulenceVineParam.VineParamBaseOutgoing
import Mathlib.Tactic

/-! # Actual source-directed models of arbitrary expanded vine templates

The selected enumeration and its orientation depend only on the molecule,
not on a decoration or its momentum values.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Outgoing counting in a literal endpoint list is the exact finite bond
count used by the actual source degree theorem. -/
theorem outgoingCount_ofFn {m : ℕ} (A : Fin m → ℕ×ℕ) (v : ℕ) :
    outgoingCount (List.ofFn A) v=((univ : Finset (Fin m)).filter fun j => (A j).1=v).card := by
  rw [outgoingCount,← Fin.univ_val_map,Multiset.countP_map]
  rfl

/-- The unordered shape of a matched actual model is precisely the expanded
source template, retaining every bond occurrence. -/
theorem realizedEnds_shape {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S)
    (he : ∀ j,Sym2.map R.f (M.ends (e j).1)=
      s(((X.expand R.k).bonds[j.1]'j.2).1,((X.expand R.k).bonds[j.1]'j.2).2)) :
    ((List.ofFn (realizedEnds R e) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun p => s(p.1,p.2))=
      ((X.expand R.k).bonds.map (fun p => s(p.1,p.2)) : Multiset (Sym2 ℕ)) := by
  rw [Multiset.map_coe,List.map_ofFn]
  have hp : (fun j => s((realizedEnds R e j).1,(realizedEnds R e j).2))=
      fun j : Fin (X.expand R.k).bonds.length =>
        s(((X.expand R.k).bonds[j.1]'j.2).1,((X.expand R.k).bonds[j.1]'j.2).2) := by
    funext j
    simpa only [realizedEnds,Molecule.ends,Sym2.map_mk] using he j
  change (List.ofFn (fun j => s((realizedEnds R e j).1,(realizedEnds R e j).2)) : Multiset (Sym2 ℕ))=_
  rw [hp]
  exact congrArg (fun l : List (Sym2 ℕ) => (l : Multiset (Sym2 ℕ)))
    (List.ofFn_getElem_eq_map (X.expand R.k).bonds (fun p => s(p.1,p.2)))

/-- Every actual vine has a literal directed model satisfying exactly the
expanded source shape and degree equations. No orientation is a premise. -/
theorem exists_realized_directed_model {M : Molecule V D} (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlockDeg S a b) :
    ∃ e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S,
      ((List.ofFn (realizedEnds R e) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun p => s(p.1,p.2))=
        ((X.expand R.k).bonds.map (fun p => s(p.1,p.2)) : Multiset (Sym2 ℕ)) ∧
      ∀ i : Fin (X.expand R.k).n,
        outgoingCount (List.ofFn (realizedEnds R e)) i.1=if i.1<2 then 1 else 2 := by
  obtain ⟨e,he⟩ := exists_bond_matching R
  refine ⟨e,realizedEnds_shape R e he,?_⟩
  intro i
  rw [outgoingCount_ofFn]
  exact (realizedEnds_degrees hM R hB e i).1

end WaveTurbulence.Vine.Param
