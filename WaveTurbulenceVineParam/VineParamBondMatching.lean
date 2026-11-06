/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulence.Foundations.Molecule.VineFiniteMatching
public import WaveTurbulence.Foundations.Molecule.VineRealizationInverse
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # Actual bond occurrences match the literal expanded vine, with multiplicity -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Internal outgoing darts are the actual directed bonds of the vine. -/
@[expose] def internalBonds (M : Molecule V D) (S : Finset V) : Finset D :=
  univ.filter (fun e => M.out e=true ∧ M.InGroup S e)

omit [DecidableEq D] in
/-- A realized vine has a bijection between literal bond occurrences and
actual directed bonds, preserving unordered endpoints. No distinction of
parallel bonds is lost and no orientation is assumed from the drawing. -/
theorem exists_bond_matching {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) :
    ∃ e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S,
      ∀ i,Sym2.map R.f (M.ends (e i).1)=
        s(((X.expand R.k).bonds[i.1]'i.2).1,((X.expand R.k).bonds[i.1]'i.2).2) := by
  classical
  let es := (X.expand R.k).bonds
  let label : Fin es.length → Sym2 ℕ := fun i => s((es[i.1]'i.2).1,(es[i.1]'i.2).2)
  let actual : internalBonds M S → Sym2 ℕ := fun e => Sym2.map R.f (M.ends e.1)
  have hl : (univ : Finset (Fin es.length)).val.map label=
      (es.map (fun p => s(p.1,p.2)) : Multiset (Sym2 ℕ)) := by
    rw [Fin.univ_val_map]
    exact congrArg (fun l : List (Sym2 ℕ) => (l : Multiset (Sym2 ℕ)))
      (List.ofFn_getElem_eq_map es (fun p => s(p.1,p.2)))
  have ha : (univ : Finset (internalBonds M S)).val.map actual=
      (M.groupBonds S).map (Sym2.map R.f) := by
    simpa only [actual,internalBonds,Molecule.groupBonds,Multiset.map_map,Function.comp_apply] using
      univ_subtype_map (internalBonds M S) (fun e => Sym2.map R.f (M.ends e))
  obtain ⟨e,he⟩ := exists_label_matching label actual (hl.trans (R.bonds_eq.symm.trans ha.symm))
  exact ⟨e,he⟩

end WaveTurbulence.Vine.Param
