/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationInverse
public import WaveTurbulence.Foundations.Molecule.VineIncidenceExtraction
public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Transfer of literal full-rung rows to actual molecule darts -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A literal full-rung sequence in a template, retaining the complete
neighbor multiset. This is local combinatorial data, not a source predicate. -/
structure LiteralFullRungSequence (T : VineTemplate) (n : ℕ) where
  u : ℕ → Fin T.n
  v : ℕ → Fin T.n
  distinct : Function.Injective (Sum.elim
    (fun i : Fin n => u (i.1+1)) (fun i : Fin n => v (i.1+1)))
  upper : ∀ i,1 ≤ i → i ≤ n → edgeListNeighbors T.bonds (u i).1=
    (univ : Finset (Fin 4)).val.map (fun j => (![v i,v i,u (i-1),u (i+1)] j).1)
  lower : ∀ i,1 ≤ i → i ≤ n → edgeListNeighbors T.bonds (v i).1=
    (univ : Finset (Fin 4)).val.map (fun j => (![u i,u i,v (i-1),v (i+1)] j).1)

omit [DecidableEq D] in
/-- Exact literal neighbor rows recover actual distinct darts under the
pinned realization. No orientation or extra incidence premise is needed. -/
theorem VineRealization.fourIncidences {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (v : Fin (X.expand R.k).n) (neighbors : Fin 4 → Fin (X.expand R.k).n)
    (hrow : edgeListNeighbors (X.expand R.k).bonds v.1=
      (univ : Finset (Fin 4)).val.map (fun j => (neighbors j).1)) :
    Nonempty (FourIncidences M (R.atomAt v).1 (fun j => (R.atomAt (neighbors j)).1)) := by
  apply exists_fourIncidences_of_neighbors M S R.f R.injOn _ _ (fun j => (R.atomAt (neighbors j)).2)
  rw [R.neighbors (R.atomAt v).2,R.label_atomAt,hrow]
  congr 1
  funext j
  exact (R.label_atomAt (neighbors j)).symm

/-- Every literal full-rung sequence lifts to actual full-rung incidences. -/
@[expose] noncomputable def LiteralFullRungSequence.realize {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) {n : ℕ}
    (L : LiteralFullRungSequence (X.expand R.k) n) : FullRungSequence M n where
  u := fun i => (R.atomAt (L.u i)).1
  v := fun i => (R.atomAt (L.v i)).1
  distinct := by
    intro i j hij
    apply L.distinct
    apply R.atomAt_injective
    cases i <;> cases j <;> exact hij
  upper := by
    intro i hi hin
    have hh := R.fourIncidences (L.u i) ![L.v i,L.v i,L.u (i-1),L.u (i+1)] (L.upper i hi hin)
    have he : (fun j => (R.atomAt (![L.v i,L.v i,L.u (i-1),L.u (i+1)] j)).1)=
        ![(R.atomAt (L.v i)).1,(R.atomAt (L.v i)).1,
          (R.atomAt (L.u (i-1))).1,(R.atomAt (L.u (i+1))).1] := by
      funext j
      fin_cases j <;> rfl
    rw [he] at hh
    exact Classical.choice hh
  lower := by
    intro i hi hin
    have hh := R.fourIncidences (L.v i) ![L.u i,L.u i,L.v (i-1),L.v (i+1)] (L.lower i hi hin)
    have he : (fun j => (R.atomAt (![L.u i,L.u i,L.v (i-1),L.v (i+1)] j)).1)=
        ![(R.atomAt (L.u i)).1,(R.atomAt (L.u i)).1,
          (R.atomAt (L.v (i-1))).1,(R.atomAt (L.v (i+1))).1] := by
      funext j
      fin_cases j <;> rfl
    rw [he] at hh
    exact Classical.choice hh

end WaveTurbulence.Vine
