/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIncidenceMultiset
public import WaveTurbulence.Foundations.Molecule.VineRealizationDegrees
import Mathlib.Tactic

/-! # Neighbor multisets transported by the exact undirected realization -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Neighbor contribution of one undirected bond at v, including both
incidences of a loop. -/
@[expose] def bondNeighbors (e : Sym2 V) (v : V) : Multiset V :=
  Sym2.lift ⟨fun x y => (if x=v then {y} else 0)+(if y=v then {x} else 0),
    fun _ _ => add_comm _ _⟩ e

/-- Evaluation on a literal pair retains one neighbor per matching endpoint. -/
theorem bondNeighbors_pair (u w v : V) :
    bondNeighbors s(u,w) v=(if u=v then {w} else 0)+(if w=v then {u} else 0) := rfl

/-- Mapped neighbors of actual internal darts at v. -/
@[expose] def mappedGroupNeighbors (M : Molecule V D) (A : Finset V) (f : V → ℕ) (v : V) : Multiset ℕ :=
  (((M.dartsAt v).filter (M.InGroup A)).val).map (fun x => f (M.atom (M.mate x)))

private theorem sum_singletons {I N : Type*} (T : Finset I) (f : I → N) :
    (∑ x ∈ T,({f x} : Multiset N))=T.val.map f := by
  change (T.val.map (fun x => ({f x} : Multiset N))).sum= _
  have he : T.val.map (fun x => ({f x} : Multiset N))=
      (T.val.map f).map (fun x => ({x} : Multiset N)) := by rw [Multiset.map_map]; rfl
  rw [he,Multiset.sum_map_singleton]

/-- Injectivity of the outer atom map identifies the actual neighbor
multiset with the mapped undirected bond contributions. -/
theorem mappedGroupNeighbors_eq_bonds (M : Molecule V D) {A S : Finset V} (hAS : A ⊆ S)
    (f : V → ℕ) (hf : Set.InjOn f S) {v : V} (hv : v ∈ S) :
    mappedGroupNeighbors M A f v=
      ((((M.groupBonds A).map (Sym2.map f)).map (fun e => bondNeighbors e (f v))).sum) := by
  let weight : D → Multiset ℕ := fun x => if M.atom x=v then {f (M.atom (M.mate x))} else 0
  have hh := sum_internal_darts M A weight
  have hl : (∑ x ∈ univ.filter (M.InGroup A),weight x)=mappedGroupNeighbors M A f v := by
    dsimp only [weight]
    rw [← sum_filter,sum_singletons]
    simp only [mappedGroupNeighbors,Molecule.dartsAt,filter_comm]
  rw [hl] at hh
  rw [hh]
  simp only [Molecule.groupBonds,Multiset.map_map,Function.comp_apply]
  change (∑ x ∈ univ.filter (fun x => M.out x=true ∧ M.InGroup A x), (weight x+weight (M.mate x)))=
    ∑ x ∈ univ.filter (fun x => M.out x=true ∧ M.InGroup A x),bondNeighbors (Sym2.map f (M.ends x)) (f v)
  apply sum_congr rfl
  intro x hx
  have hg := (mem_filter.mp hx).2.2
  have h1 : f (M.atom x)=f v ↔ M.atom x=v :=
    ⟨fun h => hf (hAS hg.1) hv h,congrArg f⟩
  have h2 : f (M.atom (M.mate x))=f v ↔ M.atom (M.mate x)=v :=
    ⟨fun h => hf (hAS hg.2) hv h,congrArg f⟩
  simp only [weight,M.mate_mate,Molecule.ends,Sym2.map_mk,bondNeighbors_pair,h1,h2]

/-- Literal edge-list neighbor multiset, preserving all multiplicities. -/
@[expose] def edgeListNeighbors (es : List (ℕ×ℕ)) (v : ℕ) : Multiset ℕ :=
  (es.map fun e => bondNeighbors s(e.1,e.2) v).sum

/-- The pinned realization transports the entire neighbor multiset, not just
its cardinality. This supplies actual full-rung incidence rows. -/
theorem VineRealization.neighbors {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) {v : V} (hv : v ∈ S) :
    mappedGroupNeighbors M S R.f v=edgeListNeighbors (X.expand R.k).bonds (R.f v) := by
  rw [mappedGroupNeighbors_eq_bonds M (subset_refl S) R.f R.injOn hv,R.bonds_eq]
  simp only [Multiset.map_coe,Multiset.sum_coe,List.map_map,Function.comp_def,edgeListNeighbors]

end WaveTurbulence.Vine
