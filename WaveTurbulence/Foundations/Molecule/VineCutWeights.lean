/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineIncidenceMultiset
public import WaveTurbulence.Foundations.Molecule.VineBoundaryCounts
public import WaveTurbulence.Foundations.Molecule.VineBondRestriction
import Mathlib.Tactic

/-! # Cut sizes from exact undirected bond multisets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- One crossing bond contributes one boundary dart; internal or external
bonds contribute zero. This definition retains bond multiplicity. -/
@[expose] def cutWeight (A : Finset V) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun x y => (if x ∈ A ∧ y ∉ A then 1 else 0)+
    (if y ∈ A ∧ x ∉ A then 1 else 0),fun _ _ => add_comm _ _⟩ e

/-- Evaluate the undirected cut weight on one raw bond. -/
theorem cutWeight_pair (A : Finset V) (x y : V) : cutWeight A s(x,y)=
    (if x ∈ A ∧ y ∉ A then 1 else 0)+(if y ∈ A ∧ x ∉ A then 1 else 0) := rfl

/-- All boundary darts of A are internal darts of S if A's incident
neighbors stay inside S. The edge-multiset cut sum is then its exact boundary. -/
theorem boundary_card_eq_cutWeight (M : Molecule V D) {A S : Finset V}
    (hAS : A ⊆ S) (hclosed : ∀ d,M.atom d ∈ A → M.atom (M.mate d) ∈ S) :
    (boundary M A).card=((M.groupBonds S).map (cutWeight A)).sum := by
  let weight : D → ℕ := fun d => if M.atom d ∈ A ∧ M.atom (M.mate d) ∉ A then 1 else 0
  have hh := sum_internal_darts M S weight
  have he : (univ.filter (M.InGroup S)).filter
      (fun d => M.atom d ∈ A ∧ M.atom (M.mate d) ∉ A)=boundary M A := by
    ext d
    simp only [mem_filter,mem_univ,true_and,boundary,Molecule.InGroup]
    constructor
    · tauto
    · intro hd
      exact ⟨⟨hAS hd.1,hclosed d hd.1⟩,hd⟩
  have hl : (∑ d ∈ univ.filter (M.InGroup S),weight d)=(boundary M A).card := by
    simp only [weight,sum_boole,Nat.cast_id,he]
  rw [hl] at hh
  rw [hh]
  simp only [Molecule.groupBonds,Multiset.map_map,Function.comp_def]
  change _=∑ d ∈ univ.filter (fun d => M.out d=true ∧ M.InGroup S d),cutWeight A (M.ends d)
  apply sum_congr rfl
  intro d _hd
  simp only [weight,Molecule.ends,cutWeight_pair,M.mate_mate]

/-- The cut weight is unchanged by an injective outer atom relabeling. -/
theorem cutWeight_map_of_injOn {A S : Finset V} (hAS : A ⊆ S) (f : V → ℕ)
    (hf : Set.InjOn f S) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    cutWeight (A.image f) (Sym2.map f s(x,y))=cutWeight A s(x,y) := by
  simp only [Sym2.map_mk,cutWeight_pair,mem_image_iff_of_injOn hAS f hf hx,
    mem_image_iff_of_injOn hAS f hf hy]

end WaveTurbulence.Vine
