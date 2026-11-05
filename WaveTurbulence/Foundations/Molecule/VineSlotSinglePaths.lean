/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSingleRailPaths
public import WaveTurbulence.Foundations.Molecule.VineSlotRailFrame
public import WaveTurbulence.Foundations.Molecule.VineSingleCoreEdges
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotEdges
import Mathlib.Tactic

/-! # Every expanded source slot has two single-bond connecting rail paths -/

public section
namespace WaveTurbulence.Vine

/-- The unordered multiplicity of either slot edge is exactly one. -/
theorem template_slot_unordered_single (X : VineType) : ∀ s ∈ X.template.slots,
    X.template.bonds.count s.1+X.template.bonds.count (s.1.2,s.1.1)=1 ∧
    X.template.bonds.count s.2+X.template.bonds.count (s.2.2,s.2.1)=1 := by
  cases X <;> decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact source slot data supply single-bond paths between the old
ports, including zero inserted rungs and type II's shared final joint. -/
theorem VineRealization.slot_single_paths {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (Q : FullRungSequence M k) (hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+(i-1) ∧
      R.f (Q.v i)=(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n+k+(i-1)) :
    Relation.EqvGen (SingleGroupAdj M S) (Q.u 0) (Q.u (k+1)) ∧
      Relation.EqvGen (SingleGroupAdj M S) (Q.v 0) (Q.v (k+1)) := by
  have hsk : (s,k) ∈ X.template.slots.zip R.k := by
    rw [hloc]
    exact List.mem_append_right _ List.mem_cons_self
  have hs := (List.of_mem_zip hsk).1
  have hb := template_slot_endpoints X s hs
  have hc := template_slot_unordered_single X s hs
  have hn := template_slot_edges_nonloop X s hs
  by_cases hk : k=0
  · subst k
    have old (u v : V) (hu : u ∈ S) (hv : v ∈ S) (i j : ℕ)
        (hi : i<X.template.n) (hj : j<X.template.n) (hij : i ≠ j)
        (hui : R.f u=i) (hvj : R.f v=j)
        (hc : X.template.bonds.count (i,j)+X.template.bonds.count (j,i)=1)
        (ha : M.Adj u v) : Relation.EqvGen (SingleGroupAdj M S) u v := by
      have hne : u ≠ v := by intro he; exact hij (hui.symm.trans ((congrArg R.f he).trans hvj))
      have hd := R.old_pair_degree_le hu hv hne (by rw [hui]; exact hi) (by rw [hvj]; exact hj)
      rw [hui,hvj,hc] at hd
      have hp := pair_degree_pos_of_adj M ha
      exact Relation.EqvGen.rel _ _ ⟨hu,hv,hne,ha,by omega⟩
    constructor
    · exact old _ _ (hmem 0).1 (hmem 1).1 _ _ hb.1 hb.2.1 hn.1
        hports.1 hports.2.2.1 hc.1
        (R.zero_slot_adj s hsk s.1 (Or.inl rfl) (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1)
    · exact old _ _ (hmem 0).2 (hmem 1).2 _ _ hb.2.2.1 hb.2.2.2 hn.2
        hports.2.1 hports.2.2.2 hc.2
        (R.zero_slot_adj s hsk s.2 (Or.inr rfl) (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2)
  · let F := R.slot_rail_frame pre post s k hloc Q hports hlabels
    exact ⟨F.upper_single_complete hM S hmem (by omega),
      F.lower_single_complete hM S hmem (by omega)⟩

end WaveTurbulence.Vine
