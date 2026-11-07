/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
public import WaveTurbulence.Foundations.FinalCount.AppBCutTriple
public import WaveTurbulence.Foundations.FinalCount.AppBEndpointSigns
import Mathlib.Tactic

/-! # The exact triple support and boundary cut in the four 3D4 figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD34Kinds : List AppbPatternKind := [.d34one,.d34two,.d34three,.d34four]

theorem appb_d34_kind_length (k : AppbPatternKind) (hk : k ∈ appbD34Kinds) : k.pattern.edges.length = 5 := by
  cases k <;> simp_all [appbD34Kinds,AppbPatternKind.pattern]

theorem appb_d34_incidence_table (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    {M : Molecule V D} (r : AppbRealization M k.pattern) (j : Fin 5) :
    appbIncidence M (r.vertex 1) (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) j)).val =
      (if j < 3 then 1 else 0) ∧
    appbIncidence M (r.vertex 2) (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) j)).val =
      (if j = 2 then 0 else 1) := by
  have ht : ∀ k ∈ appbD34Kinds,1 ∈ k.pattern.vertices ∧ 2 ∈ k.pattern.vertices := by decide
  rw [r.edge_incidence _ 1 (ht k hk).1,r.edge_incidence _ 2 (ht k hk).2]
  simp only [appbD34Kinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  all_goals fin_cases j <;> norm_num [appbFiveEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]

def appbD34Frame {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) : AppbTripleFrame r (r.vertex 1) :=
  appbFiveFirst r (appb_d34_kind_length k hk) _ (fun j => (appb_d34_incidence_table k hk r j).1)

theorem appb_d34_cut_endpoint_table (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    {M : Molecule V D} (r : AppbRealization M k.pattern) (j : Fin 5) :
    let i := appbFiveEmbedding (appb_d34_kind_length k hk) j
    r.vertex k.pattern.edges[i].1 ∈ r.removedAtoms ∧
      (r.vertex k.pattern.edges[i].2 ∈ r.removedAtoms ↔ j < 2) := by
  dsimp only
  rw [r.vertex_mem_removed_iff _ (k.pattern.fst_mem_vertices _),
    r.vertex_mem_removed_iff _ (k.pattern.snd_mem_vertices _)]
  simp only [appbD34Kinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  all_goals fin_cases j <;> norm_num [appbFiveEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]

def appbD34CutTriple {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbD34Kinds)
    (r : AppbRealization M k.pattern) : AppbCutTriple r r.removedAtoms where
  subset_atoms := r.removedAtoms_subset
  crossing := by
    intro x hx
    obtain ⟨hx,hh⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hx,by rcases hh with hh | hh; exact Or.inl hh.1; exact Or.inr hh.2⟩
  index := (⟨![2,3,4],by decide⟩ : Fin 3 ↪ Fin 5).trans (appbFiveEmbedding (appb_d34_kind_length k hk))
  cross := by
    intro j
    change (M.atom (r.edge (appbFiveEmbedding (appb_d34_kind_length k hk) (![2,3,4] j))).val ∈ r.removedAtoms ∧ _ ) ∨ _
    apply (r.edge_cut_cross_iff r.removedAtoms _).mpr
    have hh := appb_d34_cut_endpoint_table k hk r (![2,3,4] j)
    apply Or.inl
    refine ⟨hh.1,?_⟩
    intro hm
    have hj := hh.2.mp hm
    fin_cases j <;> norm_num [Fin.lt_def] at hj
  other := by
    intro i hn
    obtain ⟨j,rfl⟩ := (finCongr (appb_d34_kind_length k hk).symm).surjective i
    apply (r.edge_cut_same_iff r.removedAtoms _).mpr
    have hh := appb_d34_cut_endpoint_table k hk r j
    have hj : j < 2 := by
      fin_cases j
      · decide
      · decide
      · exact False.elim (hn 0 rfl)
      · exact False.elim (hn 1 rfl)
      · exact False.elim (hn 2 rfl)
    exact ⟨fun _ => hh.2.mpr hj,fun _ => hh.1⟩

end WaveTurbulence.Mole
