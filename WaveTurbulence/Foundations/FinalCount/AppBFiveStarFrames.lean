/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFullStarCount
import Mathlib.Tactic

/-! # The actual two triple supports in all seven 3S3 figure groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbS33Kinds : List AppbPatternKind := [.s33,.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6]

theorem appb_s33_kind_length (k : AppbPatternKind) (hk : k ∈ appbS33Kinds) : k.pattern.edges.length = 5 := by
  cases k <;> simp_all [appbS33Kinds,AppbPatternKind.pattern]

def appbFiveEmbedding {P : AppbPattern} (h : P.edges.length = 5) : Fin 5 ↪ Fin P.edges.length :=
  (finCongr h.symm).toEmbedding

def appbFiveFirst {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)
    (h : P.edges.length = 5) (v : V)
    (hi : ∀ j : Fin 5, appbIncidence M v (r.edge (appbFiveEmbedding h j)).val = if j < 3 then 1 else 0) :
    AppbTripleFrame r v where
  index := ⟨fun j => appbFiveEmbedding h ⟨j.val,by omega⟩,by intro a b he; exact Fin.ext (congrArg (fun z : Fin 5 => z.val) ((appbFiveEmbedding h).injective he))⟩
  incidence := by
    intro j
    change appbIncidence M v (r.edge (appbFiveEmbedding h ⟨j.val,by omega⟩)).val = 1
    rw [hi]
    fin_cases j <;> norm_num [Fin.lt_def]
  other := by
    intro i hn
    obtain ⟨j,rfl⟩ := (finCongr h.symm).surjective i
    change appbIncidence M v (r.edge (appbFiveEmbedding h j)).val = 0
    rw [hi]
    have hj : ¬j < 3 := by
      intro hj
      exact hn ⟨j.val,hj⟩ rfl
    simp only [hj,ite_false]

def appbFiveSecond {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)
    (h : P.edges.length = 5) (v : V)
    (hi : ∀ j : Fin 5, appbIncidence M v (r.edge (appbFiveEmbedding h j)).val = if j = 0 ∨ 3 ≤ j.val then 1 else 0) :
    AppbTripleFrame r v where
  index := (⟨![0,3,4],by decide⟩ : Fin 3 ↪ Fin 5).trans (appbFiveEmbedding h)
  incidence := by intro j; change appbIncidence M v (r.edge (appbFiveEmbedding h (![0,3,4] j))).val = 1; rw [hi]; fin_cases j <;> decide
  other := by
    intro i hn
    obtain ⟨j,rfl⟩ := (finCongr h.symm).surjective i
    change appbIncidence M v (r.edge (appbFiveEmbedding h j)).val = 0
    rw [hi]
    fin_cases j
    · exact False.elim (hn 0 rfl)
    · decide
    · decide
    · exact False.elim (hn 1 rfl)
    · exact False.elim (hn 2 rfl)

theorem appb_s33_first_incidence (k : AppbPatternKind) (hk : k ∈ appbS33Kinds)
    {M : Molecule V D} (r : AppbRealization M k.pattern) (j : Fin 5) :
    appbIncidence M (r.vertex 1) (r.edge (appbFiveEmbedding (appb_s33_kind_length k hk) j)).val =
      if j < 3 then 1 else 0 := by
  have hv : 1 ∈ k.pattern.vertices := by cases k <;> simp_all [appbS33Kinds,AppbPatternKind.pattern,AppbPattern.vertices]
  rw [r.edge_incidence _ 1 hv]
  simp only [appbS33Kinds,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals fin_cases j <;> norm_num [appbFiveEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]

theorem appb_s33_second_incidence (k : AppbPatternKind) (hk : k ∈ appbS33Kinds)
    {M : Molecule V D} (r : AppbRealization M k.pattern) (j : Fin 5) :
    appbIncidence M (r.vertex 2) (r.edge (appbFiveEmbedding (appb_s33_kind_length k hk) j)).val =
      if j = 0 ∨ 3 ≤ j.val then 1 else 0 := by
  have hv : 2 ∈ k.pattern.vertices := by cases k <;> simp_all [appbS33Kinds,AppbPatternKind.pattern,AppbPattern.vertices]
  rw [r.edge_incidence _ 2 hv]
  simp only [appbS33Kinds,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals fin_cases j <;> norm_num [appbFiveEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]

end WaveTurbulence.Mole
