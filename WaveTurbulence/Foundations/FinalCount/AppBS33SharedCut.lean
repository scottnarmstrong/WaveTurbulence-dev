/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SharedSide
public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBEdgeCutTables
import Mathlib.Tactic

/-! # The exact two-bond cut through the common neighbour in 3S3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbS33SharedKinds : List AppbPatternKind := [.s33new1,.s33new2]

theorem appb_s33_shared_mem (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds) : k ∈ appbS33Kinds := by
  simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl <;> decide


noncomputable def appbS33SharedCutPair {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS33SharedKinds)
    (r : AppbRealization M k.pattern)
    (hside : ∀ a ∈ k.pattern.vertices,r.vertex a ∈ Degen.residualComponent M r.removedAtoms (r.vertex 3) ↔ a = 3) :
    AppbCutPair r (Degen.residualComponent M r.removedAtoms (r.vertex 3)) where
  subset_atoms := fun a ha => ((Degen.mem_residualComponent M r.removedAtoms (r.vertex 3) a).mp ha).1
  crossing := r.residual_cut_crossing (r.vertex 3)
  first := appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk)) 1
  second := appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk)) 3
  distinct := fun he => (by decide : (1 : Fin 5) ≠ 3) ((appbFiveEmbedding _).injective he)
  first_cross := by
    apply (r.edge_cut_cross_iff _ _).mpr
    have ht : ∀ k ∈ appbS33SharedKinds,1 ∈ k.pattern.vertices ∧ 3 ∈ k.pattern.vertices := by decide
    have h1 := hside 1 (ht k hk).1
    have h3 := hside 3 (ht k hk).2
    have he : k.pattern.edges[appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk)) 1] = (1,3) := by
      simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl <;> rfl
    rw [he]
    exact Or.inr ⟨fun h => (by decide : (1 : ℕ) ≠ 3) (h1.mp h),h3.mpr rfl⟩
  second_cross := by
    apply (r.edge_cut_cross_iff _ _).mpr
    have ht : ∀ k ∈ appbS33SharedKinds,2 ∈ k.pattern.vertices ∧ 3 ∈ k.pattern.vertices := by decide
    have h2 := hside 2 (ht k hk).1
    have h3 := hside 3 (ht k hk).2
    have he : k.pattern.edges[appbFiveEmbedding (appb_s33_kind_length k (appb_s33_shared_mem k hk)) 3] = (2,3) := by
      simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl <;> rfl
    rw [he]
    exact Or.inr ⟨fun h => (by decide : (2 : ℕ) ≠ 3) (h2.mp h),h3.mpr rfl⟩
  other := by
    intro i h1 h3
    obtain ⟨j,rfl⟩ := (finCongr (appb_s33_kind_length k (appb_s33_shared_mem k hk)).symm).surjective i
    apply (r.edge_cut_same_iff _ _).mpr
    rw [hside _ (k.pattern.fst_mem_vertices _),hside _ (k.pattern.snd_mem_vertices _)]
    simp only [appbS33SharedKinds,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl
    all_goals fin_cases j
    all_goals first | exact False.elim (h1 rfl) | exact False.elim (h3 rfl) | norm_num [AppbPatternKind.pattern,finCongr]

end WaveTurbulence.Mole
