/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
public import WaveTurbulence.Foundations.FinalCount.AppBComponentEffects
import Mathlib.Tactic

/-! # Actual residual component bounds from displayed boundary labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Every residual component contains a surviving displayed label. This
bounds its actual quotient by the finite label set, without no-bridge data. -/
theorem post_components_le_boundary_labels
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty) : r.post.numComponents ≤ (P.vertices \ P.removed).card := by
  let f : ↥(P.vertices \ P.removed) → AppbComponents r.post := fun a =>
    appbComponent r.post ⟨r.vertex a.val,r.vertex_mem_post a.val (mem_sdiff.mp a.property).1 (mem_sdiff.mp a.property).2⟩
  have hs : Function.Surjective f := by
    intro q
    induction q using Quot.inductionOn with | h v =>
      obtain ⟨a,ha,hka,hpath⟩ := r.post_reaches_displayed hconn hne v.property
      refine ⟨⟨a,mem_sdiff.mpr ⟨ha,hka⟩⟩,?_⟩
      exact (quotient_eq_of_sameComponent r.post hpath v.property (r.vertex_mem_post a ha hka)).symm
  have hc := Nat.card_le_card_of_surjective f hs
  simpa only [Molecule.numComponents,Nat.card_eq_finsetCard] using hc

/-- A connected special-pair graph has at most two residual components;
this allows the pair's single bond to have become a bridge. -/
theorem special_pair_post_components
    (r : AppbRealization M AppbPatternKind.s33new3.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    r.post.numComponents = 1 ∨ r.post.numComponents = 2 := by
  have hb := r.post_components_le_boundary_labels hconn (by decide)
  have hc : (AppbPatternKind.s33new3.pattern.vertices \ AppbPatternKind.s33new3.pattern.removed).card = 2 := by decide
  rw [hc] at hb
  have hp := appb_numComponents_pos r.post (r.post_atoms_nonempty (by decide))
  omega

end AppbRealization
end WaveTurbulence.Mole
