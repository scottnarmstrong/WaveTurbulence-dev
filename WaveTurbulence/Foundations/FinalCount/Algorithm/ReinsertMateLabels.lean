/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33SeparatedInvariants
import Mathlib.Tactic

/-! # Bond-label equality survives reinsertion and independent component projection -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem componentHull_mate_labels (M : Molecule V D) (S : Finset V)
    (hS : AppbClosedSide M S) {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    (hA : ∀ κ,A κ → ∀ x,κ (M.mate x) = κ x)
    {κ : D → (Fin d → ℤ)} (hκ : appbComponentHull M S A κ) :
    ∀ x,κ (M.mate x) = κ x := by
  intro x
  by_cases hx : M.atom x ∈ S
  · obtain ⟨ζ,hζ,he⟩ := hκ.1
    have hmx := (hS.mate_mem x).mp hx
    have h1 : ζ x = κ x := congrFun he ⟨x,hx⟩
    have h2 : ζ (M.mate x) = κ (M.mate x) := congrFun he ⟨M.mate x,hmx⟩
    exact h2.symm.trans ((hA ζ hζ x).trans h1)
  · obtain ⟨ζ,hζ,he⟩ := hκ.2
    have hx' : M.atom x ∈ M.atoms \ S := mem_sdiff.mpr ⟨M.atom_mem x,hx⟩
    have hmx : M.atom (M.mate x) ∈ M.atoms \ S :=
      mem_sdiff.mpr ⟨M.atom_mem _,fun hh => hx ((hS.mate_mem x).mpr hh)⟩
    have h1 : ζ x = κ x := congrFun he ⟨x,hx'⟩
    have h2 : ζ (M.mate x) = κ (M.mate x) := congrFun he ⟨M.mate x,hmx⟩
    exact h2.symm.trans ((hA ζ hζ x).trans h1)

theorem reinsertedPost_mate_labels {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    (a b : ℕ) (i : Fin P.edges.length)
    {ζ : Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)}
    (hζ : r.reinsertedPostAdmissibility A i ζ) :
    ∀ x,ζ ((r.directedPostWithBond a b i).mate x) = ζ x := by
  obtain ⟨κ,hκ,hm,rfl⟩ := hζ
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · exact r.reinsertedLabels_mate κ i a b hm
  · exact r.reinsertedLabels_mate κ i b a hm

theorem s33Separated_mate_labels {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    {ζ : Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)}
    (hζ : appbS33SeparatedPostAdmissibility r A ζ) :
    ∀ x,ζ ((r.directedPostWithBond 3 5 ⟨1,by decide⟩).mate x) = ζ x := by
  exact componentHull_mate_labels _ _
    (appb_s33_reinsert_closedSide M r (appb_s33_splitTopology_of_geometry hg) ⟨1,by decide⟩)
    (r.reinsertedPostAdmissibility A ⟨1,by decide⟩)
    (fun κ hκ => reinsertedPost_mate_labels r A 3 5 ⟨1,by decide⟩ hκ)
    ((appb_s33_separated_iff_componentHull r A ζ).mp hζ)

end WaveTurbulence.Mole.AppbAlgorithm
