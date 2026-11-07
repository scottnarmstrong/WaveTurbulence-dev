/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TBCleanupReduction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33CleanupSelection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33CleanupSelection
import Mathlib.Tactic

/-! # Source reinsertion cleanup, with concrete analytic post data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set
universe u v

/-- DH23 algorithm two(c), including the optional TB normal count bound
and every inherited physical invariant, with a carrier-uniform threshold. -/
theorem exists_s33_cleanup_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,∀ (M : Molecule V D),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    ∀ r : AppbRealization M AppbPatternKind.s33.pattern,AppbS33SplitGeometry M r →
    ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4) →
    ∀ (g : ℝ) (w : Mom d)
      (A : (Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L w ζ g) →
      AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 5 ⟨1,by decide⟩) L γ δ C1 g w A P) := by
  obtain ⟨C₀,L₀,hC₀,hbase⟩ := exists_tb_cleanup_reduction_of_selected_figure d hd γ hγ
  refine ⟨C₀,L₀,hC₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M hM hno hnt r hg hdef g w A P hLG
  rcases s33_cleanup_selection M hM hno hnt r hg hdef with h | ⟨k,hk,t,ht⟩
  · exact Or.inl h
  · exact Or.inr (hbase V _ C1 hC1 L hL δ hδ _
      (appb_s33_reinsert_isMolecule M hM r hg hdef)
      (r.directedPostWithBond_noLoops 3 5 ⟨1,by decide⟩ hno (by decide) (by decide) (by decide))
      k hk t ht g w A P hLG)

/-- DH23 algorithm three(c-ii), including the optional eligible TB cleanup.
The forbidden four/four triple is excluded by the actual failed continuation
and residual common-neighbor tests. -/
theorem exists_d33_cleanup_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C₀ L₀ : ℝ,1 ≤ C₀ ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ C1 ≥ C₀,∀ L ≥ L₀,∀ δ ∈ Ioc (0 : ℝ) 1,∀ (M : Molecule V D),
    M.IsMolecule → AppbNoLoops M → AppbNoTripleBonds M →
    ∀ r : AppbRealization M AppbPatternKind.d33.pattern,AppbD33BoundaryOpposite M r →
    (∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b) → (∀ e : D,¬Degen.IsBridge M e) →
    ¬D33Continues r → ¬HasD33ResidualCommon r → AppbD33ResidualDefect M r →
    ∀ (g : ℝ) (w : Mom d)
      (A : (Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
    (∀ ζ,A ζ → AppbLargeGap (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L w ζ g) →
      AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
      Nonempty (TBCleanupReduction (r.directedPostWithBond 3 4 ⟨2,by decide⟩) L γ δ C1 g w A P) := by
  obtain ⟨C₀,L₀,hC₀,hbase⟩ := exists_tb_cleanup_reduction_of_selected_figure d hd γ hγ
  refine ⟨C₀,L₀,hC₀,?_⟩
  intro V D instV instF instD C1 hC1 L hL δ hδ M hM hno hnt r ho hc hb hn ht hdef g w A P hLG
  rcases d33_cleanup_selection M hM hno hnt r ho hc hb hn ht hdef with h | ⟨k,hk,t,hpost⟩
  · exact Or.inl h
  · exact Or.inr (hbase V _ C1 hC1 L hL δ hδ _
      (appb_d33_reinsert_isMolecule M hM r hc hb ho hdef)
      (r.directedPostWithBond_noLoops 3 4 ⟨2,by decide⟩ hno (by decide) (by decide) (by decide))
      k hk t hpost g w A P hLG)

end WaveTurbulence.Mole.AppbAlgorithm
