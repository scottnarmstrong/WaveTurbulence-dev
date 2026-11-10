/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproC2Second
public import WaveTurbulence.Foundations.FinalCount.SubproVcShape
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHingePair
import Mathlib.Tactic

/-!
# S4-DISJ: the Step-1 objects `C₁ ∪ C₂` of S2a's construction are pairwise atom-disjoint (TARGET L2175)

Package theorem for `collectionChoices G σ` (S2a) and G3's `C2Of`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3 Finset

variable {w d : ℕ}

/-- **`C₂` against `C₁` and the hinges.** A member of `C₂` lies in a host disjoint from `C₁` and the hinges. -/
theorem c2Of_disjoint_c1_hinges {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀]
    {M₀ : Molecule V D₀} {L γ η : ℝ} {base : Mom d} {κ : D₀ → (Fin d → ℤ)} (C : CollData M₀)
    {Unsel : Set (Object M₀)} {U : Object M₀} (hU : U ∈ C.C2Of L γ η base κ Unsel) :
    (∀ i, Disjoint U.atoms (C.collection i).atoms) ∧ Disjoint U.atoms C.hinges := by
  obtain ⟨⟨⟨hsg, hout, hdis, hhost⟩, _⟩, _⟩ := hU
  refine ⟨?_, hdis⟩
  intro i
  rcases hhost with ⟨S, a, b, hDV, hsub, hSh, hSC⟩ | ⟨Q, hsub, hQk, hQh, hQC⟩
  · exact Finset.disjoint_of_subset_left hsub (hSC i)
  · exact Finset.disjoint_of_subset_left hsub (hQC i)

end WaveTurbulence.Subpro
