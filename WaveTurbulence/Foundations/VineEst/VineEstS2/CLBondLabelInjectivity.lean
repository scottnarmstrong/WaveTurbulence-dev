/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInternalDartNodes

/-! # Internal bond labels determine the actual regional lattice decoration -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

noncomputable def clLocalBondLabels (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (boundary : Fin 4 → Mom d) (κ : CLLocalDecoration R L base boundary) : Bond G.molecule U → (Fin d → ℤ) :=
  fun e => Mole.restrictLabels G (clExtendIndices R κ.1) e.1

/-- The upper joint and three outgoing boundary values are fixed. Every other
node is recovered from a genuine internal incidence, without an extra gauge. -/
theorem clLocalBondLabels_injective {L : ℝ} (hL : L ≠ 0)
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (base : Mom d) (boundary : Fin 4 → Mom d) :
    Function.Injective (clLocalBondLabels R L base boundary) := by
  intro κ η he
  have hnode : ∀ x ∈ clLocalSupport R, clExtendIndices R κ.1 x = clExtendIndices R η.1 x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · by_cases ha : x = a.toNode
      · subst x
        exact clLocalDecoration_boundary_indices_eq R hL base boundary κ η 0
      · obtain ⟨z,hz⟩ := clNode_internalDart_exists hU R x hx ha
        have hκ := gardenInternalDartValue (clExtendIndices R κ.1) κ.2.2.1 z
        have hη := gardenInternalDartValue (clExtendIndices R η.1) η.2.2.1 z
        have hv := congrArg (fun k : Bond G.molecule U → (Fin d → ℤ) => internalDartValue G.molecule U k z) he
        exact (hκ.trans (congrArg (clExtendIndices R κ.1) hz)).symm.trans
          (hv.trans (hη.trans (congrArg (clExtendIndices R η.1) hz)))
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact clLocalDecoration_boundary_indices_eq R hL base boundary κ η j
  apply Subtype.ext
  funext x
  exact (clExtendIndices_apply R κ.1 x.1 x.2).symm.trans
    ((hnode x.1 x.2).trans (clExtendIndices_apply R η.1 x.1 x.2))

end WaveTurbulence.VineEstS2
