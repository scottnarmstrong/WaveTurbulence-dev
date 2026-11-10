/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionSupport
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PhysicalDecorations

/-! # The actual finite regional decoration fiber with four exterior momenta -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def clExtendIndices {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (z : ↥(clLocalSupport R) → (Fin d → ℤ)) (x : GNode G.tree) : Fin d → ℤ := by
  classical
  exact if hx : x ∈ clLocalSupport R then z ⟨x,hx⟩ else 0

/-- Genuine local conservation, matching of the completely paired internal
leaves, and four physical boundary values. Exterior labels are not parameters. -/
def CLLocalDecoration {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (boundary : Fin 4 → Mom d) : Type :=
  {z : ↥(clLocalSupport R) → (Fin d → ℤ) //
    (∀ v ∈ U, clExtendIndices R z v.toNode = clExtendIndices R z (v.child 0) -
      clExtendIndices R z (v.child 1) + clExtendIndices R z (v.child 2)) ∧
    (∀ ℓ, Mole.IsInternalLeaf G U ℓ → clExtendIndices R z ℓ.toNode = clExtendIndices R z (G.pair ℓ).toNode) ∧
    ∀ j, base+latticePoint L (clExtendIndices R z (clBoundaryNodes R j)) = boundary j}

theorem clExtendIndices_apply {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (z : ↥(clLocalSupport R) → (Fin d → ℤ)) (x : GNode G.tree) (hx : x ∈ clLocalSupport R) :
    clExtendIndices R z x = z ⟨x,hx⟩ := by
  classical
  exact dite_eq_left hx

theorem clExtendIndices_restrict {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) (κ : GNode G.tree → (Fin d → ℤ))
    (x : GNode G.tree) (hx : x ∈ clLocalSupport R) :
    clExtendIndices R (fun y => κ y.1) x = κ x := clExtendIndices_apply R _ x hx

theorem latticePoint_injective_of_ne_zero {d : ℕ} {L : ℝ} (hL : L ≠ 0) :
    Function.Injective (latticePoint (d := d) L) := by
  intro u v he
  funext j
  have hj := congrArg (fun k : Mom d => k j) he
  change (u j : ℝ)/L = (v j : ℝ)/L at hj
  have hm := congrArg (fun t : ℝ => t*L) hj
  simp only [div_mul_cancel₀ _ hL] at hm
  exact Int.cast_inj.mp hm

/-- Fixed physical boundary values leave no hidden extra lattice summation at
the four boundary nodes (the standing source scale has L > 0). -/
theorem clLocalDecoration_boundary_indices_eq {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (boundary : Fin 4 → Mom d) (κ η : CLLocalDecoration R L base boundary) (j : Fin 4) :
    clExtendIndices R κ.1 (clBoundaryNodes R j) = clExtendIndices R η.1 (clBoundaryNodes R j) :=
  latticePoint_injective_of_ne_zero hL (add_left_cancel ((κ.2.2.2 j).trans (η.2.2.2 j).symm))

end WaveTurbulence.RegRed
