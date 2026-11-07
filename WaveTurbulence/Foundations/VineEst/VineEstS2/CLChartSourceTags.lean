/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorSourceOrigins

/-! # Actual chart origins use only interior labels and the two lower boundaries -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

abbrev CLChartSourceTag (R : CLRegionData G U a b) :=
  (Fin (clLocalOrder1 R) ⊕ Fin (clLocalOrder1 R)) ⊕ Fin 2

def chartSourceTag (R : CLRegionData G U a b) : CLChartSourceTag R → CLSourceOrigin R
  | .inl o => interiorSourceTag R o
  | .inr j => .inr (.inr (if j = 0 then 2 else 3))

/-- In particular, no constrained upper boundary coordinate can be
mistaken for an independent affine parameter in the frozen (iii) identities. -/
theorem clOrigin_chartSourceTag (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (p : Bond G.molecule U ⊕ Fin 2) :
    ∃ o : CLChartSourceTag R, ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
      origin G.molecule U (fun e => Mole.restrictLabels G κ e.1)
        (κ (clBoundaryNodes R 2)) (κ (clBoundaryNodes R 2)-κ (clBoundaryNodes R 3)) p =
        clSourceOriginValue hU R hG Ei Ep κ (chartSourceTag R o) := by
  cases p with
  | inl e =>
    obtain ⟨o,ho⟩ := clBond_interiorOrigin hU R hG Ei Ep e
    exact ⟨.inl o,ho⟩
  | inr j =>
    refine ⟨.inr j,?_⟩
    intro E _ κ _
    by_cases hj : j = 0 <;>
      simp only [origin,chartSourceTag,hj,ite_true,ite_false,sub_sub_cancel,clSourceOriginValue]

end WaveTurbulence.VineEstS2
