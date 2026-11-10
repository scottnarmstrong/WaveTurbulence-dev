/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceUnionContradiction
/-! One-joint block union of two selected ordinary objects both lying inside the atoms of one
double vine: the union is eligible, not omitted and strictly larger. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceUnionDV` (sha256 3b5faeb1a68cc7d9b254d96bd00dff468c16a7f29750e07a93e1899dbd790d4c) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

theorem union_eligible_of_dv_subset {w d : ℕ} (G : Garden w) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)}
    {P Q : Object γv G.molecule} {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h)
    (hPch : Chain γv G.molecule P.atoms P.upper cj n) (hQch : Chain γv G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (D : DoubleVine γv G)
    (hD : P.atoms ∪ Q.atoms ⊆ D.first ∪ D.second)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F) :
    eligibleSecondObject γv G L γ η base κ F (oneJointUnionObject hPch hQch hPQ hU) := by
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  exact ⟨oneJointUnionObject_hasGapKind hPch hQch hPQ hU ⟨rP, hrP, hkP⟩, Or.inr ⟨D, hD, hDF⟩⟩

end WaveTurbulence.GammaLow.Famc
