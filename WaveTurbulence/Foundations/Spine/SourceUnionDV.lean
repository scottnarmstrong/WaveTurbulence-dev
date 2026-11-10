/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceUnionContradiction
/-! One-joint block union of two selected ordinary objects both lying inside the atoms of one
double vine: the union is eligible, not omitted and strictly larger. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

theorem union_eligible_of_dv_subset {w d : ℕ} (G : Garden w) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)}
    {P Q : Object G.molecule} {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (D : DoubleVine G)
    (hD : P.atoms ∪ Q.atoms ⊆ D.first ∪ D.second)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F) :
    eligibleSecondObject G L γ η base κ F (oneJointUnionObject hPch hQch hPQ hU) := by
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  exact ⟨oneJointUnionObject_hasGapKind hPch hQch hPQ hU ⟨rP, hrP, hkP⟩, Or.inr ⟨D, hD, hDF⟩⟩

end WaveTurbulence.LGSpine
