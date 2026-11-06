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

theorem one_joint_union_contradiction_dv_subset {w d : ℕ} (G : Garden w) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)}
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection) {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (D : DoubleVine G)
    (hD : P.atoms ∪ Q.atoms ⊆ D.first ∪ D.second)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F) : False := by
  have hQB0 := object_vc_block Q hQvc
  have hPB0 := object_vc_block P hPvc
  have hUel := union_eligible_of_dv_subset G hPvc hPch hQch hPQ hU hPsg D hD hDF
  have hPB := hPB0
  have hQB := hQB0
  rw [hPl] at hPB
  rw [hQu] at hQB
  have hsub := selected_not_strictly_below_vc hc hPm hUel
    (union_not_omitted hc hPB hQB hPQ hU) ⟨_, rfl⟩ subset_union_left
  have hl : Q.lower ∈ P.atoms ∩ Q.atoms :=
    mem_inter.mpr ⟨hsub (mem_union_right _ hQB0.2.2.1), hQB0.2.2.1⟩
  rw [hPQ] at hl
  exact hQB0.2.2.2.1 ((hQu.trans (mem_singleton.mp hl).symm))

end WaveTurbulence.LGSpine
