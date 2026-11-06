/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamondObjects
/-! Hyper LG/ZG containers: an object meeting a hyper object without being nested in either is
impossible (the overlap classification forces both to be ordinary blocks, but a hyper object has
joint degree three). Hence the one-joint union of two selected ordinary objects, one inside a
hyper container, is eligible, non-omitted and strictly larger: contradiction. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A hyper object meeting any object, neither nested in the other, is impossible. -/
theorem object_hyper_overlap_nested {M : Molecule V D} (hM : M.IsMolecule) (Q C : Object M)
    (hCh : ∃ R, C.shape = .hyper R) (hne : (Q.atoms ∩ C.atoms).Nonempty)
    (hQC : ¬ Q.atoms ⊆ C.atoms) (hCQ : ¬ C.atoms ⊆ Q.atoms) : False := by
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises Q
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises C
  obtain ⟨_, hCB, _⟩ := Mole.molecule_overlap_classification M hM RA RB hne hQC hCQ hdA hdB hiA hiB
  have h2 := (Mole.block_joint_degrees M hCB).1
  have h3 := (object_degIn_upper C).2 hCh
  omega

theorem union_eligible_of_hyper_container {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)}
    {P Q C : Object G.molecule} {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hCh : ∃ R, C.shape = .hyper R)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG)
    (hCF : Disjoint (↑C.atoms : Set (GBranch G.tree)) F)
    (hPC : P.atoms ⊆ C.atoms ∨ Q.atoms ⊆ C.atoms)
    (hCk : C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) :
    eligibleSecondObject G L γ η base κ F (oneJointUnionObject hPch hQch hPQ hU) := by
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  have hcP : cj ∈ P.atoms := hPl ▸ hPB0.2.2.1
  have hcQ : cj ∈ Q.atoms := hQu ▸ hQB0.2.1
  have hUsub : P.atoms ∪ Q.atoms ⊆ C.atoms := by
    rcases hPC with hPC | hQC0
    · refine union_subset hPC ?_
      by_contra hQC
      have hCQ : ¬ C.atoms ⊆ Q.atoms := by
        intro hsub
        have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, hsub (hPC hPB0.2.1)⟩
        rw [hPQ] at hu
        exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
      exact object_hyper_overlap_nested hM Q C hCh ⟨cj, mem_inter.mpr ⟨hcQ, hPC hcP⟩⟩ hQC hCQ
    · refine union_subset ?_ hQC0
      by_contra hPC'
      have hCP : ¬ C.atoms ⊆ P.atoms := by
        intro hsub
        have hu : Q.lower ∈ P.atoms ∩ Q.atoms :=
          mem_inter.mpr ⟨hsub (hQC0 hQB0.2.2.1), hQB0.2.2.1⟩
        rw [hPQ] at hu
        exact hQB0.2.2.2.1 (hQu.trans (mem_singleton.mp hu).symm)
      exact object_hyper_overlap_nested hM P C hCh ⟨cj, mem_inter.mpr ⟨hcP, hQC0 hcQ⟩⟩ hPC' hCP
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  exact ⟨oneJointUnionObject_hasGapKind hPch hQch hPQ hU ⟨rP, hrP, hkP⟩,
    Or.inl ⟨C, hUsub, hCk, hCF⟩⟩

theorem one_joint_union_contradiction_hyper_container {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)}
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q C : Object G.molecule} (hPm : P ∈ collection) {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hCh : ∃ R, C.shape = .hyper R)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG)
    (hCF : Disjoint (↑C.atoms : Set (GBranch G.tree)) F)
    (hPC : P.atoms ⊆ C.atoms ∨ Q.atoms ⊆ C.atoms)
    (hCk : C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) : False := by
  have hQB0 := object_vc_block Q hQvc
  have hPB0 := object_vc_block P hPvc
  have hUel := union_eligible_of_hyper_container G hM hPvc hQvc hCh hPl hQu hPch hQch hPQ hU
    hPsg hCF hPC hCk
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
