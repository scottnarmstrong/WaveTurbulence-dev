/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceUnionContradiction`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 One-joint block union of two selected ordinary objects, one of which lies in an ordinary
LG/ZG container: the union is eligible, non-omitted, and strictly bigger: contradiction. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

/-- The union of two ordinary chain objects at one joint is never an omitted atom set
(an omitted set is the atom set of a single type-V vine, whose interior atoms are non-cut). -/
theorem union_not_omitted {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P Q : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hP : G.molecule.IsBlock P a c) (hQ : G.molecule.IsBlock Q c b) (hPQ : P ∩ Q = {c})
    (hU : G.molecule.IsBlock (P ∪ Q) a b) : P ∪ Q ∉ omitted := by
  intro ho
  obtain ⟨D, _, _, _, hS⟩ := hc.1 _ ho
  have hne := block_union_erase_not_connected hP hQ hPQ hU
  rcases hS with h | h
  · exact hne (by rw [h]; exact Src.IsSomeVine.erase_connected D.first_vine c)
  · exact hne (by rw [h]; exact Src.IsSomeVine.erase_connected D.second_vine c)

theorem union_eligible_of_vc_container {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)}
    {P Q C : Src.Object Src.γL G.molecule} {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h) (hCvc : ∃ h, C.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Src.Chain Src.γL G.molecule P.atoms P.upper cj n) (hQch : Src.Chain Src.γL G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (hQsg : Q.HasGapKind L γ η base κ .SG)
    (hCF : Disjoint (↑C.atoms : Set (GBranch G.tree)) F)
    (hPC : P.atoms ⊆ C.atoms ∨ Q.atoms ⊆ C.atoms)
    (hCk : C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) :
    Src.eligibleSecondObject Src.γL G L γ η base κ F (oneJointUnionObject hPch hQch hPQ hU) := by
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  have hCB := object_vc_block C hCvc
  have hPB := hPB0
  have hQB := hQB0
  rw [hPl] at hPB
  rw [hQu] at hQB
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  obtain ⟨rQ, hrQ, hkQ⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η base κ .SG).mp hQsg
  obtain ⟨rC, hrC, hkC⟩ : ∃ rC, G.molecule.IsBlockGap L base κ C.atoms C.upper rC ∧
      (Molecule.gapKind L γ η rC = .LG ∨ Molecule.gapKind L γ η rC = .ZG) := by
    rcases hCk with h | h
    · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff C hCvc L γ η base κ .LG).mp h
      exact ⟨r, hr, Or.inl hk⟩
    · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff C hCvc L γ η base κ .ZG).mp h
      exact ⟨r, hr, Or.inr hk⟩
  have hcP : cj ∈ P.atoms := hPl ▸ hPB0.2.2.1
  have hcQ : cj ∈ Q.atoms := hQu ▸ hQB0.2.1
  have hUsub : P.atoms ∪ Q.atoms ⊆ C.atoms := by
    rcases hPC with hPC | hQC0
    · have habs := Vine.SG_block_outer_joints_absent G.molecule hM hCB hPB0 hPC L γ η base c0 κ
        hκ hc0 hrC hrP hkC hkP
      have hcCj : cj ≠ C.upper ∧ cj ≠ C.lower :=
        ⟨fun h => habs.1 (h ▸ hcP), fun h => habs.2 (h ▸ hcP)⟩
      have hCQ : ¬ C.atoms ⊆ Q.atoms := by
        intro hsub
        have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, hsub (hPC hPB0.2.1)⟩
        rw [hPQ] at hu
        exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
      have hrQ' : G.molecule.IsBlockGap L base κ Q.atoms cj rQ := hQu ▸ hrQ
      exact union_subset hPC (sg_block_absorbed_by_container hM L γ η base c0 κ hκ hc0 Q C hQB0
        hCB hcQ (Or.inl hQu.symm) (hPC hcP) hcCj hrQ' hkQ hrC hkC hCQ)
    · have habs := Vine.SG_block_outer_joints_absent G.molecule hM hCB hQB0 hQC0 L γ η base c0 κ
        hκ hc0 hrC hrQ hkC hkQ
      have hcCj : cj ≠ C.upper ∧ cj ≠ C.lower :=
        ⟨fun h => habs.1 (h ▸ hcQ), fun h => habs.2 (h ▸ hcQ)⟩
      have hCP : ¬ C.atoms ⊆ P.atoms := by
        intro hsub
        have hu : Q.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hsub (hQC0 hQB0.2.2.1), hQB0.2.2.1⟩
        rw [hPQ] at hu
        exact hQB0.2.2.2.1 (hQu.trans (mem_singleton.mp hu).symm)
      have hκ1 : ∀ x, κ (G.molecule.mate x) = κ x := hκ.1
      have hcons : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
          ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base κ x = 0 :=
        fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
      obtain ⟨rP', hrP', hkP'⟩ := source_block_lower_SG_gap G.molecule hM hPB0 L γ η base κ hκ1
        hcons hrP hkP
      have hrP'' : G.molecule.IsBlockGap L base κ P.atoms cj rP' := hPl ▸ hrP'
      have hPC' := sg_block_absorbed_by_container hM L γ η base c0 κ hκ hc0 P C hPB0 hCB hcP
        (Or.inr hPl.symm) (hQC0 hcQ) hcCj hrP'' hkP' hrC hkC hCP
      exact union_subset hPC' hQC0
  exact ⟨oneJointUnionObject_hasGapKind hPch hQch hPQ hU ⟨rP, hrP, hkP⟩, Or.inl ⟨C, hUsub, hCk, hCF⟩⟩

theorem one_joint_union_contradiction_vc_container {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P Q C : Src.Object Src.γL G.molecule} (hPm : P ∈ collection) {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h) (hCvc : ∃ h, C.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Src.Chain Src.γL G.molecule P.atoms P.upper cj n) (hQch : Src.Chain Src.γL G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (hQsg : Q.HasGapKind L γ η base κ .SG)
    (hCF : Disjoint (↑C.atoms : Set (GBranch G.tree)) F)
    (hPC : P.atoms ⊆ C.atoms ∨ Q.atoms ⊆ C.atoms)
    (hCk : C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) : False := by
  have hQB0 := object_vc_block Q hQvc
  have hPB0 := object_vc_block P hPvc
  have hUel := union_eligible_of_vc_container G hM hκ hc0 hPvc hQvc hCvc hPl hQu hPch hQch hPQ hU
    hPsg hQsg hCF hPC hCk
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

end WaveTurbulence.GammaLow.FinalCount.H
