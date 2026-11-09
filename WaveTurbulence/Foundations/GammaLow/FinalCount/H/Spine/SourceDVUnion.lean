/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceDVUnion`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Union eligibility when the first object lies in a double vine (any position of the second). 

**Low-range change (L6-HDS).** The double vines are DV′s of the low family (`Src.DoubleVine`: `σ = 1`, two members
of `𝒱_{γL}`; main: two vines (V)); only their blocks, `σ = 1` and the degree profile (`DS.dv_degree_profile`) are used.
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

theorem union_eligible_of_dv_container {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)}
    {P Q : Src.Object Src.γL G.molecule} {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Src.Chain Src.γL G.molecule P.atoms P.upper cj n) (hQch : Src.Chain Src.γL G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hPsg : P.HasGapKind L γ η base κ .SG) (D : Src.DoubleVine Src.γL G)
    (hPD : P.atoms ⊆ D.first ∪ D.second)
    (hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F)
    (hQF : Disjoint (↑Q.atoms : Set (GBranch G.tree)) F) :
    Src.eligibleSecondObject Src.γL G L γ η base κ F (oneJointUnionObject hPch hQch hPQ hU) := by
  by_cases hQW : Q.atoms ⊆ D.first ∪ D.second
  · exact union_eligible_of_dv_subset G hPvc hPch hQch hPQ hU hPsg D (union_subset hPD hQW) hDF
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  have hcP : cj ∈ P.atoms := hPl ▸ hPB0.2.2.1
  have hcQ : cj ∈ Q.atoms := hQu ▸ hQB0.2.1
  have hdeg := DS.dv_degree_profile hM D.sigma_one D.first_vine.block D.second_vine.block D.overlap
  have huv : D.upper ≠ D.lower := D.first_vine.block.2.2.2.1
  obtain ⟨nQ, hQch0⟩ := object_vc_chain Q hQvc
  have hconn := chain_connected hQch0.toVine
  have hex := dv_exit_contains_joints G.molecule hM huv hdeg.1 hdeg.2.1 hdeg.2.2 hQB0 hconn hQW
    ⟨cj, mem_inter.mpr ⟨hQu ▸ hQB0.2.1, hPD hcP⟩⟩
  have hmiss : ¬(D.upper ∈ P.atoms ∧ D.lower ∈ P.atoms) := by
    rintro ⟨h1, h2⟩
    have a1 : D.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h1, hex.1⟩
    have a2 : D.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h2, hex.2⟩
    rw [hPQ] at a1 a2
    exact huv ((mem_singleton.mp a1).trans (mem_singleton.mp a2).symm)
  obtain ⟨hh, _⟩ := hPvc
  have hbr : ∃ A0, Src.IsSomeVine Src.γL G.molecule A0 D.upper D.lower ∧ P.atoms ⊆ A0 ∧ A0 ⊆ D.first ∪ D.second := by
    rcases VC_in_DV_missing_joint_side G.molecule hM D.sigma_one D.first_vine D.second_vine D.overlap hh.toVine
      hPD hmiss with h | h
    · exact ⟨D.first, D.first_vine, h, subset_union_left⟩
    · exact ⟨D.second, D.second_vine, h, subset_union_right⟩
  obtain ⟨A0, hA0, hPA, hA0W⟩ := hbr
  have hQA : ¬ Q.atoms ⊆ A0 := fun h => hQW (h.trans hA0W)
  have hAQ : ¬ A0 ⊆ Q.atoms := by
    intro h
    have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, h (hPA hPB0.2.1)⟩
    rw [hPQ] at hu
    exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
  obtain ⟨D'', h1, h2⟩ := dv_branch_double_vine G hM D.sigma_one hA0 hQvc hex.1 hex.2 hQA hAQ (hPA hcP) hcQ
  exact union_eligible_of_dv_subset G ⟨hh, ‹_›⟩ hPch hQch hPQ hU hPsg D''
    (by rw [h1, h2]; exact union_subset (hPA.trans subset_union_left) subset_union_right)
    (by rw [h1, h2]; exact disjointF_union (disjointF_of_subset hA0W hDF) hQF)

end WaveTurbulence.GammaLow.FinalCount.H
