/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.Spine.SourceHyperDesignation
/-! The one-joint union of two selected ordinary objects is never a hyper-block either. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceHyperBlockFalse` (sha256 3b0e86b9439d68ddeb4f1302e9eb768ed5b4603cda80b5a4c9201b1b7fcc90c4) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isContained_of_vc_left (P U : Object γv M) (hP : ∃ h, P.shape = .vc h)
    (hsub : P.atoms ⊆ U.atoms) : P.IsContained U := by
  obtain ⟨hh, hs⟩ := hP
  rcases P with ⟨A, x, y, Psh⟩
  rcases U with ⟨S, a, b, Ush⟩
  cases Psh with
  | vc h' => cases Ush <;> exact hsub
  | hyper R => cases hs

theorem isContained_of_vc_right (P U : Object γv M) (hU : ∃ h, U.shape = .vc h)
    (hsub : P.atoms ⊆ U.atoms) : P.IsContained U := by
  obtain ⟨hh, hs⟩ := hU
  rcases P with ⟨A, x, y, Psh⟩
  rcases U with ⟨S, a, b, Ush⟩
  cases Ush with
  | vc h' => cases Psh <;> exact hsub
  | hyper R => cases hs

theorem one_joint_hyperblock_false (hfam : FamFacts γv) {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object γv G.molecule)}
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    {P Q : Object γv G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain γv G.molecule P.atoms P.upper cj n) (hQch : Chain γv G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj})
    (hH : Mole.IsHyperBlock G.molecule (P.atoms ∪ Q.atoms) P.upper Q.lower) : False := by
  obtain ⟨hPsg, hPel⟩ := ((hc.2.2 P).mp hPm).1
  obtain ⟨hQsg, _⟩ := ((hc.2.2 Q).mp hQm).1
  have hQF := eligible_atoms_disjoint ((hc.2.2 Q).mp hQm).1
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  obtain ⟨U, hUat, hUu, hUl, ⟨RU, hUsh, hUends, hUB⟩, hUgap⟩ :=
    hyper_union_object hPl hQu hPch hQch hPQ hPB0 hQB0 hH
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  have hUsg : U.HasGapKind L γ η base κ .SG := hUgap L γ η base κ .SG ⟨rP, hrP, hkP⟩
  have hbP : Q.lower ∉ P.atoms := by
    intro h
    have : Q.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h, hQB0.2.2.1⟩
    rw [hPQ] at this
    exact hQB0.2.2.2.1 (hQu.trans (mem_singleton.mp this).symm)
  have hUel : eligibleSecondObject γv G L γ η base κ F U := by
    refine ⟨hUsg, ?_⟩
    rcases one_joint_union_contained hfam G hM hκ hc0 hPvc hQvc hPl hQu hPQ hPsg hQsg hQF hPel with
      ⟨C, hCk, hsub, hCvc, hCF⟩ | ⟨C, hCk, hsub, ⟨RC, hCsh⟩, hCF⟩ | ⟨D, hD, hDF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inr ⟨D, hUat ▸ hD, hDF⟩
  have hUo : U.atoms ∉ omitted := by
    intro ho
    obtain ⟨D, _, _, _, hS⟩ := hc.1 _ ho
    have hdeg := (Mole.hyperBlock_degrees G.molecule ⟨RU.added, hUends, hUB⟩).1
    have hUa : P.upper ∈ P.atoms ∪ Q.atoms := mem_union_left _ hPB0.2.1
    have hvine : ∀ {S : Finset (GBranch G.tree)} {x y : GBranch G.tree},
        IsSomeVine γv G.molecule S x y → U.atoms = S → False := by
      intro S x y hV hS
      rw [hUat] at hS
      rw [hS] at hdeg hUa
      obtain ⟨_, _, _, _, _, _, _, _, hint⟩ := isBlock_of_isSomeVine hV
      by_cases h1 : P.upper = x
      · have := (Mole.block_joint_degrees G.molecule (isBlock_of_isSomeVine hV)).1
        rw [← h1] at this; omega
      · by_cases h2 : P.upper = y
        · have := (Mole.block_joint_degrees G.molecule (isBlock_of_isSomeVine hV)).2
          rw [← h2] at this; omega
        · have := hint.1 _ hUa h1 h2
          omega
    rcases hS with h | h
    · exact hvine D.first_vine h
    · exact hvine D.second_vine h
  have hcont := ((hc.2.2 P).mp hPm).2.2 U hUel hUo (isContained_of_vc_left P U hPvc (hUat ▸ subset_union_left))
  have hsub : U.atoms ⊆ P.atoms := Object.contained_atoms_subset U P hcont
  have hl : Q.lower ∈ P.atoms ∩ Q.atoms :=
    mem_inter.mpr ⟨hsub (hUat ▸ mem_union_right _ hQB0.2.2.1), hQB0.2.2.1⟩
  rw [hPQ] at hl
  exact hQB0.2.2.2.1 ((hQu.trans (mem_singleton.mp hl).symm))

end WaveTurbulence.GammaLow.Famc
