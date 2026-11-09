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
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperBlockFalse
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
public import WaveTurbulence.Foundations.Spine.SourceHyperBlockFalse
/-! Reversing the orientation of a selected ordinary object keeps it in the second collection:
an SG gap at one joint of a block is SG at the other, and eligibility, omission and maximality
depend only on the atom set for ordinary objects. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceSwapObject` (sha256 bd13d6ba7df43c88b54d776616394453834d606de60102b6f4ca8ca8eaff8822) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

/-- The ordinary object with joints exchanged. -/
@[expose] noncomputable def swapVC {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (P : Object γv M) (hP : ∃ h, P.shape = .vc h) : Object γv M :=
  ⟨P.atoms, P.lower, P.upper, .vc ⟨Mole.block_swap_joints M (object_vc_block P hP),
    (object_vc_chain P hP).choose, chain_swap (object_vc_chain P hP).choose_spec⟩⟩

theorem swapVC_atoms {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (P : Object γv M) (hP : ∃ h, P.shape = .vc h) :
    (swapVC P hP).atoms = P.atoms ∧ (swapVC P hP).upper = P.lower ∧ (swapVC P hP).lower = P.upper ∧
      ∃ h, (swapVC P hP).shape = .vc h := ⟨rfl, rfl, rfl, _, rfl⟩

theorem swapVC_mem {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object γv G.molecule)}
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    {P : Object γv G.molecule} (hPm : P ∈ collection) (hPvc : ∃ h, P.shape = .vc h) :
    swapVC P hPvc ∈ collection := by
  obtain ⟨⟨hPsg, hPel⟩, hPo, hPmax⟩ := (hc.2.2 P).mp hPm
  have hPB := object_vc_block P hPvc
  have hκ1 : ∀ x, κ (G.molecule.mate x) = κ x := hκ.1
  have hcons : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base κ x = 0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  obtain ⟨r', hr', hk'⟩ := source_block_lower_SG_gap G.molecule hM hPB L γ η base κ hκ1 hcons
    hrP hkP
  have hsw := swapVC_atoms P hPvc
  refine (hc.2.2 _).mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact (object_vc_hasGapKind_iff _ hsw.2.2.2 L γ η base κ .SG).mpr ⟨r', hr', hk'⟩
  · rcases hPel with ⟨C, hPC, hCk⟩ | ⟨D, hD⟩
    · exact Or.inl ⟨C, hsw.1 ▸ hPC, hCk⟩
    · exact Or.inr ⟨D, hsw.1 ▸ hD⟩
  · exact hsw.1 ▸ hPo
  · intro Q hQel hQo hcont
    have h1 : P.IsContained Q := isContained_of_vc_left P Q hPvc
      (hsw.1 ▸ Object.contained_atoms_subset _ Q hcont)
    have h2 := hPmax Q hQel hQo h1
    exact isContained_of_vc_right Q _ hsw.2.2.2 (hsw.1 ▸ Object.contained_atoms_subset Q P h2)

end WaveTurbulence.GammaLow.Famc
