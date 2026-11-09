/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
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
public import WaveTurbulence.Foundations.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
/-! Two selected ordinary objects with the same joints meeting exactly in the joints and not
nested cannot both be selected: they share a joint bond, are both type-V vines, hence form a
double vine one of whose constituents is omitted. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceDiamondContradiction` (sha256 fcd1a020fb3c3016681b1f8cef2d0db5275f2397f2d9a8768b8b548c65d43ee0) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

theorem object_vc_chain {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : Object γv M) (h : ∃ h, O.shape = .vc h) :
    ∃ n, Chain γv M O.atoms O.upper O.lower n := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact h'.2
  | hyper R => cases hs


theorem ordinary_diamond_false {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object γv G.molecule)}
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    {P Q : Object γv G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPQ : P.atoms ∩ Q.atoms = {P.upper, P.lower})
    (hQj : (Q.upper = P.upper ∧ Q.lower = P.lower) ∨ (Q.upper = P.lower ∧ Q.lower = P.upper))
    (hnest : ¬ P.atoms ⊆ Q.atoms) (hnest' : ¬ Q.atoms ⊆ P.atoms)
    (hPsg : P.HasGapKind L γ η base κ .SG) (hQsg : Q.HasGapKind L γ η base κ .SG) : False := by
  have hPB := object_vc_block P hPvc
  have hQB := object_vc_block Q hQvc
  have hQB' : G.molecule.IsBlock Q.atoms P.upper P.lower := by
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hQB
    · rw [← h1, ← h2]; exact Mole.block_swap_joints _ hQB
  obtain ⟨z, hza, hzb, hzP, hzQ⟩ := diamond_shared_bond hM hPB hQB' hPQ
  have haQ : P.upper ∈ Q.atoms := by
    have : P.upper ∈ P.atoms ∩ Q.atoms := by rw [hPQ]; simp
    exact (mem_inter.mp this).2
  have hbQ : P.lower ∈ Q.atoms := by
    have : P.lower ∈ P.atoms ∩ Q.atoms := by rw [hPQ]; simp
    exact (mem_inter.mp this).2
  have haP : P.upper ∈ P.atoms := hPB.2.1
  have hbP : P.lower ∈ P.atoms := hPB.2.2.1
  obtain ⟨nP, hPch⟩ := object_vc_chain P hPvc
  obtain ⟨nQ, hQch⟩ := object_vc_chain Q hQvc
  have hQch' : Chain γv G.molecule Q.atoms P.upper P.lower nQ := by
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hQch
    · rw [← h1, ← h2]; exact chain_swap hQch
  have hXP := chain_single_of_joint_bond hM hPch hPB hza hzb hzP
  have hXQ := chain_single_of_joint_bond hM hQch' hQB' hza hzb hzQ
  have hPnI : ¬ G.molecule.IsVine .I P.atoms P.upper P.lower := by
    intro hI
    apply hnest
    rw [Vine.typeI_atoms hI]
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact haQ
    · rw [mem_singleton.mp hv]; exact hbQ
  have hσ : G.molecule.sigma P.upper P.lower = 1 :=
    le_antisymm (isSomeVine_sigma_le_one hXP hPnI) (bondsBetween_pos_of_dart hza hzb)
  let D : DoubleVine γv G := ⟨P.atoms, Q.atoms, P.upper, P.lower, hσ, hXP, hXQ, hPQ⟩
  have hκ1 : ∀ x, κ (G.molecule.mate x) = κ x := hκ.1
  have hcons : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base κ x = 0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  obtain ⟨rQ, hrQ, hkQ⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η base κ .SG).mp hQsg
  have h1 : (Object.ofVine D.first_vine).HasGapKind L γ η base κ .SG :=
    (object_vc_hasGapKind_iff _ ⟨_, rfl⟩ L γ η base κ .SG).mpr ⟨rP, hrP, hkP⟩
  have h2 : (Object.ofVine D.second_vine).HasGapKind L γ η base κ .SG := by
    refine (object_vc_hasGapKind_iff _ ⟨_, rfl⟩ L γ η base κ .SG).mpr ?_
    rcases hQj with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨rQ, by show G.molecule.IsBlockGap L base κ Q.atoms P.upper rQ; rw [← e1]; exact hrQ, hkQ⟩
    · obtain ⟨r', hr', hk'⟩ := source_block_lower_SG_gap G.molecule hM hQB L γ η base κ hκ1 hcons
        hrQ hkQ
      exact ⟨r', by show G.molecule.IsBlockGap L base κ Q.atoms P.upper r'; rw [← e2]; exact hr', hk'⟩
  have hPo := ((hc.2.2 P).mp hPm).2.1
  have hQo := ((hc.2.2 Q).mp hQm).2.1
  have hDF : Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F :=
    disjointF_union (eligible_atoms_disjoint ((hc.2.2 P).mp hPm).1)
      (eligible_atoms_disjoint ((hc.2.2 Q).mp hQm).1)
  rcases hc.2.1 D hDF h1 h2 with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact hPo h
  · exact hQo h

end WaveTurbulence.GammaLow.Famc
