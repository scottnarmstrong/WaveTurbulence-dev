/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsMain
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourcePairsMain
public import WaveTurbulence.Foundations.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDef
/-! R6(a): pair compatibility and covering for the canonical part of the second collection. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceCanonicalDesignation` (sha256 9e485177a1741eab8aff77a3d5fb156a8b9cf538cf9139d97e8e57e9eca6af44) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem hyper_bond_eq_of_rank_eq {M : Molecule V D} (rk : D → ℕ) (hrk : Function.Injective rk)
    {P Q : Object γv M} {R : HyperLikeRealization γv M P.atoms P.upper P.lower}
    {R' : HyperLikeRealization γv M Q.atoms Q.upper Q.lower}
    (hP : P.shape = .hyper R) (hQ : Q.shape = .hyper R')
    (h : P.hyperRank rk = Q.hyperRank rk) :
    R'.added = R.added ∨ R'.added = M.mate R.added := by
  unfold Object.hyperRank at h
  rw [hP, hQ] at h
  simp only at h
  have hm : ∀ x, M.mate (M.mate x) = x := M.mate_mate
  rcases min_choice (rk R.added) (rk (M.mate R.added)) with h1 | h1 <;>
    rcases min_choice (rk R'.added) (rk (M.mate R'.added)) with h2 | h2 <;>
    rw [h1, h2] at h
  · exact Or.inl (hrk h).symm
  · right
    have := hrk h
    rw [this, hm]
  · right
    exact (hrk h).symm
  · left
    have := hrk h
    have := congrArg M.mate this
    rw [hm, hm] at this
    exact this.symm

/-- R6(a): with one canonical designation per atom set, two members of the second collection
sharing a joint use the same dart pair there; the exceptional disjunct of
`source_second_collection_pairs_compatible` is gone. -/
theorem canonical_second_collection_pairs_compatible (hfam : FamFacts γv) {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Object γv G.molecule)}
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    (rk : GardenDart G → ℕ) (hrk : Function.Injective rk)
    {P Q : Object γv G.molecule} (hPm : P ∈ canonicalSub rk collection)
    (hQm : Q ∈ canonicalSub rk collection)
    {v : GBranch G.tree} (hvP : v = P.upper ∨ v = P.lower) (hvQ : v = Q.upper ∨ v = Q.lower)
    {x y x' y' : GardenDart G}
    (hxy : SourceObjectJointPair P v x y) (hxy' : SourceObjectJointPair Q v x' y') :
    x = x' ∧ y = y' := by
  rcases source_second_collection_pairs_compatible hfam G hM hκ hc0 hc hPm.1 hQm.1 hvP hvQ hxy hxy'
    with h | ⟨hat, ⟨R, hR⟩, ⟨R', hR'⟩⟩
  · exact h
  · have h1 := hPm.2 Q hQm.1 hat.symm ⟨R, hR⟩ ⟨R', hR'⟩
    have h2 := hQm.2 P hPm.1 hat ⟨R', hR'⟩ ⟨R, hR⟩
    have hb := hyper_bond_eq_of_rank_eq rk hrk hR hR' (le_antisymm h1 h2)
    have hconv : ∀ z, Q.ContainsDart z → P.ContainsDart z := by
      intro z hz
      unfold Object.ContainsDart at hz ⊢
      rw [hR'] at hz
      rw [hR]
      simp only at hz ⊢
      obtain ⟨a1, a2, a3⟩ := hz
      refine ⟨?_, ?_, hat ▸ a3⟩
      · rcases hb with e | e
        · rw [← e]; exact a1
        · intro hz'; apply a2; rw [e, G.molecule.mate_mate]; exact hz'
      · rcases hb with e | e
        · rw [← e]; exact a2
        · rw [← e]; exact a1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hxy'
    exact source_object_joint_pair_unique P hvP hxy ⟨b1, b2, hconv _ b3, hconv _ b4, b5, b6⟩

end WaveTurbulence.GammaLow.Famc
