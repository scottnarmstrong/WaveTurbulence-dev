/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Region
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors

/-! # Regional leaf pairs under a unit twist (V5 Step 4b, R31(2), `n_(2)`)

For the actual unit twist `(G, P)` and an atom set `S`, an ordinary leaf pair (neither leaf is the retained leaf or its
partner) is regional (its LP bond is internal to `S`) iff its image under the pair bijection is regional for
`twistedAtoms S` (`regional_iff`).  The exceptional pair is regional on both sides when the designated placement sits
in the atom set (`exceptional_internal`, `exceptional_internal_twisted`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

theorem ordinary_internal_iff {S : Finset (GBranch G.tree)} (l : GLeaf G.tree) (hl : l ≠ P.retained)
    (hp : l ≠ G.pair P.retained) :
    Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P l) ↔
      Mole.IsInternalLeaf G S l := by
  constructor
  · rintro ⟨hm', hn', hp', hg'⟩
    have hm : G.mark l = none := by rwa [unitTwistGarden_mark] at hm'
    have hn : l.1.2 ≠ [] := (coreLeafEquiv_nonroot G P l).mp hn'
    have hp2 : (G.pair l).1.2 ≠ [] := by
      have h : ((unitTwistGarden G P).pair (coreLeafEquiv G P l)).1.2 ≠ [] := hp'
      rw [unitTwistGarden_pair] at h
      exact (coreLeafEquiv_nonroot G P _).mp h
    refine ⟨hm, hn, hp2, ?_⟩
    have hx : twistDartEquiv G P (.inr ⟨l, hm, hn, hp2⟩ : GardenDart G) =
        (.inr ⟨coreLeafEquiv G P l, hm', hn', hp'⟩ : GardenDart (unitTwistGarden G P)) := by
      change naiveDartEquiv G P (exceptionalDartSwap G P _) = _
      rw [exceptionalDartSwap_otherLP G P ⟨l, hm, hn, hp2⟩ hl hp]
      rfl
    exact (inGroup_twistedAtoms G P S _).mp (hx ▸ hg')
  · rintro ⟨hm, hn, hp2, hg⟩
    have hm' : (unitTwistGarden G P).mark (coreLeafEquiv G P l) = none := by rwa [unitTwistGarden_mark]
    have hn' : (coreLeafEquiv G P l).1.2 ≠ [] := (coreLeafEquiv_nonroot G P l).mpr hn
    have hp' : ((unitTwistGarden G P).pair (coreLeafEquiv G P l)).1.2 ≠ [] := by
      rw [unitTwistGarden_pair]
      exact (coreLeafEquiv_nonroot G P _).mpr hp2
    refine ⟨hm', hn', hp', ?_⟩
    have hx : twistDartEquiv G P (.inr ⟨l, hm, hn, hp2⟩ : GardenDart G) =
        (.inr ⟨coreLeafEquiv G P l, hm', hn', hp'⟩ : GardenDart (unitTwistGarden G P)) := by
      change naiveDartEquiv G P (exceptionalDartSwap G P _) = _
      rw [exceptionalDartSwap_otherLP G P ⟨l, hm, hn, hp2⟩ hl hp]
      rfl
    exact hx ▸ (inGroup_twistedAtoms G P S _).mpr hg

theorem mem_clRegionalPairs {hG : G.IsPlain} {U : Finset (GBranch G.tree)} {q : SourcePair G} :
    q ∈ clRegionalPairs hG U ↔ Mole.IsInternalLeaf G U (q.firstLeaf hG) := by
  classical
  unfold clRegionalPairs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A pair is regional iff its image under any representative leaf is. -/
theorem mem_clRegionalPairs_of_leaf {hG : G.IsPlain} {U : Finset (GBranch G.tree)} (l : GLeaf G.tree) :
    pairOfLeaf G hG l ∈ clRegionalPairs hG U ↔ Mole.IsInternalLeaf G U l := by
  rw [mem_clRegionalPairs]
  rcases pairOfLeaf_first_or_partner G hG l with h | h
  · rw [h]
  · rw [h]
    exact Mole.internal_leaf_pair_iff G U l

/-! ## The exceptional pair is regional -/

/-! ## Order bookkeeping -/

variable {G P}

end WaveTurbulence.VineEstS4
