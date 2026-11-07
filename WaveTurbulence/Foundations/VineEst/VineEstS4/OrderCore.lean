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

theorem regional_iff (hG : G.IsPlain) {S : Finset (GBranch G.tree)} (q : SourcePair G)
    (hq : q ≠ pairOfLeaf G hG P.retained) :
    chosenPairEquiv G P hG true q ∈ clRegionalPairs (chosenSkeleton_plain G P hG true) (twistedAtoms G P S) ↔
      q ∈ clRegionalPairs hG S := by
  change pairOfLeaf (chosenSkeleton G P true) (chosenSkeleton_plain G P hG true)
    (coreLeafEquiv G P (q.firstLeaf hG)) ∈ _ ↔ _
  have hl : q.firstLeaf hG ≠ P.retained := by
    intro h
    apply hq
    rw [← pairOfLeaf_firstLeaf G hG q, h]
  have hp : q.firstLeaf hG ≠ G.pair P.retained := by
    intro h
    apply hq
    rw [← pairOfLeaf_firstLeaf G hG q, h, pairOfLeaf_partner]
  have h1 := mem_clRegionalPairs_of_leaf (unitTwistGarden G P) (hG := chosenSkeleton_plain G P hG true)
    (U := twistedAtoms G P S) (coreLeafEquiv G P (q.firstLeaf hG))
  have h2 := mem_clRegionalPairs G (hG := hG) (U := S) (q := q)
  exact h1.trans ((ordinary_internal_iff G P (q.firstLeaf hG) hl hp).trans h2.symm)

/-! ## The exceptional pair is regional -/

theorem exceptional_internal {S U : Finset (GBranch G.tree)} (hP : IsPlacementAt G S P.lower P) (hS : S ⊆ U)
    (hlow : P.lower ∈ U) : Mole.IsInternalLeaf G U P.retained := by
  refine ⟨P.unmarked, retained_nonroot G P, P.paired_nonroot, ?_⟩
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  exact ⟨ha ▸ hlow, hS (placement_paired_parent_mem G P hP)⟩

/-! ## Order bookkeeping -/

/-- `n_(2)` as a function of the region data `(U, a)` and the replacement data. -/
@[expose] noncomputable def localOrder2 (hG : G.IsPlain) (U : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (D : ReconstructionData G) : ℕ :=
  (U.erase a).card + (∑ p ∈ clRegionalPairs hG U, (D.couple p).size) + ∑ v ∈ U.erase a, (D.tree v).size

theorem clLocalOrder2_eq_localOrder2 {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (D : ReconstructionData G)
    (hG : G.IsPlain) (R : CLRegionData G U a b) : clLocalOrder2 D hG R = localOrder2 G hG U a D := rfl

theorem sum_special {α α' : Type*} [DecidableEq α] [DecidableEq α'] (e : α ≃ α') (T : Finset α) (T' : Finset α')
    (hT : ∀ v, e v ∈ T' ↔ v ∈ T) (s : α → ℕ) (s' : α' → ℕ) (z : α) (hz : z ∈ T)
    (hs : ∀ v, v ≠ z → s' (e v) = s v) :
    ∑ v' ∈ T', s' v' + s z = ∑ v ∈ T, s v + s' (e z) := by
  have hT' : T' = T.map e.toEmbedding := by
    apply Finset.ext
    intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    rw [hT v]
    exact (Finset.mem_map_equiv.trans (by rw [Equiv.symm_apply_apply])).symm
  rw [hT', Finset.sum_map]
  have h1 : ∑ v ∈ T, s' (e.toEmbedding v) = s' (e z) + ∑ v ∈ T.erase z, s' (e v) :=
    (Finset.add_sum_erase T (fun v => s' (e v)) hz).symm
  have h2 : ∑ v ∈ T, s v = s z + ∑ v ∈ T.erase z, s v := (Finset.add_sum_erase T s hz).symm
  have h3 : ∑ v ∈ T.erase z, s' (e v) = ∑ v ∈ T.erase z, s v :=
    Finset.sum_congr rfl (fun v hv => hs v (Finset.ne_of_mem_erase hv))
  omega

variable {G P}

/-- Abstract form: two replacement data that agree up to bijections except at the tree at `z` and the couple at `exc`,
with equal combined size there, give the same `n_(2)` over corresponding regions. -/
theorem localOrder2_eq_of {G' : Garden w} (hG : G.IsPlain) (hG' : G'.IsPlain) (e : GBranch G.tree ≃ GBranch G'.tree)
    (g : SourcePair G ≃ SourcePair G') (U : Finset (GBranch G.tree)) (U' : Finset (GBranch G'.tree))
    (a : GBranch G.tree) (hU : ∀ v, e v ∈ U' ↔ v ∈ U)
    (hR : ∀ q, g q ∈ clRegionalPairs hG' U' ↔ q ∈ clRegionalPairs hG U)
    (D : ReconstructionData G) (D' : ReconstructionData G') (z : GBranch G.tree) (hz : z ∈ U.erase a)
    (exc : SourcePair G) (hexc : exc ∈ clRegionalPairs hG U)
    (htree : ∀ v, v ≠ z → D'.tree (e v) = D.tree v) (hcouple : ∀ q, q ≠ exc → D'.couple (g q) = D.couple q)
    (hn : (D'.tree (e z)).size + (D'.couple (g exc)).size = (D.tree z).size + (D.couple exc).size) :
    localOrder2 G' hG' U' (e a) D' = localOrder2 G hG U a D := by
  classical
  have hUe : ∀ v, e v ∈ U'.erase (e a) ↔ v ∈ U.erase a := by
    intro v
    rw [Finset.mem_erase, Finset.mem_erase, hU, e.injective.ne_iff]
  have hcard : (U'.erase (e a)).card = (U.erase a).card := by
    have := sum_special e (U.erase a) (U'.erase (e a)) hUe (fun _ => 1) (fun _ => 1) z hz (fun _ _ => rfl)
    simpa using this
  have htr := sum_special e (U.erase a) (U'.erase (e a)) hUe (fun v => (D.tree v).size)
    (fun v => (D'.tree v).size) z hz (fun v hv => by simp only [htree v hv])
  have hcp := sum_special g (clRegionalPairs hG U) (clRegionalPairs hG' U') hR (fun q => (D.couple q).size)
    (fun q => (D'.couple q).size) exc hexc (fun q hq => by simp only [hcouple q hq])
  unfold localOrder2
  omega

end WaveTurbulence.VineEstS4
