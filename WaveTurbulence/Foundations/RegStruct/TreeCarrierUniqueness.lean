/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceCoupleCount

/-! # Uniqueness of a paired-tree carrier inside fixed couple data -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Exact representation also transports the source tree-to-couple matching relation. -/
theorem RawRep.matchesTreeCouple_iff {Q : RegCpl} {R : RawCpl} (h : RawRep Q R) (G : Garden 1) :
    G.MatchesTreeCouple R ↔ G.MatchesTreeCouple Q.raw := by
  simp only [Garden.MatchesTreeCouple,h.forest,raw_tree_eq_coupleForest]
  constructor
  · rintro ⟨h0,h1,hp⟩
    refine ⟨h0,h1,fun ℓ => ?_⟩
    exact (mem_symmPairs_iff _ _).mpr
      (((mem_symmPairs_iff _ _).mp (hp ℓ)).imp (fun he => h.2.mem_iff.mp he) (fun he => h.2.mem_iff.mp he))
  · rintro ⟨h0,h1,hp⟩
    refine ⟨h0,h1,fun ℓ => ?_⟩
    exact (mem_symmPairs_iff _ _).mpr
      (((mem_symmPairs_iff _ _).mp (hp ℓ)).imp (fun he => h.2.mem_iff.mpr he) (fun he => h.2.mem_iff.mpr he))

/-- On a paired tree, a marked leaf is exactly a lower/lone leaf. -/
theorem pairedTree_mark_iff_lone (G : Garden 1) (hG : IsPairedTree G) (ℓ : GLeaf G.tree) :
    G.mark ℓ ≠ none ↔ G.IsLone ℓ := by
  constructor
  · exact hG.2 ℓ
  · intro h
    rw [Garden.IsLone] at h
    rw [h]
    decide

/-- A paired tree's mark is determined by whether its partner is itself. -/
theorem pairedTree_mark_of_pair (G : Garden 1) (hG : IsPairedTree G) (ℓ : GLeaf G.tree) :
    G.mark ℓ = if G.pair ℓ = ℓ then some MarkTag.lower else none := by
  by_cases hp : G.pair ℓ = ℓ
  · rw [ite_eq_left hp]
    exact (pairedTree_mark_iff_lone G hG ℓ).mp ((G.pair_eq_iff ℓ).mp hp)
  · rw [ite_eq_right hp]
    exact Classical.byContradiction (fun h => hp ((G.pair_eq_iff ℓ).mpr h))

/-- Fixed couple data and a fixed root sign determine at most one paired tree carrier. -/
theorem tree_carrier_unique {Q : RegCpl} {G H : Garden 1}
    (hG : IsPairedTree G) (hH : IsPairedTree H) (hsig : G.sig = H.sig)
    (hGM : G.MatchesTreeCouple Q.raw) (hHM : H.MatchesTreeCouple Q.raw) : G = H := by
  obtain ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩ := G
  obtain ⟨hs,ht,hp,hm,hpp,heq,hsgn⟩ := H
  change gs = hs at hsig
  subst hs
  have htree : gt = ht := by
    funext j
    have h0 := hGM.1.symm.trans hHM.1
    simpa only [Fin.fin_one_eq_zero] using h0
  subst ht
  have hpair : gp = hp := by
    funext ℓ
    have hrel := decodedPair_functional Q (hGM.2.2 ℓ) (hHM.2.2 ℓ)
    change (if gm ℓ = some MarkTag.lower then _ else _) =
      (if hm ℓ = some MarkTag.lower then _ else _) at hrel
    by_cases hg : gm ℓ = some MarkTag.lower <;> by_cases hh : hm ℓ = some MarkTag.lower
    · exact ((geq ℓ).mpr (by rw [hg]; decide)).trans
        ((heq ℓ).mpr (by rw [hh]; decide)).symm
    · simp only [hg,hh,ite_true,ite_false] at hrel
      have he := congrArg Prod.fst hrel
      split_ifs at he <;> norm_num at he
    · simp only [hg,hh,ite_true,ite_false] at hrel
      have he := congrArg Prod.fst hrel
      split_ifs at he <;> norm_num at he
    · simp only [hg,hh,ite_false] at hrel
      apply Subtype.ext
      apply Prod.ext (Subsingleton.elim _ _)
      exact congrArg (fun z : Fin 2 × Path => z.2) hrel
  have hmark : gm = hm := by
    funext ℓ
    have hg := pairedTree_mark_of_pair _ hG ℓ
    have hh := pairedTree_mark_of_pair _ hH ℓ
    change gm ℓ = (if gp ℓ = ℓ then some MarkTag.lower else none) at hg
    change hm ℓ = (if hp ℓ = ℓ then some MarkTag.lower else none) at hh
    rw [hg,hh,hpair]
  cases hpair
  cases hmark
  rfl

end WaveTurbulence.Reg
