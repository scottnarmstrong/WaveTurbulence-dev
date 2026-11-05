/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SourcePairTransport

/-! # Literal oriented pair inclusion determines the surviving involution -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg.Skeleton

/-- The componentwise action on literal oriented leaf-pair addresses. -/
@[expose] def mapPairAddresses {w v : ℕ} (f : Address v → Address w) (q : Pair v) : Pair w :=
  (f q.1, f q.2)

/-- For ordinary gardens, sign-compatible inclusion of all old pair addresses
forces the actual surviving partner map. Extra pairs in the larger garden
cannot alter any of these surviving pairs. -/
theorem pairEmbedding_of_sourcePairs {w v : ℕ} (G : Garden w) (H : Garden v)
    (hG : G.IsPlain) (hH : H.IsPlain) (E : GLeaf H.tree → GLeaf G.tree)
    (f : Address v → Address w) (hval : ∀ l, (E l).1 = f l.1)
    (hsign : ∀ l, nodeSign G.sig (E l).1 = nodeSign H.sig l.1)
    (hpairs : ∀ q ∈ sourcePairs H, mapPairAddresses f q ∈ sourcePairs G)
    (l : GLeaf H.tree) : G.pair (E l) = E (H.pair l) := by
  have hm := hpairs (sourcePairAt H l) (sourcePairAt_mem H hH l)
  have hend : (mapPairAddresses f (sourcePairAt H l)).1 = (E l).1 ∨
      (mapPairAddresses f (sourcePairAt H l)).2 = (E l).1 := by
    rcases sourcePairAt_endpoint H l with he | he
    · exact Or.inl ((congrArg f he).trans (hval l).symm)
    · exact Or.inr ((congrArg f he).trans (hval l).symm)
  have he := sourcePairs_eq_at G hG _ hm (E l) hend
  apply Subtype.ext
  by_cases hs : nodeSign H.sig l.1 = 1
  · have hsG : nodeSign G.sig (E l).1 = 1 := (hsign l).trans hs
    simp only [mapPairAddresses, sourcePairAt, hs, hsG, ite_true] at he
    exact (congrArg Prod.snd he).symm.trans (hval (H.pair l)).symm
  · have hsG : nodeSign G.sig (E l).1 ≠ 1 := fun ht => hs ((hsign l).symm.trans ht)
    simp only [mapPairAddresses, sourcePairAt, hs, hsG, ite_false] at he
    exact (congrArg Prod.fst he).symm.trans (hval (H.pair l)).symm

end WaveTurbulence.LFTwist
