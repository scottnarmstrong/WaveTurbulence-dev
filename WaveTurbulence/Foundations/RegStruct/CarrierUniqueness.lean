/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-! # Each code determines one actual garden carrier

This is uniqueness of the carrier for a fixed code. The converse, uniqueness
of well-formed codes for a source regular garden, is a separate structure theorem.
-/

public section
namespace WaveTurbulence.Reg

/-- The declared decoding relation determines all garden data for any fixed code. -/
theorem carrier_unique {Q : RegCpl} {G H : Garden 2} (hG : Q.Decodes G) (hH : Q.Decodes H) :
    G = H := by
  obtain ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩ := G
  obtain ⟨hs,ht,hp,hm,hpp,heq,hsgn⟩ := H
  obtain ⟨⟨gplain,gsig⟩,g0,g1,gPairs⟩ := hG
  obtain ⟨⟨hplain,hSigMatch⟩,h0,h1,hPairs⟩ := hH
  have htree : gt = ht := by
    funext j
    fin_cases j
    · exact g0.trans h0.symm
    · exact g1.trans h1.symm
  subst ht
  have hsig : gs = hs := gsig.trans hSigMatch.symm
  subst hs
  have hpair : gp = hp := by
    funext ℓ
    apply Subtype.ext
    exact decodedPair_functional Q (gPairs ℓ) (hPairs ℓ)
  have hmark : gm = hm := by
    funext ℓ
    exact (gplain ℓ).trans (hplain ℓ).symm
  cases hpair
  cases hmark
  rfl

/-- The constructed carrier is the unique garden decoded by the given code. -/
theorem decodedCouple_unique (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G) :
    G = decodedCouple Q := carrier_unique hG (decodedCouple_decodes Q)

end WaveTurbulence.Reg
