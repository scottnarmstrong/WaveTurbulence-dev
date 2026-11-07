/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.LeafCorr

/-! # `OrdCorr` is a partial bijection (LFTWIST-LEAFMAP, step 3) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (h : LFConstruction s ε)

theorem LFConstruction.OrdCorr.functional {x : GLeaf (s.data.forest s.plain)}
    {y y' : GLeaf (h.data.forest (s.chosen_plain ε))} (h1 : h.OrdCorr x y) (h2 : h.OrdCorr x y') :
    y = y' := by
  rcases h1 with ⟨q, hq, ℓ, ℓ', hc, hx, hy⟩ | ⟨b, hb, ℓ, ℓ', hc, hx, hy⟩ <;>
  rcases h2 with ⟨q2, hq2, m, m', hc2, hx2, hy2⟩ | ⟨b2, hb2, m, m', hc2, hx2, hy2⟩
  · have hs := nativeLeafMap_injective s.data s.plain
      (a₁ := ⟨.inl q, ℓ⟩) (a₂ := ⟨.inl q2, m⟩) (hx.trans hx2.symm)
    obtain ⟨hq', hm⟩ := Sigma.mk.inj_iff.mp hs
    have hqq : q = q2 := Sum.inl.inj hq'
    subst hqq
    have hlm : ℓ = m := eq_of_heq hm
    subst hlm
    have : ℓ' = m' := Subtype.ext (hc.symm.trans hc2)
    subst this
    exact hy.symm.trans hy2
  · exact absurd (Sigma.mk.inj_iff.mp (nativeLeafMap_injective s.data s.plain
      (a₁ := ⟨.inl q, ℓ⟩) (a₂ := ⟨.inr b2, m⟩) (hx.trans hx2.symm))).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp (nativeLeafMap_injective s.data s.plain
      (a₁ := ⟨.inr b, ℓ⟩) (a₂ := ⟨.inl q2, m⟩) (hx.trans hx2.symm))).1 (by simp)
  · have hs := nativeLeafMap_injective s.data s.plain
      (a₁ := ⟨.inr b, ℓ⟩) (a₂ := ⟨.inr b2, m⟩) (hx.trans hx2.symm)
    obtain ⟨hq', hm⟩ := Sigma.mk.inj_iff.mp hs
    have hqq : b = b2 := Sum.inr.inj hq'
    subst hqq
    have hlm : ℓ = m := eq_of_heq hm
    subst hlm
    have : ℓ' = m' := Subtype.ext (Subtype.ext (hc.symm.trans hc2))
    subst this
    exact hy.symm.trans hy2

theorem LFConstruction.OrdCorr.injective {x x' : GLeaf (s.data.forest s.plain)}
    {y : GLeaf (h.data.forest (s.chosen_plain ε))} (h1 : h.OrdCorr x y) (h2 : h.OrdCorr x' y) :
    x = x' := by
  rcases h1 with ⟨q, hq, ℓ, ℓ', hc, hx, hy⟩ | ⟨b, hb, ℓ, ℓ', hc, hx, hy⟩ <;>
  rcases h2 with ⟨q2, hq2, m, m', hc2, hx2, hy2⟩ | ⟨b2, hb2, m, m', hc2, hx2, hy2⟩
  · have hs := nativeLeafMap_injective h.data (s.chosen_plain ε)
      (a₁ := ⟨.inl (s.pairs ε q), ℓ'⟩) (a₂ := ⟨.inl (s.pairs ε q2), m'⟩) (hy.trans hy2.symm)
    obtain ⟨hq', hm⟩ := Sigma.mk.inj_iff.mp hs
    have hqq : q = q2 := (s.pairs ε).injective (Sum.inl.inj hq')
    subst hqq
    have hlm : ℓ' = m' := eq_of_heq hm
    subst hlm
    have : ℓ = m := Subtype.ext (hc.trans hc2.symm)
    subst this
    exact hx.symm.trans hx2
  · exact absurd (Sigma.mk.inj_iff.mp (nativeLeafMap_injective h.data (s.chosen_plain ε)
      (a₁ := ⟨.inl (s.pairs ε q), ℓ'⟩) (a₂ := ⟨.inr (s.branches ε b2), m'⟩) (hy.trans hy2.symm))).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp (nativeLeafMap_injective h.data (s.chosen_plain ε)
      (a₁ := ⟨.inr (s.branches ε b), ℓ'⟩) (a₂ := ⟨.inl (s.pairs ε q2), m'⟩) (hy.trans hy2.symm))).1 (by simp)
  · have hs := nativeLeafMap_injective h.data (s.chosen_plain ε)
      (a₁ := ⟨.inr (s.branches ε b), ℓ'⟩) (a₂ := ⟨.inr (s.branches ε b2), m'⟩) (hy.trans hy2.symm)
    obtain ⟨hq', hm⟩ := Sigma.mk.inj_iff.mp hs
    have hqq : b = b2 := (s.branches ε).injective (Sum.inr.inj hq')
    subst hqq
    have hlm : ℓ' = m' := eq_of_heq hm
    subst hlm
    have : ℓ = m := Subtype.ext (Subtype.ext (hc.trans hc2.symm))
    subst this
    exact hx.symm.trans hx2

end WaveTurbulence.LFTwist
