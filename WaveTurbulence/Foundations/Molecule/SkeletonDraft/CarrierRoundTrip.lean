/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPartner

/-! # Exact recovery of source raw data from its actual ordinary garden -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem Raw.ext {w : ℕ} {R S : Raw w} (hs : R.sig = S.sig) (ht : R.tree = S.tree)
    (hp : R.pairs = S.pairs) : R = S := by
  cases R
  cases S
  cases hs
  cases ht
  cases hp
  rfl

/-- The actual carrier retains every oriented pair, without enumeration choices. -/
theorem sourcePairs_gardenOfRaw {w : ℕ} (R : Raw w) (hR : R.Valid) :
    sourcePairs (gardenOfRaw R hR) = R.pairs := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
    change GLeaf R.tree at ℓ
    have hpos := (Finset.mem_filter.mp hℓ).2
    change nodeSign R.sig ℓ.1 = 1 at hpos
    have he := edgeAt_spec R hR ℓ
    have hv := hR.1 _ he.1
    have hf : (edgeAt R hR ℓ).1 = ℓ.1 := by
      rcases he.2 with h | h
      · exact h
      · have hn : (1 : ℤˣ) = -1 := hpos.symm.trans ((congrArg (nodeSign R.sig) h).symm.trans hv.2.2.2)
        exact ((by decide : (1 : ℤˣ) ≠ -1) hn).elim
    have ht : (rawPartner R hR ℓ).1 = (edgeAt R hR ℓ).2 := by
      rw [rawPartner_val,ite_eq_left hf]
    change (ℓ.1,(rawPartner R hR ℓ).1) ∈ R.pairs
    rw [ht,← hf]
    exact he.1
  · intro hp
    have hv := hR.1 p hp
    let ℓ : GLeaf R.tree := ⟨p.1,hv.1⟩
    have he : p = edgeAt R hR ℓ := edgeAt_unique R hR ℓ p hp (Or.inl rfl)
    have ht : (rawPartner R hR ℓ).1 = p.2 := by
      rw [rawPartner_val,← he,ite_eq_left rfl]
    apply Finset.mem_image.mpr
    refine ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv.2.2.1⟩,?_⟩
    exact Prod.ext rfl ht

/-- The canonical carrier construction is an exact section of source data extraction. -/
theorem rawOfGarden_gardenOfRaw {w : ℕ} (R : Raw w) (hR : R.Valid) :
    rawOfGarden (gardenOfRaw R hR) = R :=
  Raw.ext rfl rfl (sourcePairs_gardenOfRaw R hR)

/-- Plain garden carriers are determined by their signature, forest and literal pair set. -/
theorem rawOfGarden_injective_plain {w : ℕ} {G H : Garden w} (hG : G.IsPlain) (hH : H.IsPlain)
    (he : rawOfGarden G = rawOfGarden H) : G = H := by
  obtain ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩ := G
  obtain ⟨hs,ht,hp,hm,hpp,heq,hsgn⟩ := H
  have hsig := congrArg Raw.sig he
  have htree := congrArg Raw.tree he
  change gs = hs at hsig
  change gt = ht at htree
  subst hs
  subst ht
  let G : Garden w := ⟨gs,gt,gp,gm,gpp,geq,gsgn⟩
  let H : Garden w := ⟨gs,gt,hp,hm,hpp,heq,hsgn⟩
  change G.IsPlain at hG
  change H.IsPlain at hH
  have hpairs : sourcePairs G = sourcePairs H := congrArg Raw.pairs he
  have hpair : gp = hp := by
    funext ℓ
    apply Subtype.ext
    have hm := sourcePairAt_mem G hG ℓ
    rw [hpairs] at hm
    have he := sourcePairs_eq_at H hH (sourcePairAt G ℓ) hm ℓ (sourcePairAt_endpoint G ℓ)
    change (if nodeSign gs ℓ.1 = 1 then (ℓ.1,(gp ℓ).1) else ((gp ℓ).1,ℓ.1)) =
      (if nodeSign gs ℓ.1 = 1 then (ℓ.1,(hp ℓ).1) else ((hp ℓ).1,ℓ.1)) at he
    by_cases h : nodeSign gs ℓ.1 = 1
    · simp only [h,ite_true] at he
      exact congrArg Prod.snd he
    · simp only [h,ite_false] at he
      exact congrArg Prod.fst he
  have hmark : gm = hm := funext fun ℓ => (hG ℓ).trans (hH ℓ).symm
  cases hpair
  cases hmark
  rfl

end WaveTurbulence.Reg.Skeleton
