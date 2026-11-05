/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairPartition

/-! # Exact surviving pair set after collapsing an embedded source couple -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- A positive first collapsed root orients the new root pair literally. -/
theorem collapseCoupleGarden_root_pair {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (ha : nodeSign G.sig a.1 = 1) :
    (a.1,b.1) ∈ sourcePairs (collapseCoupleGarden h) := by
  let E := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  apply Finset.mem_image.mpr
  refine ⟨E (.inr 0),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · exact ha
  · have hp := collapseCoupleGarden_pair_left h
    change ((E (.inr 0)).1,((collapseCoupleGarden h).pair (E (.inr 0))).1) = _
    rw [hp]
    rfl

/-- Erasing the new root pair leaves exactly the unchanged outside source matching. -/
theorem collapseCoupleGarden_pairs_erase {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (ha : nodeSign G.sig a.1 = 1) :
    (sourcePairs (collapseCoupleGarden h)).erase (a.1,b.1) =
      (sourcePairs G).filter (fun p => ∃ ℓ : OutsideRoots G.tree a b, ℓ.1.1 = p.1) := by
  classical
  let E := collapseLeafEquiv G.tree a b (Comb.subCouple_incomparable h)
  have hb : nodeSign G.sig b.1 = -1 := (Comb.subCouple_sign h).trans (congrArg Neg.neg ha)
  have hv (x : OutsideRoots G.tree a b) : (E (.inl x)).1 = x.1.1 := rfl
  have hp (x : OutsideRoots G.tree a b) :
      ((collapseCoupleGarden h).pair (E (.inl x))).1 = (G.pair x.1).1 := by
    rw [collapseCoupleGarden_pair_old h]
    rfl
  ext p
  constructor
  · intro hm
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hm
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
    have hs := (Finset.mem_filter.mp hx).2
    obtain ⟨z,rfl⟩ := E.surjective x
    cases z with
    | inl z =>
      rw [hv,hp]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨z.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,rfl⟩,z,rfl⟩
    | inr i =>
      fin_cases i
      · have he : ((E (.inr 0)).1,((collapseCoupleGarden h).pair (E (.inr 0))).1) = (a.1,b.1) := by
          rw [collapseCoupleGarden_pair_left h]
          rfl
        exact (hne he).elim
      · have hs' : nodeSign G.sig b.1 = 1 := hs
        rw [hb] at hs'
        contradiction
  · intro hm
    obtain ⟨hm,⟨z,hz⟩⟩ := Finset.mem_filter.mp hm
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hm
    have hzy : z.1 = y := Subtype.ext (hz.trans (congrArg (fun p : Pair w => p.1) he).symm)
    have hs : nodeSign G.sig z.1.1 = 1 := by rw [hzy]; exact (Finset.mem_filter.mp hy).2
    have he' : ((E (.inl z)).1,((collapseCoupleGarden h).pair (E (.inl z))).1) = p := by
      rw [hv,hp,hzy]
      exact he
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      apply z.ne_left
      exact hz.trans (congrArg (fun p : Pair w => p.1) heq)
    · exact Finset.mem_image.mpr ⟨E (.inl z),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,he'⟩

end WaveTurbulence.Reg.Skeleton
