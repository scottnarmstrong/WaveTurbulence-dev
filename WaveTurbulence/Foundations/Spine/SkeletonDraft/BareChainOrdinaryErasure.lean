/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBarePairFactorization
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawChainSubtrees
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBOrdinaryPredecessor

/-! # Constructive actual erasure of a bare chain above a complete existing subtree -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem bareChain_ordinary_erasure {w : ℕ} (X : RegChain) (hX : BareChain X)
    (R : Raw w) (a : Address w) (ha : a.2 ∈ (R.tree a.1).nodes)
    (G : Garden w) (hG : G.IsPlain) (he : rawOfGarden G = R.insertChain a X) :
    ∃ H : Garden w, H.IsPlain ∧ rawOfGarden H = R ∧ GardenReduces G H := by
  cases X with
  | nil =>
    rw [Raw.insertChain_nil] at he
    exact ⟨G,hG,he,Relation.ReflTransGen.refl⟩
  | pair m Qr Qg inner rest =>
    obtain ⟨rfl,rfl,hi,hr⟩ := hX
    let R₀ := R.opB a m
    let b := addrExt a [m.c]
    let R₁ := R₀.insertChain b inner
    let d := addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])
    have hb : b.2 ∈ (R₀.tree b.1).nodes := R.opB_continuing_node a m ha
    have hd : d.2 ∈ (R₁.tree d.1).nodes := by
      have ht := R.insertChain_pair_inner_forest a ha m inner
      change R₁.tree = _ at ht
      rw [ht]
      exact R.insertChain_pair_rest_node a ha m inner
    have hfactor : R₁.insertChain d rest = R.insertChain a (.pair m .triv .triv inner rest) :=
      R.insertChain_pair a ha m inner rest
    obtain ⟨H₁,hH₁,he₁,hGH₁⟩ := bareChain_ordinary_erasure rest hr R₁ d hd G hG
      (he.trans hfactor.symm)
    obtain ⟨H₀,hH₀,he₀,hH₁H₀⟩ := bareChain_ordinary_erasure inner hi R₀ b hb H₁ hH₁ he₁
    obtain ⟨H,hH,heH,hH₀H⟩ := exists_ordinary_predecessor_of_raw_opB R H₀ hH₀ a m ha he₀
    exact ⟨H,hH,heH,(hGH₁.trans hH₁H₀).tail hH₀H⟩
termination_by structural X

end WaveTurbulence.Reg.Skeleton
