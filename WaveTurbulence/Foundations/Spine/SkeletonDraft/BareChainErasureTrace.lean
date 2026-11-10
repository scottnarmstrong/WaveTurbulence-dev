/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBarePairFactorization
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawChainSubtrees
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBPredecessorTrace

/-! # Bare-chain erasure with exact transport of every retained original branch -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem bareChain_erasure_trace {w : ℕ} (X : RegChain) (hX : BareChain X)
    (R : Raw w) (a : Address w) (ha : a.2 ∈ (R.tree a.1).nodes)
    (G : Garden w) (hG : G.IsPlain) (he : rawOfGarden G = R.insertChain a X) :
    ∃ H : Garden w, H.IsPlain ∧ rawOfGarden H = R ∧
      ∃ T : ReductionTrace G H, ∀ b : GBranch H.tree,
        (T.branches b).1 = stretch a X.lonePath b.1 := by
  cases X with
  | nil =>
    rw [Raw.insertChain_nil] at he
    refine ⟨G,hG,he,ReductionTrace.refl G,?_⟩
    intro b
    exact (stretch_nil a b.1).symm
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
    obtain ⟨H₁,hH₁,he₁,T₁,hT₁⟩ := bareChain_erasure_trace rest hr R₁ d hd G hG
      (he.trans hfactor.symm)
    obtain ⟨H₀,hH₀,he₀,T₀,hT₀⟩ := bareChain_erasure_trace inner hi R₀ b hb H₁ hH₁ he₁
    obtain ⟨H,hH,heH,T,hT⟩ := exists_predecessor_trace_of_raw_opB R H₀ hH₀ a m ha he₀
    refine ⟨H,hH,heH,ReductionTrace.trans T₁ (ReductionTrace.trans T₀ T),?_⟩
    intro e
    change (T₁.branches (T₀.branches (T.branches e))).1 = _
    rw [hT₁,hT₀,hT]
    exact stretch_outer_inner_rest a e.1 m.c m.lone inner.lonePath rest.lonePath
termination_by structural X

end WaveTurbulence.Reg.Skeleton
