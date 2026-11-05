/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.RootedLayering
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestMinis
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # Restricting actual decorations to completely paired rooted subforests -/

public section
namespace WaveTurbulence.RegRed
open TTree Reg.Skeleton

theorem labels_eq_of_sourcePair {w : ℕ} (G : Garden w) {V : Type*}
    (κ : GNode G.tree → V) (hp : ∀ ℓ, κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (x y : GNode G.tree) (h : (x.1,y.1) ∈ sourcePairs G) : κ x = κ y := by
  obtain ⟨ℓ,q,hℓ,hq,hpair⟩ := sourcePairs_actual_endpoints G _ h
  have hx : x = ℓ.toNode := Subtype.ext hℓ.symm
  have hy : y = q.toNode := Subtype.ext hq.symm
  rw [hx,hy,← hpair]
  exact hp ℓ

/-- Both Kirchhoff conservation and the actual inherited matching are retained. -/
theorem subforest_isDecoration {w v : ℕ} (G : Garden w)
    (E : Comb.RootedSubforest G.tree v) (hc : G.CompletelyPaired E.leafSet)
    {V : Type*} [AddCommGroup V] (κ : GNode G.tree → V) (hκ : IsDecoration G κ) :
    IsDecoration (E.inducedGarden hc) (fun a => κ (E.nodeEmbedding a)) := by
  constructor
  · intro b
    let b' : GBranch E.shape := b
    have h := hκ.1 (subforestBranchEmbedding E b')
    have h0 := congrArg κ (subforest_node_child E b' 0)
    have h1 := congrArg κ (subforest_node_child E b' 1)
    have h2 := congrArg κ (subforest_node_child E b' 2)
    have hb := congrArg κ (subforest_branch_node E b')
    exact hb.trans (h.trans (congrArg₂ (· + ·) (congrArg₂ (· - ·) h0.symm h1.symm) h2.symm))
  · intro ℓ
    let ℓ' : GLeaf E.shape := ℓ
    have h := congrArg (fun q : GLeaf G.tree => κ q.toNode) (E.inducedGarden_pair hc ℓ')
    exact (congrArg κ (subforest_node_leaf E ℓ')).trans
      ((hκ.2 (E.leafEmbedding ℓ')).trans
        (h.symm.trans (congrArg κ (subforest_node_leaf E ((E.inducedGarden hc).pair ℓ'))).symm))

end WaveTurbulence.RegRed
