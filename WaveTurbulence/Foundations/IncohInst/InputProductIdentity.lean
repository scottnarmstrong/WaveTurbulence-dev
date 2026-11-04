/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.SourceInputs
public import WaveTurbulence.Foundations.Incoh.SourcePointwiseLocalization
public import WaveTurbulence.Foundations.Incoh.MomentumTreeInputs

/-! # The actual analytic leaf product equals the original garden input product -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The analytic couple input momentum is exactly its original positive leaf momentum. -/
theorem couple_inputMomentum_eq {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {d : ℕ} (k : Mom d) (x : Fin Q.links.length → Fin 2 → Mom d)
    (a : Fin (Fintype.card (PlusLeaf G))) :
    (coupleCarrier hQ).inputMomentum k x a =
      (decOfParams hQ k (fun j => (x j 0, x j 1))).1 ((coupleInputEquiv G).symm a).1.toNode :=
  coupleNodeRow_eval hQ _ (rootLinkMomenta k x)

/-- The analogous identity for actual paired-tree input momenta. -/
theorem tree_inputMomentum_eq {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    {d : ℕ} (k : Mom d) (x : Fin (X.treeLinks (G.sig 0)).length → Fin 2 → Mom d)
    (a : Fin (Fintype.card (TPlus G))) :
    (treeCarrier hX).inputMomentum k x a =
      (treeDecOfParams hX k (fun j => (x j 0, x j 1))).1 ((treeInputEquiv G).symm a).1.toNode :=
  treeNodeRow_eval hX _ (rootLinkMomenta k x)

/-- Exact input-product agreement for the original decoded couple, with each leaf layer retained. -/
theorem couple_sourceLeafWeight_eq {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {d : ℕ} (F : ℕ → Mom d → ℝ) (k : Mom d) (x : Fin Q.links.length → Fin 2 → Mom d) :
    (coupleCarrier hQ).sourceLeafWeight (coupleInputFunctions LG F) k x =
      ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) ((decOfParams hQ k (fun j => (x j 0, x j 1))).1 ℓ.toNode) : ℂ) := by
  let κ : GNode LG.garden.tree → Mom d := (decOfParams hQ k (fun j => (x j 0, x j 1))).1
  let h : GLeaf LG.garden.tree → ℂ := fun ℓ => F (LG.layer ℓ.toNode) (κ ℓ.toNode)
  unfold MomentumTreeData.sourceLeafWeight
  simp_rw [couple_inputMomentum_eq]
  change (∏ a, h ((coupleInputEquiv LG.garden).symm a).1) = ∏ ℓ ∈ inputLeaves LG.garden, h ℓ
  calc
    _ = ∏ ℓ : PlusLeaf LG.garden, h ℓ.1 := Equiv.prod_comp (coupleInputEquiv LG.garden).symm _
    _ = _ := by
      rw [couple_inputLeaves hQ.1]
      exact (Finset.prod_subtype (plusLeaves LG.garden) (fun ℓ => by simp [plusLeaves]) h).symm

/-- Exact input-product agreement for the paired tree; the lone leaf remains absent. -/
theorem tree_sourceLeafWeight_eq {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    {d : ℕ} (F : ℕ → Mom d → ℝ) (k : Mom d)
    (x : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → Mom d) :
    (treeCarrier hX).sourceLeafWeight (treeInputFunctions LG F) k x =
      ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) ((treeDecOfParams hX k (fun j => (x j 0, x j 1))).1 ℓ.toNode) : ℂ) := by
  let κ : GNode LG.garden.tree → Mom d := (treeDecOfParams hX k (fun j => (x j 0, x j 1))).1
  let h : GLeaf LG.garden.tree → ℂ := fun ℓ => F (LG.layer ℓ.toNode) (κ ℓ.toNode)
  unfold MomentumTreeData.sourceLeafWeight
  simp_rw [tree_inputMomentum_eq]
  change (∏ a, h ((treeInputEquiv LG.garden).symm a).1) = ∏ ℓ ∈ inputLeaves LG.garden, h ℓ
  calc
    _ = ∏ ℓ : TPlus LG.garden, h ℓ.1 := Equiv.prod_comp (treeInputEquiv LG.garden).symm _
    _ = _ := by
      rw [tree_inputLeaves hX]
      exact (Finset.prod_subtype (plusPaired LG.garden) (fun ℓ => by simp [plusPaired]) h).symm

end WaveTurbulence.IncohInst
