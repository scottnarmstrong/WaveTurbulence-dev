/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleLinkCoordinates
public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates

/-! # The actual C2 decoration construction has exactly the prescribed link momenta -/

public section
namespace WaveTurbulence.IncohInst
open Links

variable {V : Type} [AddCommGroup V]

/-- Exact first couple link parameter, read in source branching-node notation. -/
theorem couple_xNode_decOfParams {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (r : V) (θ : Fin Q.links.length → V × V) (j : Fin Q.links.length) :
    xNode (decOfParams hQ r θ).1 (chosenBranch hQ j) = (θ j).1 := by
  have h := congrArg (fun θ => (θ j).1) (decParams_decOfParams hQ hQ.1 r θ)
  change xv (extend _) (chosenBranch hQ j).1 = _ at h
  rw [xv_extend] at h
  exact h

/-- Exact second couple link parameter. -/
theorem couple_yNode_decOfParams {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (r : V) (θ : Fin Q.links.length → V × V) (j : Fin Q.links.length) :
    yNode (decOfParams hQ r θ).1 (chosenBranch hQ j) = (θ j).2 := by
  have h := congrArg (fun θ => (θ j).2) (decParams_decOfParams hQ hQ.1 r θ)
  change yv (extend _) (chosenBranch hQ j).1 = _ at h
  rw [yv_extend] at h
  exact h

/-- Exact first paired-tree link parameter. -/
theorem tree_xNode_decOfParams {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (r : V) (θ : Fin (X.treeLinks (G.sig 0)).length → V × V)
    (j : Fin (X.treeLinks (G.sig 0)).length) :
    xNode (treeDecOfParams hX r θ).1 (treeChosenBranch hX j) = (θ j).1 := by
  have h := congrArg (fun θ => (θ j).1) (treeDecParams_treeDecOfParams hX r θ)
  change xv (extend _) (treeChosenBranch hX j).1 = _ at h
  rw [xv_extend] at h
  exact h

/-- Exact second paired-tree link parameter. -/
theorem tree_yNode_decOfParams {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (r : V) (θ : Fin (X.treeLinks (G.sig 0)).length → V × V)
    (j : Fin (X.treeLinks (G.sig 0)).length) :
    yNode (treeDecOfParams hX r θ).1 (treeChosenBranch hX j) = (θ j).2 := by
  have h := congrArg (fun θ => (θ j).2) (treeDecParams_treeDecOfParams hX r θ)
  change yv (extend _) (treeChosenBranch hX j).1 = _ at h
  rw [yv_extend] at h
  exact h

end WaveTurbulence.IncohInst
