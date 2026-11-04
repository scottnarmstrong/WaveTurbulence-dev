/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleCarrier
public import WaveTurbulence.Foundations.IncohInst.TreeCarrier

/-! # Exact decoded source order and link count identities -/

public section
namespace WaveTurbulence.IncohInst

/-- The original couple branching order is exactly twice the link count. -/
theorem couple_order_eq_twice_links {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    G.order = 2 * Q.links.length := by
  have h := (coupleCarrier hQ).order_eq
  simpa only [coupleCarrier, treeShape_order, Garden.order] using h

/-- The original tree branching order is exactly twice the link count. -/
theorem tree_order_eq_twice_links {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    G.order = 2 * (X.treeLinks (G.sig 0)).length := by
  have h := (treeCarrier hX).order_eq
  simpa only [treeCarrier, treeShape_order, Garden.order] using h

end WaveTurbulence.IncohInst
