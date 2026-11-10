/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Ports
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PortOverlap

/-! # A uniform four-port representation retaining every source edge

Root vertices use port 0; their three other ports are explicitly inactive
identities. Branch vertices use all four ordered ports. The padding is an
exact embedding of the actual source port matching, not a graph quotient.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

abbrev Vertex {w : ℕ} (G : Garden w) := Fin w ⊕ GBranch G.tree
abbrev UniformPort {w : ℕ} (G : Garden w) := Vertex G × Fin 4

def padPort {w : ℕ} (G : Garden w) : Port G → UniformPort G
  | .inl j => (.inl j,0)
  | .inr (b,i) => (.inr b,i)

end WaveTurbulence.Reg.Skeleton
