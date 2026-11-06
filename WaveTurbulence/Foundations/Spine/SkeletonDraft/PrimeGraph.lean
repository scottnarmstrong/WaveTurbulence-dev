/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import WaveTurbulence.Foundations.Molecule.PrimeGardenDefs

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniClassification
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GraphFaithfulness

/-! # Source prime gardens are terminal in the labelled graph reduction

The prime predicate is TARGET's literal absence of an embedded mini piece.
Source expansion histories still require their graph-collapse fidelity theorem.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- A source-prime garden has no labelled graph contraction. -/
theorem LabelledGarden.graph_normal_of_prime {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) (hG : IsPrimeGarden G.garden) : PortMatching.Normal G.graph := by
  rintro N ⟨D,_⟩
  exact hG.2 (G.sourceMini_of_graph_dipole hG.1 D)

/-- Conditional bridge on literal graph histories: prime source carriers agree
when both are terminal labelled reducts of one matching and inherit one signature.
The source A/B-to-graph history theorem is proved separately. -/
theorem LabelledGarden.prime_eq_of_graph_reductions {w : ℕ} {B : Type*} [DecidableEq B]
    (G H : LabelledGarden w B) (M : PortMatching (Fin w ⊕ B))
    (hG : IsPrimeGarden G.garden) (hH : IsPrimeGarden H.garden)
    (hsig : G.garden.sig = H.garden.sig)
    (hMG : PortMatching.Reduces M G.graph) (hMH : PortMatching.Reduces M H.graph) : G.garden = H.garden :=
  G.garden_eq_of_graph_eq H hG.1 hH.1 hsig
    (PortMatching.normal_unique (G.graph_normal_of_prime hG) (H.graph_normal_of_prime hH) hMG hMH)

end WaveTurbulence.Reg.Skeleton
