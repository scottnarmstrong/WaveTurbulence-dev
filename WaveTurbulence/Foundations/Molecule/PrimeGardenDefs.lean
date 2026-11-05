/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniClassification

/-! # Definition-only extraction of the accepted source prime-garden predicates

Verbatim bodies from SKELETON SourceMiniClassification and PrimeGraph.
Only their unrelated graph-reduction proof imports are excluded.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- TARGET Proposition 4.5 / DH21-2 Definition 4.3: an ordinary garden
containing neither an embedded `(1,1)` mini couple nor an embedded mini tree.
(UNIVERSE: `LeafBond`, `MiniAOccurrence`, `MiniBOccurrence`, `MiniOccurrence` are the identical declarations of
`SkeletonDraft.SourceMiniClassification`, no longer duplicated here.) -/
def IsPrimeGarden {w : ℕ} (G : Garden w) : Prop := G.IsPlain ∧ ¬ Nonempty (MiniOccurrence G)

end WaveTurbulence.Reg.Skeleton
