/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIncomparable
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerGarden
public import WaveTurbulence.Frozen.Defs.GardenIsPlain
public import WaveTurbulence.Frozen.Defs.InstDecidableEqGNode
public import WaveTurbulence.Frozen.Defs.IsCanonC
public import WaveTurbulence.Frozen.Defs.IsCanonG
public import WaveTurbulence.Frozen.Defs.IsCanonGC
public import WaveTurbulence.Frozen.Defs.IsCanonH
public import WaveTurbulence.Frozen.Defs.IsCouple
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachLinkedOn
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes
public import WaveTurbulence.Frozen.Defs.LayeredGardenCanonInd
public import WaveTurbulence.Frozen.Defs.LayeredGardenRoots
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecomp
public import WaveTurbulence.Frozen.Defs.LayeredGardenTopDecompWith
public import WaveTurbulence.Provider.CanonicalCharacterization

/-!
# canonicalCharacterization

Wave B tier B1 (WaveB1-Statements.lean), source: T Def `defcanon`, L657–L668; L888–L897; T Def `defgtr`; T L2288. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B1.11 `canonicalCharacterization`** (T Def `defcanon`, L657–L668; Prop `canonequiv`,
L888–L897; Def `defflower`, L2262; review G-2, mandatory with B1). (1) The criterion `IsCanonG (p+1)`
coincides with the inductive construction of Def `defcanon` (read as `CanonInd` on the roots, plain
garden); (2) **uniqueness of the construction data**, for gardens, couples and flower gardens alike
(`IsCanonGC` covers `𝒢` and `𝒞`; stage-3 R7): any top-level decomposition `(U, Bp)` has
`U = attachNodes p` and blocks the classes of the relation `AttachLinkedOn p` generated on `𝒰`
(stage-1 R1), hence `IsTrunc`, defined through these data, is T Def `defgtr` (and `ℋ^tr`, T L2288,
for the restriction kind `0`, i.e. `𝒳`; the `𝒴`/`𝒲` reading is packet X1's, delta-1 D1);
for flower gardens with `flowers = false` the hypothesis is unsatisfiable, so the clause is vacuous
there; (3) the same as (1) for couples (`IsCanonC`, no properness/irreducibility) and (4) for flower
gardens (`IsCanonH`, flowers allowed in the top region, stems in layer `p`, no irreducibility).
Deviation: Def `defcanon` builds gardens from data; we state the equivalent decomposition of a given
garden (the construction is a bijection onto its image, which is (2)). -/
theorem canonicalCharacterization {w : ℕ} (p : ℕ) (LG : LayeredGarden w) :
    (IsCanonG (p + 1) LG ↔ LG.garden.IsPlain ∧ LG.CanonInd (p + 1) LG.roots) ∧
    ((IsCanonGC (p + 1) LG ∨ IsCanonH (p + 1) LG) →
      ∀ (flowers : Bool) (U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U),
        LG.TopDecompWith flowers p (LG.CanonInd p) LG.roots U Bp →
        U = LG.attachNodes p ∧
          ∀ B ∈ Bp.parts, ∀ u ∈ B, ∀ u' ∈ U,
            (u' ∈ B ↔ Relation.EqvGen (LG.AttachLinkedOn p) u u')) ∧
    (∀ LG2 : LayeredGarden 2, IsCanonC (p + 1) LG2 ↔ IsCouple LG2.garden ∧
      (∀ s ∈ LG2.roots, ∀ s' ∈ LG2.roots, s ≠ s' → s.Incomparable s') ∧
      LG2.TopDecomp false p (LG2.CanonInd p) LG2.roots) ∧
    (IsCanonH (p + 1) LG ↔ LG.garden.IsFlowerGarden ∧
      LG.TopDecomp true p (LG.CanonInd p) LG.roots) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
