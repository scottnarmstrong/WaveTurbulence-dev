/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.MarkTag
public import WaveTurbulence.Frozen.Defs.NodeSign
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# Garden

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defgarden`, L632–L638; DH21-2 Def 4.1; L2259–L2263; WAVE-B v2 §2.2.2. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A **garden of width `w` with marked leaves** (T Def `defgarden`, L632–L638; DH21-2 Def 4.1;
paired trees L637; flower gardens Def `defflower`, L2259–L2263; WAVE-B v2 §2.2.2 and topology review
G-1): trees `𝒯_j` of signs `ζ_j` (`j < w`), a set of **marked** leaves with tags, and a pairing of the
unmarked leaves into pairs of opposite signs. The pairing is encoded as an involution `pair` of all
leaves whose fixed points are exactly the marked leaves. Instances: ordinary gardens (`IsPlain`,
width `2m`), couples (`IsCouple`), paired trees (`IsPairedTree`, width 1), flower gardens
(`IsFlowerGarden`). Irreducibility and balance of the signature are predicates. -/
structure Garden (w : ℕ) where
  /-- the signature `(ζ₁,…,ζ_w)` -/
  sig : Fin w → ℤˣ
  /-- the trees `𝒯₁,…,𝒯_w` -/
  tree : Fin w → TTree
  /-- the pairing involution (fixed points = marked leaves) -/
  pair : GLeaf tree → GLeaf tree
  /-- the marks: `none` for paired leaves, `some tag` for marked (unpaired) leaves -/
  mark : GLeaf tree → Option MarkTag
  pair_pair : ∀ ℓ, pair (pair ℓ) = ℓ
  pair_eq_iff : ∀ ℓ, pair ℓ = ℓ ↔ mark ℓ ≠ none
  /-- paired leaves have opposite signs -/
  pair_sign : ∀ ℓ, pair ℓ ≠ ℓ → nodeSign sig (pair ℓ).1 = -nodeSign sig ℓ.1

end WaveTurbulence
