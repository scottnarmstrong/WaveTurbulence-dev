/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.FixPat
public import WaveTurbulence.Frozen.Defs.FlowerKind
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.GardenOrder
public import WaveTurbulence.Frozen.Defs.GardenSign
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.IsCanonH
public import WaveTurbulence.Frozen.Defs.KernelKgen
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachNodes
public import WaveTurbulence.Frozen.Defs.LayeredGardenAttachedOrder
public import WaveTurbulence.Frozen.Defs.LayeredGardenCutWeight1
public import WaveTurbulence.Frozen.Defs.LayeredGardenCutWeight2
public import WaveTurbulence.Frozen.Defs.LayeredGardenFixPat
public import WaveTurbulence.Frozen.Defs.LayeredGardenFlowerKindOK
public import WaveTurbulence.Frozen.Defs.LayeredGardenPatValid
public import WaveTurbulence.Frozen.Defs.LayeredGardenSibWeight
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN

/-!
# flowerSum

Wave B tier B1 (WaveB1-Flower.lean), source: T (flowerexp2), L2287–L2290. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open Classical in
/-- **The flower sum** (corrects `truncSumHζ`; T (flowerexp2), L2287–L2290; F39, F46/D1, R8). It sums
`kernelKgen` over the layered flower gardens `𝒢` of width `w` and order `N` such that:
- `𝒢 ∈ ℋ_{p+1}` (stems in layer `p`);
- the attached gardens have order `≤ N_p`;
- the initial flower trees are of kind `kind`;
- the flower signs are `ζ · ζ_j`;
- each tree's pattern is valid.

The kernel data:
- flower parents ↦ `s`, plus the pattern's node;
- the phases at the flower parents removed if `dagger` is given;
- the weights: `M₁` cutoff (index `cut1`), `M₂` cutoff (`cut2`), sibling labels (`dagger`);
- `(n, n')`-decorations: roots `n`, flowers `n'`. -/
noncomputable def flowerSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid p j (pat j)),
    kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
      (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)
      (fun k => (cut1.elim 1 fun j₁ => LG.cutWeight1 p P.L j₁ k) *
        (cut2.elim 1 fun j₂ => LG.cutWeight2 P.L j₂ k) * (dagger.elim 1 fun c => LG.sibWeight c k))
      (fun _ => t) 0 (fun _ => n) n'

end WaveTurbulence
