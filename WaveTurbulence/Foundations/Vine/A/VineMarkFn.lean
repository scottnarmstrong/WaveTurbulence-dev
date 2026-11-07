/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions
/-! # B1a THREAD-ROOTS (ruling F-1): marked vine sets of a prime reconstruction, on main

Copied by source from `scope/B0-STAGE1MK/probe/Stage1MKProbe.lean` (sha256 `dab37b30…6c6b`): lines 9–26 (`AddrBelow`,
`ownRegion`, `nearRegion`, which `markedVinesRaw` uses) and lines 91–97 (`markedVinesRaw`, `MarkFn`), into the fresh
namespace `WaveTurbulence.Stage1Mk` (the world's `Flower.MkDefs` copies keep their own names until they switch to
these).  `MarkFn` is the type of the trailing marking argument `mk` of the prescribed-point roots (R12, default
`fun _ => ∅`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1Mk
open WaveTurbulence WaveTurbulence.LGSpine

variable {w : ℕ}

/-- `y` lies at or below the address `x` (same tree, `x` a prefix of `y`). -/
def AddrBelow (x y : Reg.Skeleton.Address w) : Prop := x.1 = y.1 ∧ x.2 <+: y.2

/-- The addresses of the inflated garden owned by the skeleton node `a`: at or below its inflated attachment
address, and not at or below that of any proper skeleton descendant. For a branch this is the regular tree
`𝒯_(a)` together with the node `a`; for a leaf it is the tree of the couple inflated at that leaf. -/
def ownRegion (S : Garden w) (X : GBranch S.tree → RegChain) (a : GNode S.tree) :
    Set (Reg.Skeleton.Address w) :=
  {y | AddrBelow (Reg.Skeleton.inflatedPosition S X a) y ∧
    ∀ c : GNode S.tree, a.IsDesc c → c ≠ a → ¬ AddrBelow (Reg.Skeleton.inflatedPosition S X c) y}

/-- The near region of a skeleton branch `b`: its own region, the regions of its three children, and the region
of the partner of every leaf child (the far tree of a couple at a leaf child). Over the non-upper atoms of a
(CL) vine `𝕍` the union is `𝐀(𝕍) ∪ LS(𝕍)` (o75 Def. 2.3 plus the lower slots: U-clock §15 enlarged marking). -/
def nearRegion (S : Garden w) (X : GBranch S.tree → RegChain) (b : GBranch S.tree) :
    Set (Reg.Skeleton.Address w) :=
  ownRegion S X b.toNode ∪ (⋃ i : Fin 3, ownRegion S X (b.child i)) ∪
    ⋃ (ℓ : GLeaf S.tree) (_ : b.IsParentOf ℓ), ownRegion S X (S.pair ℓ).toNode

/-- The marked vines of `𝒱` for a skeleton `S` with tree data `X` and a protected set `Pi` of the inflated garden. -/
def markedVinesRaw (S : Garden w) (X : GBranch S.tree → RegChain) {T : Fin w → TTree}
    (Pi : Finset (GNode T)) : Set (Stage1.CLVine S) :=
  {c | c ∈ Stage1.vinesV S ∧ ∃ b ∈ c.atoms, b ≠ c.upper ∧ ∃ a ∈ Pi, a.1 ∈ nearRegion S X b}

/-- A marking function: the marked vines of every prime reconstruction. -/
abbrev MarkFn (w : ℕ) := ∀ {LG : LayeredGarden w} (A : VineA.PrimeData LG), Set (Stage1.CLVine A.skeleton)

/-- The empty marking (main's Stage 1): no vine is marked. -/
theorem markFn_empty_apply {LG : LayeredGarden w} (A : VineA.PrimeData LG) :
    ((fun _ => ∅ : MarkFn w) A) = (∅ : Set (Stage1.CLVine A.skeleton)) := rfl

end WaveTurbulence.Stage1Mk
