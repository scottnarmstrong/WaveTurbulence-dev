/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Defs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
public import WaveTurbulence.Foundations.FinalCount.S1Collection
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso

/-! # MK-DEFS (A2-R, from B0 S-STAGE1MK): the concrete marking rule and the intrinsic capped data

Copied by source from `scope/B0-STAGE1MK/probe/Stage1MKProbe.lean` (sha256 `dab37b30…6c6b`), lines 9–126, into
namespace `WaveTurbulence.Flower.MkDefs` (see COPIED-SHA256SUMS): `AddrBelow`, `ownRegion`, `nearRegion`, the concrete
`protSkOf`, `markedVines`, `protSkOf_state_iff`, the intrinsic pins `fixCap`, the depth selection `stemAt`/`selCap`/
`selSetCap`, the dagger `offCap`, `selOK`, the protected sets `protI`/`protI0`, and the marking statements
`MarkCountBound`, `MarkTransported`, `MarkInvariantBatch` (B2 targets). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

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

/-- **The concrete marking rule** (S-MARKED F-3): a skeleton branch is protected iff its near region contains a node
of the protected set `Π` of the layered garden. -/
def protSkOf : ∀ R, MarkRule R := fun _R J fix sel _ι B b =>
  ∃ a ∈ protectedSet B.layered J (fix B.layered) (sel B.layered),
    a.1 ∈ nearRegion B.skeleton B.data.tree b

/-- Intrinsic capped pins: the frozen `fixPat` with capped flower parents (S-MARKED A2 `capFix`). -/
noncomputable def fixCap (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (b : GBranch LG.garden.tree) : Option ℝ :=
  if IsCapFlowerParent LG J b then some s else
  match pat b.1.1 with
  | .plain => none
  | .dRoot => if b.1.2 = [] then some t else none
  | .dParent => if ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ c.IsChildOf b then some s else none
  | .dChild i => if ∃ c : GBranch LG.garden.tree, IsCapFlowerParent LG J c ∧ b.1.1 = c.1.1 ∧
      b.1.2 = c.1.2 ++ [i] then some s else none

/-- Intrinsic selected vertex: the capped-stem vertex of tree `j` at depth `k` (if unique). -/
noncomputable def stemAt (LG : LayeredGarden w) (J : Finset (Fin w)) (j : Fin w) (k : ℕ) :
    Option (GBranch LG.garden.tree) :=
  if h : ((stemSetCap LG J j).filter fun b => b.1.2.length = k).card = 1 then
    some (Classical.choose (Finset.card_eq_one.mp h)) else none

noncomputable def selCap (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) :
    Fin w → Option (GBranch LG.garden.tree) :=
  fun j => (kSel j).bind (stemAt LG J j)

noncomputable def selSetCap (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) :
    Finset (GBranch LG.garden.tree) :=
  Finset.univ.filter fun b => ∃ j, selCap LG J kSel j = some b


/-- Dagger: phases omitted at the capped flower parents (transport of the frozen carrier's `off`). -/
noncomputable def offCap (LG : LayeredGarden w) (J : Finset (Fin w)) (dag : Bool) : Finset (GBranch LG.garden.tree) :=
  if dag then Finset.univ.filter (IsCapFlowerParent LG J) else ∅

/-- Every requested selected vertex exists (else the derivative-expansion term is absent: weight `0`). -/
noncomputable def selOK (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) : ℝ :=
  if ∀ j, (kSel j).isSome → (selCap LG J kSel j).isSome then 1 else 0

/-- The intrinsic protected set `Π` (fine marking) and its stem-independent part `Π₀` (coarse marking). -/
noncomputable def protI (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) : Finset (GNode LG.garden.tree) :=
  protectedSet LG J (fixCap LG J pat t s) (selSetCap LG J kSel)

noncomputable def protI0 (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) :
    Finset (GNode LG.garden.tree) :=
  protectedSet LG J (fixCap LG J pat t s) ∅

/-! ## Marked vine sets on a reconstruction, and their transport (o75 Lemmas 1⁺–2⁺). -/

/-- The marked vines of `𝒱` for a skeleton `S` with tree data `X` and a protected set `Pi` of the inflated garden. -/
def markedVinesRaw (S : Garden w) (X : GBranch S.tree → RegChain) {T : Fin w → TTree}
    (Pi : Finset (GNode T)) : Set (Stage1.CLVine S) :=
  {c | c ∈ Stage1.vinesV S ∧ ∃ b ∈ c.atoms, b ≠ c.upper ∧ ∃ a ∈ Pi, a.1 ∈ nearRegion S X b}

/-- A marking function: the marked vines of every prime reconstruction. -/
abbrev MarkFn (w : ℕ) := ∀ {LG : LayeredGarden w} (A : VineA.PrimeData LG), Set (Stage1.CLVine A.skeleton)

/-- Fine marking (`Π`, with selected seeds) and coarse marking (`Π₀`). -/
def markI (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ) : MarkFn w :=
  fun {LG} A => markedVinesRaw A.skeleton A.data.tree (protI LG J pat t s kSel)

def markI0 (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) : MarkFn w :=
  fun {LG} A => markedVinesRaw A.skeleton A.data.tree (protI0 LG J pat t s)

/-- **Lemma 1⁺ (B2a target).** At most `3|Π|` vines of `𝒱` are marked. -/
def MarkCountBound : Prop :=
  ∀ {w : ℕ} {LG : LayeredGarden w} (A : VineA.PrimeData LG) (Pi : Finset (GNode LG.garden.tree)),
    (markedVinesRaw A.skeleton A.data.tree Pi).ncard ≤ 3 * Pi.card

/-- Transport of a marked set along a molecule isomorphism of skeletons. -/
def MarkTransported {S S' : Garden w} (F : Stage1.MolIso S.molecule S'.molecule)
    (M : Set (Stage1.CLVine S)) (M' : Set (Stage1.CLVine S')) : Prop :=
  ∀ (c : Stage1.CLVine S) (c' : Stage1.CLVine S'), c'.atoms = F.img c.atoms → (c ∈ M ↔ c' ∈ M')

end WaveTurbulence.Flower.MkDefs
