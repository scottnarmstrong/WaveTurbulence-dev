/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.XChain.FlowerDraft.Kernel

/-!
# X2, part 1: the random flower kernels of `flowerest1`

TARGET Prop `flowerest1` (L2279–L2305) bounds `𝔼_p|𝒦^ζ_{kk'}(t,s)|^{2P}` for the kernels `𝒦 ∈ {𝒳, 𝒴, 𝒲}`
(T (operatorxker), L2270–L2273) and their variants. A variant has:
- the `M₁` and `M₂` smooth cutoffs;
- the `†` modification (T L2327);
- the derivative patterns, which put a Dirac factor `δ(t_𝔯 − t)` or `δ(t_𝔫 − s)` on one more node (T L2312,
  L2331).

This file defines these kernels with the input `a(p)` (a single flower tree, before the moment expansion). Each piece
mirrors the garden-level piece of the B1.12 gate (`Flower-Gate.lean`):

| here (one flower tree) | B1.12 (layered flower garden) |
|---|---|
| `treeFixPat`, `treePatValid` | `LayeredGarden.fixPat`, `PatValid` |
| `treeDomFix`, `extendFixT` | `kDomainFix`, `Garden.extendFix` (layer `p`, upper time `t`) |
| `phaseOffT` | `phaseProdOff` |
| `treeCut1`, `treeCut2`, `treeSib` | `cutWeight1`, `cutWeight2`, `sibWeight` |
| `flowerKernelGen` | `kernelKgen` |
| `kindTrees`, `randFlowerKernel` | `FlowerKindOK`, `flowerSum` |

With the plain pattern, no `†` and no cutoffs, `flowerKernelGen` is TARGET's `𝒥̃_𝒯` (jtflower), the
`flowerKernel` of `Flower-Kernel.lean`.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.SysAPI

open FTree

variable (L γ δ : ℝ) {d : ℕ}

/-! ## Designated times, time domain -/

open Classical in
/-- **The designated times of one flower tree** for the pattern `pat` (as `LayeredGarden.fixPat`):
- `𝔣^pr ↦ s` always;
- `dRoot`: the root also `↦ t`;
- `dParent`: the parent of `𝔣^pr` also `↦ s`;
- `dChild i`: the `i`-th child of `𝔣^pr` also `↦ s`. -/
noncomputable def treeFixPat (F : FTree) (hF : F ≠ flower) (pat : FixPat) (t s : ℝ)
    (b : GBranch (single F.toTree)) : Option ℝ :=
  if b = F.flowerParent hF then some s else
  match pat with
  | .plain => none
  | .dRoot => if b.1.2 = [] then some t else none
  | .dParent => if (F.flowerParent hF).IsChildOf b then some s else none
  | .dChild i => if b.1.2 = (F.flowerParent hF).1.2 ++ [i] then some s else none

/-- The pattern designates an existing node other than `𝔣^pr` (as `LayeredGarden.PatValid`). -/
def treePatValid (F : FTree) (hF : F ≠ flower) : FixPat → Prop
  | .plain => True
  | .dRoot => (F.flowerParent hF).1.2 ≠ []
  | .dParent => (F.flowerParent hF).1.2 ≠ []
  | .dChild i => (F.flowerParent hF).1.2 ++ [i] ∈ F.toTree.branching

/-- The branch times from the free times (as `Garden.extendFix`). -/
def extendFixT {T : TTree} (fix : GBranch (single T) → Option ℝ)
    (τ : {b : GBranch (single T) // fix b = none} → ℝ) : GBranch (single T) → ℝ :=
  fun b => match h : fix b with
    | some v => v
    | none => τ ⟨b, h⟩

/-- **The time domain with designated nodes** of one tree, all of whose nodes are in layer `p` (as `kDomainFix`
with `up = t`):
- every free node has `p < t_𝔫 < p + 1`, `0 < t_𝔫 < t`;
- `t_{𝔫'} < t_𝔫` for a branching child `𝔫'` of `𝔫` whenever one of the two is free. -/
def treeDomFix (p : ℕ) (T : TTree) (t : ℝ) (fix : GBranch (single T) → Option ℝ) :
    Set (GBranch (single T) → ℝ) :=
  {τ | ∀ b, (fix b = none → (p : ℝ) < τ b ∧ τ b < p + 1 ∧ 0 < τ b ∧ τ b < t) ∧
    ∀ b' : GBranch (single T), b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b}

/-! ## Phases and weights -/

/-- `Ω_𝔫` of a branching node for a lattice decoration. -/
noncomputable def omegaT (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) (c : GBranch (single T)) : ℝ :=
  resFactor (latticePoint L (κ (c.child 0))) (latticePoint L (κ (c.child 1)))
    (latticePoint L (κ (c.child 2))) (latticePoint L (κ c.toNode))

/-- The phase product with the phases at the nodes of `off` removed (as `phaseProdOff`). -/
noncomputable def phaseOffT (T : TTree) (off : Finset (GBranch (single T))) (κ : GNode (single T) → (Fin d → ℤ))
    (τ : GBranch (single T) → ℝ) : ℂ :=
  ∏ c : GBranch (single T), if c ∈ off then 1 else
    Complex.exp ((Real.pi * ((treeSign T c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaT L T κ c * τ c : ℝ) *
      Complex.I)

/-- The stem branching nodes: the proper ancestors of the flower. -/
def OnStemT (F : FTree) (b : GBranch (single F.toTree)) : Prop := b.1.2 <+: F.flowerPath

open Classical in
/-- The `M₁` weight (as `cutWeight1`): `φ_{M₁}` of the largest `|k_ℓ|` over the non-flower leaves. -/
noncomputable def treeCut1 (F : FTree) (j₁ : ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) : ℝ :=
  dyadicCut L j₁ (((Finset.univ.erase F.flowerLeaf).sup fun ℓ => ‖latticePoint L (κ ℓ.toNode)‖₊ : NNReal) : ℝ)

open Classical in
/-- The `M₂` weight (as `cutWeight2`): `φ_{M₂}` of the largest `|Ω_𝔫|` over the stem branching nodes `≠ 𝔣^pr`. -/
noncomputable def treeCut2 (F : FTree) (hF : F ≠ flower) (j₂ : ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ℝ :=
  dyadicCut L j₂ (((Finset.univ.filter fun b : GBranch (single F.toTree) =>
    OnStemT F b ∧ b ≠ F.flowerParent hF).sup fun b => ‖omegaT L F.toTree κ b‖₊ : NNReal) : ℝ)

open Classical in
/-- The `†` weight (as `sibWeight`): the children of `𝔣^pr` other than the flower carry the vectors `c i`. -/
noncomputable def treeSib (F : FTree) (hF : F ≠ flower) (c : Fin 3 → Mom d)
    (κ : GNode (single F.toTree) → (Fin d → ℤ)) : ℝ :=
  ∏ i : Fin 3, if ((F.flowerParent hF).child i).1.2 = F.flowerPath then 1 else
    if latticePoint L (κ ((F.flowerParent hF).child i)) = c i then 1 else 0

/-- The decoration weight: the `M₁` and `M₂` cutoffs and the `†` labels (as in `flowerSum`). -/
noncomputable def treeWeight (F : FTree) (hF : F ≠ flower) (dagger : Option (Fin 3 → Mom d))
    (cut1 cut2 : Option ℕ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) : ℝ :=
  (cut1.elim 1 fun j₁ => treeCut1 L F j₁ κ) * (cut2.elim 1 fun j₂ => treeCut2 L F hF j₂ κ) *
    (dagger.elim 1 fun c => treeSib L F hF c κ)

/-! ## The kernels -/

open Classical in
/-- **The general flower kernel of one flower tree** with input `aP = a(p)` (T (jtflower), with the pattern, `†`
and cutoffs of `flowerest1`/`fixedpoint`; as `kernelKgen` for one tree). For `F ≠ 𝔣`:
`(δ/(2L^{d−γ}))^n ζ(𝒯) ∑_{(k,k')-dec. κ} ε_κ wt(κ) ∫ 1_{𝒟_fix} ∏_{𝔫 ∉ off} e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}
∏_{ℓ≠𝔣} a_{κ_ℓ}(p)^{ζ_ℓ}`. The integral runs over the free times, and `off = {𝔣^pr}` iff `†`. It is `0` for
the trivial tree. -/
noncomputable def flowerKernelGen (p : ℕ) (F : FTree) (aP : (Fin d → ℤ) → ℂ) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ) (k k' : Fin d → ℤ) : ℂ :=
  if hF : F = flower then 0 else
  treePrefactor L γ δ d F.toTree *
    ∑' κ : FlowerDecoration F d k k',
      epsProd F.toTree κ.1.1 * (treeWeight L F hF dagger cut1 cut2 κ.1.1 : ℂ) *
        (∫ τ : {b : GBranch (single F.toTree) // treeFixPat F hF pat t s b = none} → ℝ,
          (treeDomFix p F.toTree t (treeFixPat F hF pat t s)).indicator
            (phaseOffT L γ δ F.toTree (if dagger.isSome then {F.flowerParent hF} else ∅) κ.1.1)
            (extendFixT (treeFixPat F hF pat t s) τ)) *
        ∏ ℓ ∈ Finset.univ.erase F.flowerLeaf,
          zpowSign (treeSign F.toTree ℓ.toNode) (aP (κ.1.1 ℓ.toNode))

/-- The flower trees of each kind (orders in terms of `N_{p+1}`):
- `X`: orders `1, …, N`;
- `Y`: (Y-1)–(Y-2);
- `W`: (W-1)–(W-3).

These are the trees of `Xker`, `Yker`, `Wker`. -/
noncomputable def kindTrees (Ntr : ℕ) : FlowerKind → Finset FTree
  | .X => Xset Ntr
  | .Y => (Yind Ntr).image rootOf
  | .W => (Wind Ntr).image bottomOf

open Classical in
/-- **The random kernel `𝒦^ζ_{kk'}(t,s)`** of kind `kind` (`𝒳`, `𝒴` or `𝒲`, T (operatorxker), L2270–L2273),
with pattern, `†` and cutoffs. It sums `flowerKernelGen` over the trees of the kind with flower sign `ζ` and a
valid pattern. -/
noncomputable def randFlowerKernel (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (kind : FlowerKind) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (k k' : Fin d → ℤ) : ℂ :=
  ∑ F ∈ (kindTrees Ntr kind).filter (fun F => F.sign = ζ ∧ ∃ hF : F ≠ flower, treePatValid F hF pat),
    flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k'

end WaveTurbulence.SysAPI
