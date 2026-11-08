/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.IncohInst.LayerReg.Embed2

/-! # B3s-HELPER8 / ruling R188: the off-stem root-trace gate `RootTraceGate` (STATEMENT ONLY)

**Case (e) of STOP S2** (`MkSlotsO/PROGRESS.md`; B3s's decision in `MkSlots/HANDOFF.md`). Take a `dChild i` pattern on
tree `j₀` whose capped flower parent `F` is a CORE branch (the cap couple at the flower is trivial), pinned at `s`.
Child `i` of `F` is a branching vertex `r`, pinned at `s` by `fixCap … (dChild i)`, in layer `p` (`CapPatValid`).
In the skeleton decomposition `r` is the ROOT of a native object of its own slot, and the clock of that slot at `r`
is `F` (pinned at `s`):
* **chain variant**: skeleton child `i` of `F`'s branch is a branch `γ'` with a nontrivial chain; the slot is
  `.inr γ'`, its native object is the regular paired tree `X(γ')` rooted at `r`, with lone node the core of `γ'`
  (layer `q'`, the lower clock of the slot, free);
* **couple variant**: skeleton child `i` is a leaf; the slot is the leaf pair of that leaf, its native object is a
  regular couple whose tree `j` is rooted at `r`; the other root's clock is free, or the other root is itself the
  pinned `dChild` child of a second core flower parent (both clocks pinned).
The object meets no capped stem node (D2b `offStem_pin_root_tree` / `offStem_pin_root_cpl`: its only pinned vertex is
`r`), so it is not a `ProtShape` object: neither `ProtBoundAt` nor `ProtAnnBoundAt` applies, even per ball. It is
o104 (P8)'s root trace off the stem. On the relaxed domain (R187, β's `kDomainR`) the pinned root keeps no constraint
with its clock, so the slot kernel does not read the pinned clock coordinate; in `kernelProt` this is main's
`kDomainFix` (a pinned branch has no window/upper-time clause).

**`RootTraceBoundAt P`** (per lattice ball; couples with the centre decay `⟨c₀⟩^{-2d}`; star weights, no filters, no dagger — an off-stem object carries no stem
filter, selection shell or capped-flower-parent child; its root's dagger weight is in the core's `restW`):
* (i) **trees** (`w = 1`): a well-formed regular paired tree `X` (nontrivial chain, `X.DecodesTree LG.garden`), layers
  `≤ p`, root in layer `p`, lone node in layer `q' ≤ p`, canonical ambient `ProtAmbient p X LG`; the root pinned at
  `s ∈ (p, p+1)` (`rootPins (fun _ => True) s`), lone-port lower time `ts 1`; on
  `timeBoxGt p q' ∩ {ts 1 < s ∧ s ≤ ts 0}` (the root's clock is the flower parent, pinned at `s`), outputs
  `latticeBall P.L b₀ c₀`, weight `θ = η`: `X^{η,30d,0} ≤ ∏ cω · L^{47d+5} · regBound(n, incoh) · leaf`;
* (ii) **couples** (`w = 2`): a well-formed regular couple `Q` (`Q.Decodes LG.garden`), layers `≤ p`, the roots of the
  trees in a nonempty set `Rt` branching vertices in layer `p` pinned at `s` (`rootPins Rt s`; BOTH roots are pinned
  when the two leaves of the skeleton pair are the `dChild` children of two core flower parents — D2b's
  `offStem_pin_root_cpl` allows exactly the roots), clock windows `q`, `q'` (`timeBox` coordinates: tree `0` reads
  `ts 0`, tree `1` reads `ts 1`, root layers `≤` their windows), canonical signed ambient `CplAmbient p q q' Q LG`
  (D3's `TcCplAmbS`: root signs `+1`, `-1`, root parent layers = the windows `q`, `q'`; F-RT-3); per lattice ball `latticeBall P.L b₀ c₀` WITH the centre decay
  `⟨c₀⟩^{-2d}` (a leaf-pair slot is consumed at every lattice momentum with ball-localized amplitudes and ONE summable
  mass: the decay makes the per-ball masses summable over the unit balls at `latPt x`; it comes from the pieces'
  `⟨k⟩^{30d}` gate weights, D3's `tcWt`; agreed with RT-GATE, which found the global `X^{θ,30d,30d}` form out of reach),
  on the box `timeBox q q' ∩ {s ≤ ts j for the pinned roots j}` (the consumer fixes the clock of a pinned root at the
  flower parent's pin `s`; R176's box for (P1)); weight `θ = η`, and `θ = 1/4` when ONE
  root is pinned (the `SelAdj` variant: the free clock can be the core of a residual selected vertex of another
  tree; with both roots pinned both clocks are capped flower parents, never selected), all at `L^{47d+5}`.
The tree variant is never `SelAdj` (both clocks lie in the `dChild` tree, which carries no selection), so only
`θ = η` is asked there.

Budget (consumer: `genSlotMass` on these slots carries `L^{2(47d+5)}`, `HasProtNative` holds at `r ∈ Π`; the `1/4`
mass carries a further `L^{47d+2}`): `L^{47d+5}` leaves room for the node-ball/lattice-ball covering and the
superposition constants. Templates (D3 internal): `ProtPin.TcTraceUF` (side-couple root trace of (P7), all couple
shapes, `tc2a_trace`), `ProtPin.cfgU_trace_tree` ((P8) trees on the stem), `mirror_tri`, `mirror_low`.

* `rootPins`, `CplAmbient`, **`RootTraceBoundAt`**, **`RootTraceGate := WTPrefix RootTraceBoundAt`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset
open WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.MkSlotsO

/-- The roots of the trees in `Rt` pinned at `s`, nothing else pinned. -/
def rootPins {w : ℕ} {T : Fin w → TTree} (Rt : Fin w → Prop) (s : ℝ) (b : GBranch T) : Option ℝ :=
  if b.1.2 = [] ∧ Rt b.1.1 then some s else none

/-- **The canonical signed ambient of a couple with its clock windows** (D3's `TcCplAmbS` with general windows; F-RT-3):
the couple `Q` is embedded at the positions `a`, `b` of a canonical garden `H` of level `p + 1`, with root signs `+1`,
`-1`, the parent layers of its roots are the clock windows `q`, `q'` (`parAt H p`, as in main's `IsCoherentCoupleAt`:
the coherent pieces of a cut need it for FILT-COH), and it carries the layers of `H`. -/
def CplAmbient (p q q' : ℕ) (Q : RegCpl) (LG : LayeredGarden 2) : Prop :=
  ∃ (w' : ℕ) (H : LayeredGarden w') (a b : Fin w' × TTree.Path), IsCanonGC (p + 1) H ∧ Embeds H.garden Q a b ∧
    nodeSign H.garden.sig a = 1 ∧ nodeSign H.garden.sig b = -1 ∧ parAt H p a = q ∧ parAt H p b = q' ∧
    ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)

/-- **The off-stem root-trace bound at one parameter record** (case (e) of S2, ruling R188). -/
def RootTraceBoundAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ s : ℝ, (p : ℝ) < s → s < p + 1 →
  -- (i) trees: a regular paired tree with its root pinned at `s`, weight `θ = η`
  (∀ (X : RegChain) (LG : LayeredGarden 1), X.wf = true → X.size = 2 * n → X.DecodesTree LG.garden →
    X.lonePath ≠ [] → (∀ a, LG.layer a ≤ p) → LG.layer (GNode.root LG.garden.tree 0) = p →
    ∀ q' : ℕ, q' ≤ p → (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
    ProtAmbient p X LG →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
    ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (b₀ c₀ : Mom P.d),
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt p q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0}) (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
          (fun _ => ts 0) (ts 1) (rootPins (fun _ => True) s) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) *
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) * ENNReal.ofReal (leafSizeProduct LG B)) ∧
  -- (ii) couples: a regular couple with the roots of the trees in `Rt ≠ ∅` pinned at `s`, weight `θ = η`, and
  -- `θ = 1/4` when one root is pinned
  (∀ (Rt : Fin 2 → Prop) (θ : ℝ), (∃ j, Rt j) → (θ = P.η ∨ (θ = 1 / 4 ∧ ¬ (Rt 0 ∧ Rt 1))) →
    ∀ (Q : RegCpl) (LG : LayeredGarden 2), Q.wf = true → Q.size = 2 * n → Q.Decodes LG.garden →
    (∀ a, LG.layer a ≤ p) →
    (∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p) →
    ∀ q q' : ℕ, q ≤ p → q' ≤ p →
    LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
    CplAmbient p q q' Q LG →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
    ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (timeBox q q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
          (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (rootPins Rt s) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * (P.d : ℝ) + 5)) *
          regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B) *
          ENNReal.ofReal ((jbr c₀ ^ (2 * P.d))⁻¹))

/-- **`RootTraceGate`** (ruling R188): the off-stem root-trace bound on the parameter prefix. HELPER8's ONE isolated
hypothesis; to be proved by the D3 session RT-GATE. -/
def RootTraceGate : Prop := WTPrefix RootTraceBoundAt

end WaveTurbulence.Flower.MkSlotsO
