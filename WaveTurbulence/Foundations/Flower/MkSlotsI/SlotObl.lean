/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeavesL
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelSlot
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Piece
public import WaveTurbulence.Foundations.Flower.MkSlots.IntSplit

/-! # B3s-HELPER7 (final assembly): the ONE uniform slot obligation `GenSlotObligation`

The general analogue of `MkSlots.CapSlotObligationAt` (α, cap slots) for EVERY outer slot of the class piece, with
the member's pins, per-slot factors and lower-bound convention of the general chain:

* the slot kernel is β's relaxed pinned weighted slot kernel `MkSlotsB.slotFnGWFRL` (R187 form: a pinned object top
  keeps no top/clock constraint inside the slot, it sits in the core domain through `lbGen`), with
  - the anchored profiles `MkSlots.anchProfiles` (cap pairs: the indicator of the cap momentum),
  - the node weight `MkSlots.chainW` (frontier cutoffs × the node-local dagger weight off the "case b" nodes — the core
    of a capped flower parent and its non-flower children, whose dagger weight is the skeleton-level constant ×
    indicator `restW` of the α split; on a cap pair it is `capNodeW`, `MkSlots.IntMember.slotFn_chainW_cap`),
  - the intrinsic pins `fixCap … pat` (all patterns),
  - the per-slot factor `genΘs`: over the non-core native nodes of the slot, the stem node weight `genNW` (σ's dyadic
    filters and δ's selection shells, radii `MkSlotsG.radRaw`, times the selected filter `chiD(|Ω|/Rs)` at a
    selected vertex; `Ω` of the native garden at the slot momentum), as in δ's `MkSlotsS.selΘs`;
  (`genSlotKer`);
* the box `genSlotBox`: every clock coordinate whose clock is pinned (a root clock: the top time `t`; a pinned core
  branch: its pin) is fixed at that value, and if some clock is free the point lies in main's `slotBox` (this is
  F-H3-2's box for root-pinned cap objects, and contains the pinned point `(s, s)` of a chain slot whose two clocks
  are pinned — β's `dParent` parent/child pair);
* the top-pin cut (revision 5, HELPER8 S5, pre-approved): the HasSum is asked only at the slot times satisfying
  `TopCut` (every pinned native top is at most the clock of its side) — the R187 constraint on the consumed times;
* the momenta (revision 3, HELPER8 S3): only the momenta the chain consumes, the lattice points
  `latticePoint L n` (coset base `0`); on a cap pair only the cap momentum (`n = roots j`, as `CapSlotObligationAt`),
  on the chain slot of a skeleton ROOT branch `β` only its root label (`n = roots β.1.1`, revision 2, HELPER8 S2(a));
* the centres (revision 3, B3s's ruling on HELPER8 S2): the family may depend on a node centre `x : Fin d → ℤ`
  (quantified BEFORE the family); on the chain slot of a NON-root branch the HasSum is asked only at the momenta in
  the node ball `‖latticePoint L n - latPt d x‖ ≤ 1` of `x` (the support of main's node partition piece
  `RepAnalytic.chi d x`, `norm_sub_le_one_of_chi_ne_zero`), with masses uniform in `x`; on leaf-pair and root chain
  slots `x` is a dummy (the assembly uses `x = 0`); plain, nil and filtered chains supply their global family for
  every `x`;
* the amplitudes: `SlotFam`-compatible (`‖amp‖ ≤ 1`, `SNorm (30d) 0 ≤ 1`), localized within distance `1` of a lattice
  centre ON LEAF-PAIR SLOTS ONLY, as main's `Represents.SlotFam.a_supp` (revision 2, HELPER8 S1: on a chain slot whose
  kernel is constant, e.g. a nil chain, no localized summable family exists);
* the mass `genSlotMass`: the B3 slot mass `(C√δ)^{size} · L^{-η⁸·incoh} · c_F^{nr} · leaf` (leaf factor without the
  anchored pair, `b⁻¹ · slotLeaf`, on a cap pair), times the protected loss `L^{2(47d+5)}` (D6's `L^{(47d+5)r}`,
  `r ≤ 2`; D3's `L^{31d+6}` is smaller) when the slot carries a node of the protected set `Π` as a non-core native
  node (`HasProtNative`), times the gain `∏ Rs_{j(v)}^{-1/18}` over the selected native vertices of the slot (δ's
  `selNative`, `selMassMK`'s absorbed selections);
* for a slot one of whose clocks is the core of a selected vertex (`SelAdj`; the selected vertex is then a residual
  selected atom of `G_sb`), the `X^{1/4}`-type moment bound at the extra cost `L^{47d+2}` INSTEAD of the `η` bound
  (revision 4, HELPER8 S4: the gates give the two exponents through different near-optimal extensions; δ's engine
  reads one exponent per slot, `θs = 1/4` there, and `RepresentsIntMKSel`'s `L^{7(47d+2)#sel}` pays the loss); the
  `η` bound is asked on the other slots.

The slots are the OUTER slots of the class piece (`G_sb = (stA mkF a).G`, slots `iota s'` through main's splice shape
`shapeRep mkF a`) at a prescribed point `a` satisfying the hypotheses that the representative of a non-zero class has
in `ClassRepGen` (canonical, capped geometry, valid patterns, irreducible, `|J| = R`, times, selections on plain trees,
fine marking, stem-clean when the weight is stem dependent, high roots, profile/frontier bounds).

**`GenSlotObligation`** `:= ∃ Kg, (∀ d η, 1 ≤ Kg d η) ∧ WTPrefix (GenSlotObligationAt Kg)` is the only hypothesis of
`MkSlotsI.classRepGen_prefix_of`. It is to be proved (another helper) from the kind-specific obligations: B3's plain
slots (`MkUnits.vine_slot_dataWMk`), `MkSlots.capSlotObligation` (cap pairs, plain pins), β's B5 (pattern pins, pinned
chain slots), γ's T3 (filtered slots), δ's S3 (`MkSlotsS.SelSlotObligation`, selected slots). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles recLG IsCapPair capTreeOf stA fixCore)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-! ## The stem node weight and the per-slot factor -/

/-- **The general stem node weight** at a node `z` of `LG` with resonance value `x`: on a capped-stem branch `b`, σ's
dyadic filters and the selection shells at the radii `MkSlotsG.radRaw … b` (`radProd`), times the selected filter
`chiD(|x|/Rs)` if `b` is a selected vertex; `1` elsewhere. The product over the stem branches is
`stemFilterCap · selWeightCap` up to the constant `∏ Rs_j⁻¹` (`MkSlotsG.stemFilterCap_mul_selWeightCap`). -/
def genNW (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (z : GNode LG.garden.tree) (x : ℝ) : ℂ :=
  if h : z.1.2 ∈ (LG.garden.tree z.1.1).branching then
    if ∃ j, (⟨z.1, h⟩ : GBranch LG.garden.tree) ∈ stemSetCap LG J j then
      (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs ⟨z.1, h⟩) x : ℂ) *
        (if (⟨z.1, h⟩ : GBranch LG.garden.tree) ∈ selSetCap LG J kSel then
          ((chiD (|x| / Rs z.1.1) : ℝ) : ℂ) else 1)
    else 1
  else 1

section Slots

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
  (Rs : Fin w → ℝ)

/-- **The general per-slot factor** (β's `Θs`): over the non-core native nodes of the slot, the general stem node
weight at the resonance factor of the native garden at the slot momentum `k` (δ's `selΘs` with `genNW`). -/
def genΘs : (sl : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d sl → ℂ
  | .inl p => fun k κ => ∏ a : GNode (nativeCoupleGarden D hS p).tree,
      if ∃ β : GBranch S.tree, (nativeCoupleForest D hS p).nodeEmbedding a = (D.coreBranch hS β).toNode then 1
      else genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
        ((nativeCoupleForest D hS p).nodeEmbedding a)
        (MkSlotsS.omegaAt (cosetDecoration (nativeCoupleGarden D hS p) L k κ.1) a)
  | .inr b => fun k κ => ∏ a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree,
      if ∃ β : GBranch S.tree, chainContextNode D hS b a = (D.coreBranch hS β).toNode then 1
      else genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (chainContextNode D hS b a)
        (MkSlotsS.omegaAt (cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L k κ.1) a)

/-- The slot carries a node of the protected set `Pi` as a non-core native node. -/
def HasProtNative (Pi : Finset (GNode (layeredReconstruction D hS layer hLayer).garden.tree))
    (sl : ReplacementSlot S) : Prop :=
  ∃ a : NativeNode D sl, (∀ β : GBranch S.tree, nativeNodeAt D hS sl a ≠ (D.coreBranch hS β).toNode) ∧
    ∃ z ∈ Pi, z.1 = (nativeNodeAt D hS sl a).1

/-- One clock of the slot is a skeleton branch whose core is a selected vertex (a residual selected atom). -/
def SelAdj (sl : ReplacementSlot S) : Prop :=
  ∃ (i : Fin 2) (β : GBranch S.tree), argSrc hS sl i = Sum.inr β ∧
    ∃ v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel, v.1 = (D.coreBranch hS β).1

end Slots

/-- The pin of a clock source: the top time at a root clock, the core pin at a branch clock. -/
def clkPin {S : Garden w} (tt : Fin w → ℝ) (fixC : GBranch S.tree → Option ℝ) : ClkSrc S → Option ℝ
  | .inl j => some (tt j)
  | .inr b => fixC b

/-- **The general slot box**: pinned clock coordinates at their pins; if some clock is free, main's `slotBox`. -/
def genSlotBox {S : Garden w} (p : ℕ) (layer0 : GBranch S.tree → ℕ) (hS : S.IsPlain) (tt : Fin w → ℝ)
    (fixC : GBranch S.tree → Option ℝ) (sl : ReplacementSlot S) : Set (Fin 2 → ℝ) :=
  {ts | (∀ (i : Fin 2) (v : ℝ), clkPin tt fixC (argSrc hS sl i) = some v → ts i = v) ∧
    ((∃ i : Fin 2, clkPin tt fixC (argSrc hS sl i) = none) → ts ∈ slotBox p layer0 hS sl)}

/-- The protected loss exponent of a slot carrying protected native nodes: D6's `(47d+5)·r`, `r ≤ 2`. -/
def genLossExp (d : ℕ) : ℝ := 2 * (47 * (d : ℝ) + 5)

/-- **The general slot kernel** of a slot of the reconstruction of `a`. -/
def genSlotKer (L γ δ : ℝ) (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    (t s : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) :
    ReplacementSlot a.prime.skeleton → (Fin 2 → ℝ) → Mom d → ℂ :=
  MkSlotsB.slotFnGWFRL a.prime.data a.prime.prime.1 L γ δ (anchProfiles J (recLG a) h L roots)
    (MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ p s J Rf dag)
    (genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs)
    (sourceLayer a) (sourceLayer_isLayering a) (fixCap (recLG a) J pat t s)

/-- The box of a slot of the reconstruction of `a` (top time `t`, core pins of `fixCap … pat`). -/
def genBoxAt (p : ℕ) (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (sl : ReplacementSlot a.prime.skeleton) : Set (Fin 2 → ℝ) :=
  genSlotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
    (fun _ => t) (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s)) sl

/-- **The top-pin cut** (revision 5, HELPER8 S5, pre-approved by wt-orch; R187): at every pinned native top (a root of
the native object, pinned at `v` by `fixCap … pat`) the clock of its side is at least `v`. On the consumed slot times
this always holds: a pinned clock carries a pin `≥ v` (pins are monotone along ancestry, `RelaxPins.mono`), a root clock
is `t ≥ v`, and a free clock carries R187's lower bound `lbGen = s = v` (the core domain has `τ_π > s`). It is the
constraint R187 moved into the core domain; on the cap side it is β's `capPatBox` clause (R176's `cfg.box`, F-H3-2). -/
def TopCut {w : ℕ} (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) :
    (sl : ReplacementSlot a.prime.skeleton) → (Fin 2 → ℝ) → Prop
  | .inl q => fun ts => ∀ (b : GBranch (decodedCouple (a.prime.data.couple q)).tree) (v : ℝ), b.1.2 = [] →
      MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inl q) b = some v → v ≤ ts b.1.1
  | .inr β => fun ts => ∀ (b : GBranch (decodedTree (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree)
      (v : ℝ), b.1.2 = [] → MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inr β) b =
        some v → v ≤ ts 0

/-- The leaf factor of a slot: `b⁻¹ · slotLeaf` on a cap pair (the anchored pair has no profile), `slotLeaf` else. -/
def genLeaf {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (b : ℝ) :
    ReplacementSlot a.prime.skeleton → ℝ
  | .inl q => (if IsCapPair a.prime.skeleton a.prime.prime.1 J q then b⁻¹ else 1) *
      slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q)
  | .inr β => slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inr β)

/-- **The mass of a slot** (without the constant `Kg`). -/
def genSlotMass (P : WTParams) (C b : ℝ) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (sl : ReplacementSlot a.prime.skeleton) : ℝ :=
  (C * Real.sqrt P.δ) ^ slotSize a.prime.data sl *
    P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      sl : ℝ)) *
    (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 sl * genLeaf a J b sl) *
    P.L ^ (if HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) sl then genLossExp P.d else 0) *
    ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl,
      Rs v.1.1 ^ (-(1 / 18 : ℝ))

/-- **The general slot obligation at one parameter record** (constant `Kg d η`). For every `C ≥ C₁`, every
prescribed point `a` with the hypotheses of the representative of a non-zero class in `ClassRepGen`, every outer slot
`iota s'` of the class piece: a countable family of modes with `SlotFam`-compatible amplitudes such that on the box
`genBoxAt` the general slot kernel is `Σ_l wt l · amp l k · e(m l · ts)` at the lattice momenta `k = latticePoint L n`
(the cap momentum only, on a cap pair; the root label only, on a root chain slot; the node ball of the centre `x`
only, on a non-root chain slot; ball-localized amplitudes on leaf-pair slots only), with `1/4`-moment mass
`≤ Kg · L^{47d+2} · genSlotMass` if a clock of the slot is the core of a selected vertex (`SelAdj`), and `η`-moment
mass `≤ Kg · genSlotMass` otherwise (revision 4). -/
def GenSlotObligationAt (Kg : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  ∀ C : ℝ, P.C₁ ≤ C →
  ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (t s : ℝ),
    p < P.D → IsCanonGC (p + 1) a.layered → a.prime.data.size ≤ P.N (p + 1) ^ 4 → J.card = R →
    CapGeo a.layered J p → CapPatValid a.layered J pat p → a.layered.garden.Irreducible →
    t ∈ Ioo (p : ℝ) (p + 1) → s ∈ Ioo (p : ℝ) t →
  ∀ (kSel : Fin (2 * R) → Option ℕ), (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
  ∀ (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ), (∀ j, P.L ≤ Rs j) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
    (¬ StemDep σ kSel ∨ CleanPt J a) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ), (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
  ∀ (s' : ReplacementSlot (stA mkF a).G) (sl : ReplacementSlot a.prime.skeleton),
    sl = (MkSlotsT.shapeRep mkF a).iota a.prime.prime.1 ((stA mkF a).plain a.prime.prime.1) s' →
  ∀ x : Fin P.d → ℤ,
  ∃ (Λ : Type) (_ : Countable Λ) (wt : Λ → ℝ) (m : Λ → Fin 2 → ℤ) (c : Λ → Fin P.d → ℤ)
    (amp : Λ → Mom P.d → ℂ),
    (∀ l, 0 ≤ wt l) ∧ Summable wt ∧ (∀ l k, ‖amp l k‖ ≤ 1) ∧ (∀ l, SNorm (30 * P.d) 0 (amp l) ≤ 1) ∧
    (∀ q, sl = .inl q → ∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
    (∀ ts ∈ genBoxAt p a J pat t s sl, TopCut a J pat t s sl ts → ∀ n : Fin P.d → ℤ,
      (∀ q, sl = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
        n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 = [] → n = roots β.1.1) →
      (∀ β : GBranch a.prime.skeleton.tree, sl = .inr β → β.1.2 ≠ [] →
        ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
      HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L n) * fsPhase (m l) ts)
        (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag sl ts (latticePoint P.L n))) ∧
    (¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs sl)) ∧
    (SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl →
      ∑' l, maxBracketPow (1 / 4) (half (m l)) * ENNReal.ofReal (wt l) ≤
        ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs sl))

/-- **`GenSlotObligation`** — the ONE isolated hypothesis of the general assembly (B3s-HELPER7). -/
def GenSlotObligation : Prop :=
  ∃ Kg : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ Kg d η) ∧ WTPrefix (GenSlotObligationAt Kg)

/-- The per-record obligation is monotone in the large constants (it reads `C₁` only through `C ≥ C₁`). -/
theorem genSlotObligationAt_mono (Kg : ℕ → ℝ → ℝ) : LargeConstantMonotone (GenSlotObligationAt Kg) := by
  intro P c₁ c₂ _ _ _ _ h₁ _ h C hC R p a J pat t s hp hcan hsz
  exact h C (h₁.trans hC) (R := R) (p := p) a J pat t s hp hcan (by rw [← vineEstHalfMK_N P c₁ c₂ (p + 1)]; exact hsz)

end WaveTurbulence.Flower.MkSlotsI
