/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.Fam
public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsI.CoreW5
public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember2
public import WaveTurbulence.Foundations.Flower.MkUnitsL.ClassSumL
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR1

/-! # B3s-HELPER7 AsmI (phase 1): the interface `ClassCentreIdentityAt` between the class identity and the assembly

The final per-record assembly `classRepGen_at : … → ClassCentreIdentityAt Kg P' → … → MkSlotsG.ClassRepGen 452 P''`
applies HELPER9's engine `MkSlotsE.centreEngine : CentreEngine` (W:MkSlotsI/CentreForm.lean, W:MkSlotsE/Engine.lean
`representsIntMKSel_of_centreModes`, `repMK_of_centreModes`) to the general piece `MkSlotsG.pieceGen` transported to
B3's unit marking. This file fixes every quantity the engine reads, so that the class identity (`hval`) can be proved
separately from the member chain and consumed verbatim by the assembly.

## The general piece at a marked set
B3's chain runs the units at a marking function `mkU` with `mkU a.prime = classMk mkF a` only propositionally (α's
`obtain ⟨mkU, hset, hout⟩`, W:MkSlots/IntAsm4.lean). As α's `MkSlots.pieceAt` (W:MkSlots/IntPiece.lean), the general
piece is restated with the marked set `Mk` explicit:
`selRAt`, `filtGenAt`, `indGenAt`, `PinTopBelowAt`, `lbGenAt`, **`pieceGenAt`** (α's `coreAt`, `protAt`, `fixAt`,
`flwAt`, `sibIndAt` for the rest). At `Mk = classMk mkF a` they are `MkSlotsG.selRGen`, …, `MkSlotsG.pieceGen` by
`rfl` (**`pieceGenAt_classMk`**, `selRAt_classMk`). Transport along `Mk = Mk'`:
**`representsIntMKSel_pieceGenAt_congr`**, `representsIntMK_pieceGenAt_congr`, `selRAt_image_congr`.
**`zatomG_mul_sibIndAt`**: CoreW's `zatomG_mul_sibInd` at a marked set `Mk = classMk mkF a` (the source of the class
constant `chiDNorm ^ #selR`).

## The slot data (`SlotDataOK`)
`iotaAt a Mk s'` is main's `stShape … Mk` slot map. **`SlotDataOK Kg P C p a J … dag Mk sd`** is the conclusion of
`GenSlotObligationAt Kg P` (W:MkSlotsI/SlotObl.lean, revision 4) at the point `a`, for the slot data
`sd : ReplacementSlot G_sb → (Fin d → ℤ) → SlotDatum d` (W:MkSlotsI/Fam.lean) at every outer slot `s'` and centre `x`:
leaf-pair localization (`supp`), the superposition on `genBoxAt` at the consumed lattice momenta (`hasSum`), the
`η`-moment mass off `SelAdj` (`massEta`) and the `1/4`-moment mass on `SelAdj` (`massSel`). **`exists_slotDataOK`**:
the obligation provides such data at every marked set `Mk = classMk mkF a` (in particular at `mkU a.prime`).
`fam₀Of sd hsupp = famOfData (sd · 0)`: the leaf-pair / root-chain family (centre `0`); `famCOfData sd`: the chain
pieces at the centred slots.

## The class data
* `centreForm`: the right-hand side of `CentreEngine`'s `hval`, VERBATIM, as a function of the engine's data;
* `domOf π tt = splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ lbDomR π.lb` (VBC's domain form; `= fixLB`,
  `domOf_eq_fixLB`, so the engine's `hsliceD` is `Iff.rfl`);
* **`sgnGen`** `= capConstO a mk … · selOK(a) · selConst(a) · chiDNorm ^ #selRAt` (the class constant) and
  **`norm_sgnGen_le`**: `‖sgnGen‖ ≤ (∏_{kSel j ≠ none} Rs_j⁻¹) · chiDNorm ^ #selR`;
* **`unitKerGen`**: the class kernels `MkUnitsL.unitHkFWL P p (SURep a mk J (radTGen …) j) (sourceAssemblyMk a mk j) …
  (frontierG ∘ Rf) (unitProfile … h j) 0`;
* `classCentreRHS`: `centreForm` at these data (one class term, `I = Unit`).

**`ClassCentreIdentityAt Kg P`**: for every class (the binders of `ClassRepGen`), every unit marking `mkU` with
`hset`/`hout`, and every `sd` with `SlotDataOK … (mkU a.prime) sd`: `classValue … = classCentreRHS …`. The prover
(next phase) proves `∀ Kg P, ClassCentreIdentityAt Kg P` from the member chain; the assembly feeds it as `hval`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.RedSplice (stSt unitBlocks)
open WaveTurbulence.Flower.MkSlots (IsCapPair capTreeOf outerValMμD fixMeasure coreAt protAt fixAt flwAt sibIndAt
  recLG)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-! ## The general piece at a marked set -/

section PieceAt

/-- **The residual selected atoms at a marked set `Mk`** (δ's `MkSlotsS.selROf` with the marked set explicit): the
atoms of `G_sb = (stSt a.prime.skeleton a.totalSigma Mk).G` whose core branch is a selected vertex. -/
def selRAt (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) : Finset (GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree) :=
  univ.filter fun c => coreAt a Mk c ∈ selSetCap a.layered J kSel

/-- **The atom filters at a marked set `Mk`** (`MkSlotsG.filtGen` with the marked set explicit; main's splice shape
`stShape … Mk`). -/
def filtGenAt (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (c : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree) : Option (ℝ × SchwartzMap ℝ ℂ) :=
  if c ∈ selRAt J kSel a Mk then some (Rs c.1.1, MkSlotsS.chiDNS)
  else MkSlotsT.filtStem a.prime.data a.prime.prime.1
    (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
    (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
    (sourceLayer a) (sourceLayer_isLayering a) J (MkSlotsG.radGen (MkSlotsG.recA a) J L σ kSel Rs)
    (MkSlotsG.one_le_radGen (MkSlotsG.recA a) J L σ kSel Rs) c

/-- **The indicator at a marked set `Mk`** (`MkSlotsG.indGen`): α's dagger sibling indicator `sibIndAt` times σ's
filter at the residual selected atoms. -/
def indGenAt {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (dag : Option (Fin w → Fin 3 → Mom d))
    (k : GNode (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Mom d) : ℝ :=
  sibIndAt J a Mk dag (flwAt J a Mk) k *
    ∏ v ∈ selRAt J kSel a Mk,
      MkSlotsT.radProd (MkSlotsT.radSigma L σ v) (omegaNode (stSt a.prime.skeleton a.totalSigma Mk).G k v)

/-- The pinned object tops below an atom `c` at a marked set `Mk` (`MkSlotsG.PinTopBelow`). -/
def PinTopBelowAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (c : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree)
    (u : GBranch a.layered.garden.tree) : Prop :=
  (fixCap a.layered J pat t s u).isSome ∧ u.IsChildOf (coreAt a Mk c) ∧
    ∀ c' : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree, coreAt a Mk c' ≠ u

/-- **The lower bounds at a marked set `Mk`** (`MkSlotsG.lbGen`, ruling R187). -/
def lbGenAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (c : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree) :
    Option ℝ :=
  if pat c.1.1 = FixPat.dParent ∧ fixAt J pat t s a Mk c = none ∧ ∃ u, PinTopBelowAt J pat t s a Mk c u
  then some s else none

/-- **The general piece at a marked set `Mk`** (`MkSlotsG.pieceGen` with the marked set explicit). -/
def pieceGenAt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    Stage1PieceMK P.d R :=
  MkSubpro.stage1PieceMKOf P a.prime.prime.1 a.layered a.prime.decodes a.totalSigma Mk
    (protAt J pat t s kSel a Mk) (protI a.layered J pat t s kSel).card (fixAt J pat t s a Mk)
    (filtGenAt J P.L σ kSel Rs a Mk) (indGenAt J P.L σ kSel a Mk dag) (lbGenAt J pat t s a Mk)

/-- At B4's class marking the residual selected atoms are `MkSlotsG.selRGen` (definitionally). -/
theorem selRAt_classMk (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) : selRAt J kSel a (classMk mkF a) = MkSlotsG.selRGen J kSel mkF a := rfl

/-- **At B4's class marking the piece is `MkSlotsG.pieceGen`** (definitionally). -/
theorem pieceGenAt_classMk (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    pieceGenAt P J pat t s kSel σ Rs a (classMk mkF a) dag = MkSlotsG.pieceGen P J pat t s kSel σ Rs mkF a dag :=
  rfl

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))

/-- **A selected representation by the piece at `Mk` is one at every equal marked set** (α's
`representsIntMK_pieceAt_congr` for `RepresentsIntMKSel`, the residual selected atoms transported along). -/
theorem representsIntMKSel_pieceGenAt_congr {Mk Mk' : Set (Stage1.CLVine a.prime.skeleton)} (hMk : Mk = Mk')
    {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {m : ℝ}
    {val : ℂ}
    (h : RepresentsIntMKSel (pieceGenAt P J pat t s kSel σ Rs a Mk dag) (selRAt J kSel a Mk) n cP tt base roots m
      val) :
    RepresentsIntMKSel (pieceGenAt P J pat t s kSel σ Rs a Mk' dag) (selRAt J kSel a Mk') n cP tt base roots m
      val := by
  subst hMk
  exact h

/-- A representation by the piece at `Mk` is one at every equal marked set. -/
theorem representsIntMK_pieceGenAt_congr {Mk Mk' : Set (Stage1.CLVine a.prime.skeleton)} (hMk : Mk = Mk')
    {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {m : ℝ}
    {val : ℂ} (h : (pieceGenAt P J pat t s kSel σ Rs a Mk dag).RepresentsIntMK n cP tt base roots m val) :
    (pieceGenAt P J pat t s kSel σ Rs a Mk' dag).RepresentsIntMK n cP tt base roots m val := by
  subst hMk
  exact h

/-- The selected trees (the image of the residual selected atoms) do not depend on the marked set's presentation. -/
theorem selRAt_image_congr {Mk Mk' : Set (Stage1.CLVine a.prime.skeleton)} (hMk : Mk = Mk') :
    (selRAt J kSel a Mk).image (fun v => v.1.1) = (selRAt J kSel a Mk').image (fun v => v.1.1) := by
  subst hMk
  rfl

/-- **The atom weight of `G_sb` at a marked set `Mk = classMk mkF a`** (CoreW's `zatomG_mul_sibInd`, transported):
`zatomG z · sibIndAt (coset z) = chiDNorm ^ #selRAt · pieceAtomW (pieceGenAt …) (coset z)`. -/
theorem zatomG_mul_sibIndAt (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (z : GenDecoration (stSt a.prime.skeleton a.totalSigma Mk).G P.d roots 0) :
    zatomG J P.L σ kSel Rs a Mk z *
        ((sibIndAt J a Mk dag (flwAt J a Mk) (cosetDecoration (stSt a.prime.skeleton a.totalSigma Mk).G P.L 0 z.1) :
          ℝ) : ℂ) =
      (chiDNorm : ℂ) ^ (selRAt J kSel a Mk).card *
        MkSlotsS.pieceAtomW (pieceGenAt P J pat t s kSel σ Rs a Mk dag)
          (cosetDecoration (stSt a.prime.skeleton a.totalSigma Mk).G P.L 0 z.1) := by
  subst hMk
  exact zatomG_mul_sibInd P J pat t s kSel σ Rs mkF a dag hsub hL hRs z

end PieceAt

/-! ## The slot data -/

section Slots

/-- The skeleton slot of an outer slot `s'` of the spliced garden at `Mk` (main's splice shape `stShape … Mk`; at
`Mk = classMk mkF a` the slot `(MkSlotsT.shapeRep mkF a).iota … s'` of `GenSlotObligationAt`). -/
abbrev iotaAt (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) : ReplacementSlot a.prime.skeleton :=
  (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).iota a.prime.prime.1
    ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1) s'

/-- **The conclusions of `GenSlotObligationAt Kg P` at the point `a`, for the slot data `sd`** (at every outer slot
`s'` of the spliced garden at the marked set `Mk` and every node centre `x`; revision 4 of W:MkSlotsI/SlotObl.lean,
the existential data of `∃ Λ … amp` being `sd s' x`):
* `supp`: the amplitudes of the leaf-pair slots are localized within distance `1` of their centres;
* `hasSum`: on the box `genBoxAt`, at the lattice momenta `latticePoint L n` consumed by the chain (the cap momentum on
  a cap pair, the root label on a root chain slot, the node ball of `x` on a non-root chain slot), the general slot
  kernel `genSlotKer` is the superposition `Σ_l w_l · a_l(k) · e(m_l · ts)`;
* `massEta`: off `SelAdj`, the `η`-moment mass is at most `Kg · genSlotMass`;
* `massSel`: on `SelAdj`, the `1/4`-moment mass is at most `Kg · L^{47d+2} · genSlotMass`. -/
structure SlotDataOK (Kg : ℕ → ℝ → ℝ) (P : WTParams) (C : ℝ) {R : ℕ} (p : ℕ) (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (b : ℝ) (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G → (Fin P.d → ℤ) → SlotDatum P.d) : Prop where
  supp : ∀ q x l k, (sd (Sum.inl q) x).a l k ≠ 0 → ‖k - latPt P.d ((sd (Sum.inl q) x).n l)‖ ≤ 1
  hasSum : ∀ s' x, ∀ ts ∈ genBoxAt p a J pat t s (iotaAt a Mk s'), TopCut a J pat t s (iotaAt a Mk s') ts → ∀ n : Fin P.d → ℤ,
    (∀ q, iotaAt a Mk s' = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
      n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
    (∀ β : GBranch a.prime.skeleton.tree, iotaAt a Mk s' = .inr β → β.1.2 = [] → n = roots β.1.1) →
    (∀ β : GBranch a.prime.skeleton.tree, iotaAt a Mk s' = .inr β → β.1.2 ≠ [] →
      ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
    HasSum (fun l => ((sd s' x).w l : ℂ) * (sd s' x).a l (latticePoint P.L n) * fsPhase ((sd s' x).m l) ts)
      (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (iotaAt a Mk s') ts (latticePoint P.L n))
  massEta : ∀ s' x,
    ¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk s') →
    ∑' l, maxBracketPow P.η (half ((sd s' x).m l)) * ENNReal.ofReal ((sd s' x).w l) ≤
      ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (iotaAt a Mk s'))
  massSel : ∀ s' x,
    SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk s') →
    ∑' l, maxBracketPow (1 / 4) (half ((sd s' x).m l)) * ENNReal.ofReal ((sd s' x).w l) ≤
      ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) *
        genSlotMass P C b a J pat t s kSel Rs (iotaAt a Mk s'))

/-- **The obligation provides the slot data at every marked set equal to the class marking** (in particular at the
unit marking `mkU a.prime`, `hset`): `GenSlotObligationAt` + `exists_slotData`. -/
theorem exists_slotDataOK {Kg : ℕ → ℝ → ℝ} {P : WTParams} (hobl : GenSlotObligationAt Kg P) (C : ℝ)
    (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (hp : p < P.D) (hcan : IsCanonGC (p + 1) a.layered)
    (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4) (hJ : J.card = R) (hGeo : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p) (hirr : a.layered.garden.Irreducible) (ht : t ∈ Ioo (p : ℝ) (p + 1))
    (hs : s ∈ Ioo (p : ℝ) t) (kSel : Fin (2 * R) → Option ℕ) (hpl : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j) (mkF : Stage1Mk.MarkFn (2 * R))
    (hmk : FineMarking J pat t s kSel σ mkF) (hstem : ¬ StemDep σ kSel ∨ CleanPt J a)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hsn : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
    (hhigh : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (hMk : Mk = classMk mkF a) :
    ∃ sd, SlotDataOK Kg P C p a J pat t s kSel σ Rs roots h b Rf dag Mk sd := by
  subst hMk
  obtain ⟨sd, hsd⟩ := exists_slotData (G := (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G) (d := P.d)
    (fun s' x Λ wt m c amp =>
      (∀ q, iotaAt a (classMk mkF a) s' = .inl q → ∀ l k, amp l k ≠ 0 → ‖k - latPt P.d (c l)‖ ≤ 1) ∧
      (∀ ts ∈ genBoxAt p a J pat t s (iotaAt a (classMk mkF a) s'), TopCut a J pat t s (iotaAt a (classMk mkF a) s') ts → ∀ n : Fin P.d → ℤ,
        (∀ q, iotaAt a (classMk mkF a) s' = .inl q → IsCapPair a.prime.skeleton a.prime.prime.1 J q →
          n = roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) →
        (∀ β : GBranch a.prime.skeleton.tree, iotaAt a (classMk mkF a) s' = .inr β → β.1.2 = [] →
          n = roots β.1.1) →
        (∀ β : GBranch a.prime.skeleton.tree, iotaAt a (classMk mkF a) s' = .inr β → β.1.2 ≠ [] →
          ‖latticePoint P.L n - latPt P.d x‖ ≤ 1) →
        HasSum (fun l => (wt l : ℂ) * amp l (latticePoint P.L n) * fsPhase (m l) ts)
          (genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (iotaAt a (classMk mkF a) s') ts
            (latticePoint P.L n))) ∧
      (¬ SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
          (iotaAt a (classMk mkF a) s') →
        ∑' l, maxBracketPow P.η (half (m l)) * ENNReal.ofReal (wt l) ≤
          ENNReal.ofReal (Kg P.d P.η * genSlotMass P C b a J pat t s kSel Rs (iotaAt a (classMk mkF a) s'))) ∧
      (SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
          (iotaAt a (classMk mkF a) s') →
        ∑' l, maxBracketPow (1 / 4) (half (m l)) * ENNReal.ofReal (wt l) ≤
          ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) *
            genSlotMass P C b a J pat t s kSel Rs (iotaAt a (classMk mkF a) s'))))
    (fun s' x => hobl C hC a J pat t s hp hcan hsz hJ hGeo hpat hirr ht hs kSel hpl σ Rs hRs mkF hmk hstem roots h b
      hb hsn Rf hRf hhigh dag s' _ rfl x)
  exact ⟨sd, ⟨fun q x l k hk => (hsd (.inl q) x).1 _ rfl l k hk, fun s' x => (hsd s' x).2.1,
    fun s' x => (hsd s' x).2.2.1, fun s' x => (hsd s' x).2.2.2⟩⟩

/-- **The leaf-pair / root-chain family of the slot data** (centre `0`): `famOfData (sd · 0)`. On the centred slots
its modes are kept at weight `0` by `famX`. -/
def fam₀Of {G : Garden w} {d : ℕ} (sd : ReplacementSlot G → (Fin d → ℤ) → SlotDatum d)
    (hsupp : ∀ q x l k, (sd (Sum.inl q) x).a l k ≠ 0 → ‖k - latPt d ((sd (Sum.inl q) x).n l)‖ ≤ 1) :
    SlotFam G d :=
  famOfData (fun s' => sd s' 0) (fun q l k hk => hsupp q 0 l k hk)

end Slots

/-! ## The class data -/

section ClassData

/-- **The centre-indexed outer mode form**: the right-hand side of `CentreEngine`'s `hval` (W:MkSlotsI/CentreForm.lean),
verbatim, as a function of the engine's data. `CentreEngine`'s `hval` is `val = centreForm π hS tt base roots selSk Dom
route hclk hmom sgn fam₀ famC HkM` (definitionally). -/
def centreForm {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (Dom : Set (GBranch π.Gsb.tree → ℝ)) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J) (hclk : J → Fin 3 → ClkSrc π.Gsb)
    (hmom : J → Fin 4 → GNode π.Gsb.tree) {I : Type} [Fintype I] (sgn : I → ℂ) (fam₀ : I → SlotFam π.Gsb P.d)
    (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) : ℂ :=
  ∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
    ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t, (((∏ t, (famX (fam₀ i) (famC i) X).w t (ξ t) : ℝ)) : ℂ) *
      outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => MkSlotsS.pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
          chiX P.L base X z) hS
        (fixMeasure π.fix)
        (fun t => (famX (fam₀ i) (famC i) X).a t (ξ t)) (fun t => (famX (fam₀ i) (famC i) X).m t (ξ t))
        route hclk hmom (HkM i)

/-- **The time domain of a piece**: `splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ lbDomR π.lb` (the form of VBC's
`hasSum_sigma_centred`). -/
def domOf {d R : ℕ} (π : Stage1PieceMK d R) (tt : Fin (2 * R) → ℝ) : Set (GBranch π.Gsb.tree → ℝ) :=
  splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ MkSlotsB.lbDomR π.lb

/-- The domain of a piece is the engine's `fixLB` (so `CentreEngine`'s `hsliceD` holds by `Iff.rfl`). -/
theorem domOf_eq_fixLB {d R : ℕ} (π : Stage1PieceMK d R) (tt : Fin (2 * R) → ℝ) :
    domOf π tt = MkSlotsS.fixLB π.Gsb π.layer tt π.fix π.lb := rfl

variable {R : ℕ}

/-- **The class constant** of a fine′ class at the unit marking `mk`: the `G_sb` dagger constant `capConstO a mk …`
(`member_skelValG`; = `restConstO` of every member, α's `member_restConst`), the selection test `selOK` and the
selection constant `∏_j [v_j] Rs_j⁻¹` of the representative (CoreW's `selOK_mul_genCoreW_member_gen`: common to the
run class), and `chiDNorm ^ #selR` (`zatomG_mul_sibIndAt`: the selected filter `chiD = chiDNorm · chiDN` at the
residual selected atoms). -/
def sgnGen {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) : ℂ :=
  MkSlots.IntMember.capConstO a mk J L γ δ s roots dag *
    ((selOK (recLG a) J kSel : ℂ) *
      ((∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
        (chiDNorm : ℂ) ^ (selRAt J kSel a (mk a.prime)).card))

/-- **The mass of the class constant**: `‖sgnGen‖ ≤ (∏_{kSel j ≠ none} Rs_j⁻¹) · chiDNorm ^ #selR` (the first factor
is the main factor of `selMassMK`; `chiDNorm ^ #selR` is paid by the `C₁` lift or by `L^{7(47d+2)#sel}`). -/
theorem norm_sgnGen_le {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, 0 < Rs j) (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R)) (roots : Fin (2 * R) → (Fin d → ℤ)) (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) :
    ‖sgnGen J L γ δ s kSel Rs a mk roots dag‖ ≤
      (∏ j, if (kSel j).isSome then (Rs j)⁻¹ else 1) * chiDNorm ^ (selRAt J kSel a (mk a.prime)).card := by
  have hP0 : 0 ≤ ∏ j, (if (kSel j).isSome then (Rs j)⁻¹ else 1 : ℝ) :=
    Finset.prod_nonneg fun j _ => by
      split_ifs
      · exact (inv_pos.2 (hRs j)).le
      · exact zero_le_one
  have hC0 : 0 ≤ chiDNorm ^ (selRAt J kSel a (mk a.prime)).card := pow_nonneg chiDNorm_pos.le _
  have hCn : ‖(chiDNorm : ℂ) ^ (selRAt J kSel a (mk a.prime)).card‖ =
      chiDNorm ^ (selRAt J kSel a (mk a.prime)).card := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg chiDNorm_pos.le]
  unfold sgnGen
  rw [norm_mul, MkSlots.IntMember.norm_capConstO, one_mul, norm_mul, norm_mul, hCn]
  by_cases hok : ∀ j, (kSel j).isSome → (selCap (recLG a) J kSel j).isSome
  · have h1 : selOK (recLG a) J kSel = 1 := (selOK_eq_one_iff _ _ _).2 hok
    rw [h1, Complex.ofReal_one, norm_one, one_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)) hC0
    by_cases hk : (kSel j).isSome
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hok j hk)
      rw [hv]
      simp only [Option.elim, hk, ↓reduceIte, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 (hRs j)).le]
    · have hn : selCap (recLG a) J kSel j = none := by
        unfold selCap
        rw [Option.not_isSome_iff_eq_none.1 hk]
        rfl
      rw [hn]
      simp only [Option.elim, hk, Bool.false_eq_true, ↓reduceIte, norm_one]
  · have h0 : selOK (recLG a) J kSel = 0 := by
      unfold selOK
      exact ite_eq_right_iff.2 fun h => absurd h hok
    rw [h0, Complex.ofReal_zero, norm_zero, zero_mul]
    exact mul_nonneg hP0 hC0

/-- **The class kernels** at the unit marking `mk`: B3-2's weighted class kernel `MkUnitsL.unitHkFWL` of unit `j`
(`twistedRecenteredFWL` of the canonical class of the unit) with the per-unit top filters
`SURep a mk J (radTGen L σ kSel Rs) j` (CoreW's `top_member`, γ's `unitTopFilters_gen`), the frontier weights
`frontierG ∘ Rf` (RSlot's `unitSlot_plain`: the unit-internal slots carry B3's `slotFW … (frontierG ∘ Rf)`), the unit
profile `unitProfile … h j` and the coset base `0`; the form of `MkUnitsL.unit_hinge_dataWMkL`'s kernels. -/
def unitKerGen (P : WTParams) (p : ℕ) (J : Finset (Fin (2 * R))) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ :=
  MkUnitsL.unitHkFWL P p (MkSlotsT.SURep a mk J (radTGen P.L σ kSel Rs) j) (sourceAssemblyMk a mk j) a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun j => frontierG (Rf j))
    (VineB.unitProfile (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) 0

/-- **The centre-indexed form of a class value** at the representative `a` and the unit marking `mk`: `centreForm` with
* the piece `pieceGenAt … a (mk a.prime) dag` (`G_sb = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G`, plain),
  top times `t`, coset base `0`;
* the common gap selection `selSkCMk a mk L γ η _ 0 roots`;
* the domain `domOf` of the piece;
* main's routes, hinge clocks and hinge momenta of `stShape … (mk a.prime)`;
* one class term (`I = Unit`): the constant `sgnGen`, the slot families `fam₀Of sd hsupp` and `famCOfData sd`, the
  class kernels `unitKerGen`. -/
def classCentreRHS (P : WTParams) (p : ℕ) (hL1 : 1 ≤ P.L) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → (Fin P.d → ℤ) → SlotDatum P.d)
    (hsupp : ∀ q x l k, (sd (Sum.inl q) x).a l k ≠ 0 → ‖k - latPt P.d ((sd (Sum.inl q) x).n l)‖ ≤ 1) : ℂ :=
  centreForm (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag)
    ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).plain a.prime.prime.1) (fun _ => t) 0 roots
    (MkUnits.selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots)
    (domOf (pieceGenAt P J pat t s kSel σ Rs a (mk a.prime) dag) (fun _ => t))
    ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1
      ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).plain a.prime.prime.1))
    ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
      (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
      (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
    (fun _ : Unit => sgnGen J P.L P.γ P.δ s kSel Rs a mk roots dag)
    (fun _ => fam₀Of sd hsupp) (fun _ => famCOfData sd)
    (fun _ => unitKerGen P p J σ kSel Rs a mk h Rf)

end ClassData

/-! ## The interface -/

/-- **`ClassCentreIdentityAt Kg P`** — the class value in the centre-indexed outer mode form consumed by
`CentreEngine`'s `hval`. For every class (the binders of `MkSlotsG.ClassRepGen` up to `π` and its hypotheses), every
unit marking `mkU` with `mkU (repPt π).prime = classMk mkF (repPt π)` and the same outputs (α's IntAsm4
`obtain ⟨mkU, hset, hout⟩`), every constant `C` and every choice of slot data `sd` with the conclusions of
`GenSlotObligationAt Kg P` at the representative and the marked set `mkU (repPt π).prime` (`SlotDataOK`; provided by
`exists_slotDataOK` from the obligation and `hset`):
`classValue … = classCentreRHS …`, i.e.
`Σ_{i : Unit} sgnGen · Σ'_X Σ'_ξ (∏_t w) · outerValMμD G_sb … (domOf πM) πM.Cs.hinges
  (fun z => pieceAtomW πM (coset z) · [selSkCMk … z] · chiX L 0 X z) … (fixMeasure πM.fix) … route hclk hmom
  (unitKerGen …)` with `πM = pieceGenAt … (mkU (repPt π).prime) dag`, the families `famX (fam₀Of sd _) (famCOfData sd) X`.

The record hypotheses `1 ≤ d`, `1 ≤ L` (the member identity `member_skelValG`, VBC), `0 ≤ η` (the uniform chain-piece
weight bound `hMC` of VBC from `massEta`/`massSel`, `maxBracketPow ≥ 1`) come first. To be proved (next phase) for every
`Kg` and `P` from the member chain; the assembly consumes it as the engine's `hval` (`classCentreRHS` and `centreForm`
unfold to the engine's expression; checked against `MkSlotsE.representsIntMKSel_of_centreModes`).

Where each engine quantity comes from (`a = repPt π`, `G_sb = (stSt a.prime.skeleton a.totalSigma (mkU a.prime)).G`,
the target of the members' shapes `memShape a mkU y hy`):
* `π := pieceGenAt … (mkU a.prime) dag`: B4's `pieceGen` (`pieceGenAt_classMk`), back by
  `representsIntMKSel_pieceGenAt_congr`/`representsIntMK_pieceGenAt_congr`/`selRAt_image_congr` along `hset`;
* `selSk := selSkCMk a mkU L γ η _ 0 roots`: the selection of `member_skelValG` (B3's `hZ_commonMk`); `hgsp` is α's
  `normalizedPiece_gapIndicatorMk`;
* `Zw z = pieceAtomW π (coset z) · [selSk z]`, `sgn = sgnGen`: the member weight `[selSk ∧ restIndO] · genZa`
  (`member_skelValG`) is, at `z = resDec κ`, `selOK(a) · selConst(a) · zatomG z · sibIndAt (coset z) · [selSk z]`
  (CoreW's `zatom_member'`, `selOK_member`, `selConst_member`, `member_selAnd_ZwG`), and
  `zatomG · sibIndAt = chiDNorm^{#selR} · pieceAtomW π` (`zatomG_mul_sibIndAt` with `hset`); the dagger constant is
  `capConstO a mkU …` (`member_skelValG`); `‖Zw‖ ≤ 1` (filters, `indGenAt ∈ [0,1]`); mass `norm_sgnGen_le`;
* `Dom := domOf π (fun _ => t)`, `μ = fixMeasure π.fix`, hinges `π.Cs.hinges`: VBC's `splicedTimeDomainFix G_sb
  (layer_y ∘ core ∘ br) tt (fixS_y ∘ br) ∩ lbDomR (lbS_y ∘ br)` with the class-common layers (B3), pins (β's
  `member_fixCap_pat`) and lower bounds — the prover must identify `lbS_y ∘ br_y` with `lbGenAt … (mkU a.prime)` on the
  pinned slice (β's `lbAt`, `lbS_dParent`: lower bounds only on `dParent` trees); `hsliceD` is `domOf_eq_fixLB`;
* `route`, `hclk`, `hmom`: main's `stShape … (mkU a.prime)` (members: B3's shape equalities, e.g. `memShape_hmom`);
* `fam₀ = fam₀Of sd hsd.supp`, `famC = famCOfData sd`: VBC's `hexp₀` (cap momenta, root labels: `hsd.hasSum` at `x = 0`)
  and `hexpC` (centre `y`: `hsd.hasSum` at `x = y`), after RSlot (`member_genSlot_*`: member kernel = `genSlotKer` of
  `a`) and Box (`slotTs_mem_genSlotBox`); NOTE: `hsd.hasSum` holds at the lattice momenta `latticePoint L n` only, and
  its root/non-root case split is on the skeleton branch `br c` (the prover needs `(br c).1.2 = [] ↔ c.1.2 = []` and a
  lattice-momentum version of VBC's `hexpC`, the chain reading the slot kernels only at `0 + latticePoint L (z _)`);
* `HkM = unitKerGen`: T4D's `weightedClassFactorizationμDLZ` (class kernels `twistedRecenteredFWL`, = B3-2's
  `unitHkFWL`), unit kernels via B3-2's `unitKernelMG_slotFWW_eq` with RSlot's `unitSlot_plain` and CoreW's
  `top_member`; the hinge data is `MkUnitsL.unit_hinge_dataWMkL` (same kernels) + β's `hHkPropD_of_hHkProp`. -/
def ClassCentreIdentityAt (Kg : ℕ → ℝ → ℝ) (P : WTParams) : Prop :=
  1 ≤ P.d → ∀ hL1 : 1 ≤ P.L, 0 ≤ P.η → ∀ C : ℝ,
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  ∀ mkU : Stage1Mk.MarkFn (2 * R), mkU (repPt π).prime = classMk mkF (repPt π) →
    (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF →
  ∀ (sd : ReplacementSlot (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G →
      (Fin P.d → ℤ) → SlotDatum P.d)
    (hsd : SlotDataOK Kg P C p (repPt π) J pat t s kSel σ Rs roots h b Rf dag (mkU (repPt π).prime) sd),
  classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π =
    classCentreRHS P p hL1 J pat t s kSel σ Rs roots h Rf dag (repPt π) mkU sd hsd.supp

end WaveTurbulence.Flower.MkSlotsI
