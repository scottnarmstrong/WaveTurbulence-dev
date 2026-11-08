/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WAlign

/-! # B3s MK-SLOTS (integration): the native couple of an outer couple slot is common to the run class

The R-SLOT chain specialized to native couples: for a member `y` of the run class of a prescribed point at a marking,
the native couple layered garden (`nativeCoupleLayered`, with the canonical state layer) of every outer couple slot is
the representative's (`memShape_slotNCL`, `memShape_nativeCouple`).

The chain is B3's marked weighted R-SLOT (`Flower/MkUnits/WAlign.lean`: `spliceKerQMk` → `operation_spliceKerQMk` →
`batch_spliceKerQMk` → `commonShape_kerQMk` → `memShape_kerQ`) on top of Stage1WVine's per-operation step
(`Flower/Stage1WVine/WAlign2.lean`: `stateKerQ`, `operation_kerQ`, `stateKerQ_eq`), with the frontier-weighted slot kernel
`slotKerQ` replaced by the native couple family `slotNCL` (`some` of the native couple at a couple slot, `none` at a
chain slot); the weight parameters `f L γ δ pw g` disappear.  The only per-operation input is main's
`VineEstS4.native_couple_eq` (`VineEst/VineEstS4/Tw9Native.lean`: one LF construction leaves the native layered couple
of an ordinary pair unchanged); at a chain slot both sides are `none`.  See `COPIED-SHA256SUMS` for the provenance.

* `slotNCL`, `stateNCL`: the native couple family of a reconstruction / of a state;
* `operation_stateNCL`, `stateNCL_eq`: one selected LF operation; the layering may be any reconstructing one;
* `spliceNCLMk`, `operation_spliceNCLMk`, `spliceNCL_congrMk`, `batch_spliceNCLMk`: the spliced garden at a marking,
  along a batch carrying the marking;
* `commonShape_NCLMk`: every carried member;
* **`memShape_slotNCL`**, **`memShape_nativeCouple`**: every run-class member of a prescribed point at a marking. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

namespace WaveTurbulence.Flower.MkSlots

/-- The native couple of a slot (`none` at chain slots). -/
noncomputable def slotNCL {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ReplacementSlot S → Option (LayeredGarden 2)
  | .inl q => some (nativeCoupleLayered D hS layer hLayer q)
  | .inr _ => none

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-! ## One selected LF operation -/

/-- The native couple family of a state (canonical state layer). -/
def stateNCL (A : FamilyReconstruction w ι) : ReplacementSlot A.skeleton → Option (LayeredGarden 2) :=
  slotNCL A.data A.plain (stateLayer A) (stateLayer_isLayering A)

/-- Equality of the native couple families at an ordinary slot along one selected LF operation. -/
theorem operation_stateNCL {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i)
    (s : ReplacementSlot A.skeleton)
    (hs : match s with
      | .inl q => q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      | .inr b => b ≠ (A.family.placement i).lower) :
    stateNCL op.output (operationSlotMap op s) = stateNCL A s := by
  cases op with
  | mk hc he ht hq ε C =>
    let B := (⟨hc, he, ht, hq, ε, C⟩ : FamilyOperation (p := p) (kind := kind) A i).output
    cases s with
    | inl q =>
      exact congrArg some (native_couple_eq C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) q hs)
    | inr b => rfl

/-- The canonical state layer may be replaced by any layering reconstructing that state. -/
theorem stateNCL_eq (A : FamilyReconstruction w ι)
    (layer : GNode (A.data.forest A.plain) → ℕ) (hL : IsLayering (A.data.garden A.plain) layer)
    (hspec : layeredReconstruction A.data A.plain layer hL = A.layered) :
    stateNCL A = slotNCL A.data A.plain layer hL := by
  have hl : layer = stateLayer A :=
    layeredReconstruction_inj A.data A.plain (hspec.trans (stateLayer_spec A).symm)
  subst layer
  rfl

/-! ## The spliced garden at a marking, along a batch -/

/-- The native couple of a slot of the spliced garden at the marking `Mk`. -/
def spliceNCLMk (A : FamilyReconstruction w ι) (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton))
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) : Option (LayeredGarden 2) :=
  stateNCL A ((stShape (Mole.garden_isMolecule A.skeleton) σ Mk).iota
    A.plain ((stSt _ _ Mk).plain A.plain) s)

/-- Every outer slot at a marking is ordinary along an operation carrying the marking. -/
theorem operation_spliceNCLMk {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk) (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceNCLMk op.output (transportPrescription (operationMolIso op) σ) Mk'
      (slotCast (operation_splice_garden_eqMk hA op hT).symm s) = spliceNCLMk A σ Mk s := by
  unfold spliceNCLMk
  rw [operation_iotaMk hA op hT]
  apply operation_stateNCL
  cases s with
  | inl q =>
    exact surviving_pair_neMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ A.plain (q.firstLeaf ((stSt _ _ Mk).plain A.plain))
  | inr b =>
    exact fun he => active_lower_not_survivingMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ ⟨b, he⟩

theorem spliceNCL_congrMk (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (Mk : Set (CLVine A.skeleton)) (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ Mk).G)
    (e' : G = (stSt A.skeleton τ Mk).G) (s : ReplacementSlot G) :
    spliceNCLMk A σ Mk (slotCast e s) = spliceNCLMk A τ Mk (slotCast e' s) := by
  subst τ
  rfl

/-- The native couple R-SLOT along a batch carrying the marking. -/
theorem batch_spliceNCLMk {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceNCLMk B (transportPrescription F σ) Mk' (slotCast (h.splice_garden_eqMk σ hT hA).symm s) =
      spliceNCLMk A σ Mk s := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact spliceNCL_congrMk A Mk (transportPrescription_refl σ) _ rfl s
  | skip _ _ ih => exact ih σ hT hA s
  | @apply xs A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) F hT
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operationMk hA op h1
    let e0 := (operation_splice_garden_eqMk hA op h1).symm
    let e1 := (h.splice_garden_eqMk τ h2 hB).symm
    calc
      _ = spliceNCLMk B (transportPrescription F τ) Mk' (slotCast (e0.trans e1) s) :=
        spliceNCL_congrMk B Mk' (transportPrescription_trans _ _ σ).symm _ _ s
      _ = spliceNCLMk B (transportPrescription F τ) Mk' (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceNCLMk op.output τ _ (slotCast e0 s) := ih τ h2 hB (slotCast e0 s)
      _ = _ := operation_spliceNCLMk hA op h1 s

/-! ## Every carried member, every run-class member -/

section Member
variable {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {xs : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q xs
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : xs.Nodup)
  {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')

/-- The native couples of every carried member agree on the literal common garden at the marking. -/
theorem commonShape_NCLMk (hG : (stSt S σ Mk).G.IsPlain) (s : ReplacementSlot (stSt S σ Mk).G) :
    slotNCL Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y)
      ((commonShapeMk hM σ D hS layer hLayer hr hn hT).iota Y.plain hG s) =
    slotNCL D hS layer hLayer ((stShape hM σ Mk).iota hS hG s) := by
  let A := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer
  let h := batchMolIso_spec hr.batch
  change stateNCL Y _ = _
  unfold commonShapeMk
  erw [cast_iota _ _ Y.plain ((stSt _ _ Mk').plain Y.plain), endpointShape_iotaMk]
  change spliceNCLMk Y (transportPrescription (batchMolIso hr.batch) σ) Mk' _ = _
  erw [batch_spliceNCLMk h σ hT (unitsFamily_isV0FamMk hM σ)]
  unfold spliceNCLMk
  erw [stateNCL_eq A layer hLayer rfl]
  rfl

end Member

/-- **The native couple R-SLOT at a marking**: the native couple family of the outer slots of a run-class member is
the representative's. -/
theorem memShape_slotNCL {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotNCL y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        ((memShape a mk y hy).iota y.1.plain hG s) =
      slotNCL a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) :=
  commonShape_NCLMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1
    (markTransported_imageMark _ (mk a.prime)) hG s

/-- **The native couple of an outer couple slot is common to the run class** (at a marking): `memShape_slotNCL` at
`s = .inl q`, with `SpliceShape.iota` unfolded. -/
theorem memShape_nativeCouple {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG))) =
      nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (pairOfLeaf a.prime.skeleton a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG))) :=
  Option.some.inj (memShape_slotNCL a mk y hy hG (.inl q))

end WaveTurbulence.Flower.MkSlots
