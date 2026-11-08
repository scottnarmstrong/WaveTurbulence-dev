/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntChain

/-! # B3s-HELPER3 B4 (pattern R-core 1): the native chain of an outer chain slot is common to the run class

The chain twin of B3s's `MkSlots/IntChain.lean` (copied by source and adapted, see `COPIED-SHA256SUMS`): the native
chain family `slotNTL` (`some` of the native chain layered garden at a chain slot, `none` at a couple slot) along
B3's marked R-SLOT chain, with main's per-operation input `VineEstS4.native_tree_eq` (one LF construction leaves the
native layered chain of an ordinary branch unchanged) in place of `native_couple_eq`.

* `slotNTL`, `stateNTL`, `operation_stateNTL`, `stateNTL_eq`, `spliceNTLMk`, `operation_spliceNTLMk`,
  `spliceNTL_congrMk`, `batch_spliceNTLMk`, `commonShape_NTLMk`, `memShape_slotNTL`;
* **`memShape_nativeChain`**: the native chain of an outer chain slot `.inr c` of a run-class member is the
  representative's;
* `lonePath_nil_iff`, **`memShape_lonePath_nil_iff`**: the chain at a `G_sb` atom is trivial for a member iff it is
  for the representative (so the core branch of a `G_sb` atom is the attached node for both, or for neither). -/

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

namespace WaveTurbulence.Flower.MkSlotsB

/-- The native chain of a slot (`none` at couple slots). -/
noncomputable def slotNTL {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ReplacementSlot S → Option (LayeredGarden 1)
  | .inl _ => none
  | .inr b => some (nativeChainLayered D hS layer hLayer b)

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-! ## One selected LF operation -/

/-- The native chain family of a state (canonical state layer). -/
def stateNTL (A : FamilyReconstruction w ι) : ReplacementSlot A.skeleton → Option (LayeredGarden 1) :=
  slotNTL A.data A.plain (stateLayer A) (stateLayer_isLayering A)

/-- Equality of the native chain families at an ordinary slot along one selected LF operation. -/
theorem operation_stateNTL {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i)
    (s : ReplacementSlot A.skeleton)
    (hs : match s with
      | .inl q => q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      | .inr b => b ≠ (A.family.placement i).lower) :
    stateNTL op.output (operationSlotMap op s) = stateNTL A s := by
  cases op with
  | mk hc he ht hq ε C =>
    let B := (⟨hc, he, ht, hq, ε, C⟩ : FamilyOperation (p := p) (kind := kind) A i).output
    cases s with
    | inl q => rfl
    | inr b =>
      exact congrArg some (native_tree_eq C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) b hs)

/-- The canonical state layer may be replaced by any layering reconstructing that state. -/
theorem stateNTL_eq (A : FamilyReconstruction w ι)
    (layer : GNode (A.data.forest A.plain) → ℕ) (hL : IsLayering (A.data.garden A.plain) layer)
    (hspec : layeredReconstruction A.data A.plain layer hL = A.layered) :
    stateNTL A = slotNTL A.data A.plain layer hL := by
  have hl : layer = stateLayer A :=
    layeredReconstruction_inj A.data A.plain (hspec.trans (stateLayer_spec A).symm)
  subst layer
  rfl

/-! ## The spliced garden at a marking, along a batch -/

/-- The native chain of a slot of the spliced garden at the marking `Mk`. -/
def spliceNTLMk (A : FamilyReconstruction w ι) (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton))
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) : Option (LayeredGarden 1) :=
  stateNTL A ((stShape (Mole.garden_isMolecule A.skeleton) σ Mk).iota
    A.plain ((stSt _ _ Mk).plain A.plain) s)

/-- Every outer slot at a marking is ordinary along an operation carrying the marking. -/
theorem operation_spliceNTLMk {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk) (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceNTLMk op.output (transportPrescription (operationMolIso op) σ) Mk'
      (slotCast (operation_splice_garden_eqMk hA op hT).symm s) = spliceNTLMk A σ Mk s := by
  unfold spliceNTLMk
  rw [operation_iotaMk hA op hT]
  apply operation_stateNTL
  cases s with
  | inl q =>
    exact surviving_pair_neMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ A.plain (q.firstLeaf ((stSt _ _ Mk).plain A.plain))
  | inr b =>
    exact fun he => active_lower_not_survivingMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ ⟨b, he⟩

theorem spliceNTL_congrMk (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (Mk : Set (CLVine A.skeleton)) (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ Mk).G)
    (e' : G = (stSt A.skeleton τ Mk).G) (s : ReplacementSlot G) :
    spliceNTLMk A σ Mk (slotCast e s) = spliceNTLMk A τ Mk (slotCast e' s) := by
  subst τ
  rfl

/-- The native chain R-SLOT along a batch carrying the marking. -/
theorem batch_spliceNTLMk {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceNTLMk B (transportPrescription F σ) Mk' (slotCast (h.splice_garden_eqMk σ hT hA).symm s) =
      spliceNTLMk A σ Mk s := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact spliceNTL_congrMk A Mk (transportPrescription_refl σ) _ rfl s
  | skip _ _ ih => exact ih σ hT hA s
  | @apply xs A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) F hT
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operationMk hA op h1
    let e0 := (operation_splice_garden_eqMk hA op h1).symm
    let e1 := (h.splice_garden_eqMk τ h2 hB).symm
    calc
      _ = spliceNTLMk B (transportPrescription F τ) Mk' (slotCast (e0.trans e1) s) :=
        spliceNTL_congrMk B Mk' (transportPrescription_trans _ _ σ).symm _ _ s
      _ = spliceNTLMk B (transportPrescription F τ) Mk' (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceNTLMk op.output τ _ (slotCast e0 s) := ih τ h2 hB (slotCast e0 s)
      _ = _ := operation_spliceNTLMk hA op h1 s

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

/-- The native chains of every carried member agree on the literal common garden at the marking. -/
theorem commonShape_NTLMk (hG : (stSt S σ Mk).G.IsPlain) (s : ReplacementSlot (stSt S σ Mk).G) :
    slotNTL Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y)
      ((commonShapeMk hM σ D hS layer hLayer hr hn hT).iota Y.plain hG s) =
    slotNTL D hS layer hLayer ((stShape hM σ Mk).iota hS hG s) := by
  let A := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer
  let h := batchMolIso_spec hr.batch
  change stateNTL Y _ = _
  unfold commonShapeMk
  erw [cast_iota _ _ Y.plain ((stSt _ _ Mk').plain Y.plain), endpointShape_iotaMk]
  change spliceNTLMk Y (transportPrescription (batchMolIso hr.batch) σ) Mk' _ = _
  erw [batch_spliceNTLMk h σ hT (unitsFamily_isV0FamMk hM σ)]
  unfold spliceNTLMk
  erw [stateNTL_eq A layer hLayer rfl]
  rfl

end Member

/-- **The native chain R-SLOT at a marking**: the native chain family of the outer slots of a run-class member is the
representative's. -/
theorem memShape_slotNTL {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotNTL y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        ((memShape a mk y hy).iota y.1.plain hG s) =
      slotNTL a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) :=
  commonShape_NTLMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1
    (markTransported_imageMark _ (mk a.prime)) hG s

/-- **The native chain of an outer chain slot is common to the run class** (at a marking). -/
theorem memShape_nativeChain {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    nativeChainLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) ((memShape a mk y hy).br c) =
      nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) :=
  Option.some.inj (memShape_slotNTL a mk y hy hG (.inr c))

/-! ## Trivial chains -/

/-- A chain has an empty lone path iff its plugged tree is a single leaf. -/
theorem lonePath_nil_iff (X : RegChain) (ζ : ℤˣ) : X.lonePath = [] ↔ X.plug ζ .leaf = TTree.leaf := by
  constructor
  · intro h
    have hX : X = .nil := (chain_lonePath_length_zero_iff X).mp (by rw [h]; rfl)
    subst hX
    rfl
  · intro h
    have hm := PL234.lonePath_mem_leaves X ζ
    rw [h] at hm
    simpa [TTree.leaves] using hm

/-- The chain of a skeleton branch is trivial iff its native chain garden is a single leaf. -/
theorem lonePath_nil_iff_native {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) :
    (D.tree b).lonePath = [] ↔ (nativeChainLayered D hS layer hLayer b).garden.tree 0 = TTree.leaf :=
  lonePath_nil_iff (D.tree b) (nodeSign S.sig b.1)

/-- **The chain at a `G_sb` atom is trivial for a run-class member iff it is for the representative.** -/
theorem memShape_lonePath_nil_iff {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    (y.1.data.tree ((memShape a mk y hy).br c)).lonePath = [] ↔
      (a.prime.data.tree ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).lonePath
        = [] := by
  rw [lonePath_nil_iff_native y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1),
    lonePath_nil_iff_native a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a),
    memShape_nativeChain a mk y hy hG c]

end WaveTurbulence.Flower.MkSlotsB
