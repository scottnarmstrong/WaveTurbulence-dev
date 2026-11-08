/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Member0
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign3

/-! # MK-UNITS: the weighted R-SLOT at a marking

Stage1WVine's `WAlign2`/`WAlign3` (the frontier-weighted outer slot kernels of a run-class member are the
representative's) at the marking `Mk`: the splice is `stSt A.skeleton σ Mk`, the batch carries the marking
(`MarkTransported`), and the chain is main's B1b-3 `batch_spliceKernelMk` → `commonShape_slotFnMk` with main's native
kernel replaced by Stage1WVine's `slotKerQ` (the per-operation step `operation_kerQ` is marking-free and imported).

Adapted from `Flower/Stage1WVine/WAlign2.lean`, `WAlign3.lean` and main's `Vine/Align/{OperationKernels,BatchKernels,
MemberKernels,ClassKernels}.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open TTree WaveTurbulence WaveTurbulence.RegRed Finset WaveTurbulence.Represents Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.VineA WaveTurbulence.VineB WaveTurbulence.VineC
  WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

variable {w p d : ℕ} {kind : Bool} {ι : Type*}

/-- The weighted kernel of a slot of the spliced garden at the marking `Mk`. -/
def spliceKerQMk (A : FamilyReconstruction w ι) (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton))
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) : (Fin 2 → ℕ) → (Fin 2 → ℝ) → Mom d → ℂ :=
  stateKerQ A f L γ δ pw g ((stShape (Mole.garden_isMolecule A.skeleton) σ Mk).iota
    A.plain ((stSt _ _ Mk).plain A.plain) s)

/-- Every outer slot at a marking is ordinary along an operation carrying the marking. -/
theorem operation_spliceKerQMk {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk) (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceKerQMk op.output (transportPrescription (operationMolIso op) σ) Mk' f L γ δ pw g
      (slotCast (operation_splice_garden_eqMk hA op hT).symm s) = spliceKerQMk A σ Mk f L γ δ pw g s := by
  unfold spliceKerQMk
  rw [operation_iotaMk hA op hT]
  apply operation_kerQ
  cases s with
  | inl q =>
    exact surviving_pair_neMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ A.plain (q.firstLeaf ((stSt _ _ Mk).plain A.plain))
  | inr b =>
    exact fun he => active_lower_not_survivingMk (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ ⟨b, he⟩

theorem spliceKerQ_congrMk (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (Mk : Set (CLVine A.skeleton)) (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ Mk).G)
    (e' : G = (stSt A.skeleton τ Mk).G) (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ)
    (g : Fin w → Mom d → ℂ) (s : ReplacementSlot G) :
    spliceKerQMk A σ Mk f L γ δ pw g (slotCast e s) = spliceKerQMk A τ Mk f L γ δ pw g (slotCast e' s) := by
  subst τ
  rfl

/-- The weighted R-SLOT along a batch carrying the marking. -/
theorem batch_spliceKerQMk {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceKerQMk B (transportPrescription F σ) Mk' f L γ δ pw g (slotCast (h.splice_garden_eqMk σ hT hA).symm s) =
      spliceKerQMk A σ Mk f L γ δ pw g s := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact spliceKerQ_congrMk A Mk (transportPrescription_refl σ) _ rfl f L γ δ pw g s
  | skip _ _ ih => exact ih σ hT hA s
  | @apply xs A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) F hT
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operationMk hA op h1
    let e0 := (operation_splice_garden_eqMk hA op h1).symm
    let e1 := (h.splice_garden_eqMk τ h2 hB).symm
    calc
      _ = spliceKerQMk B (transportPrescription F τ) Mk' f L γ δ pw g (slotCast (e0.trans e1) s) :=
        spliceKerQ_congrMk B Mk' (transportPrescription_trans _ _ σ).symm _ _ f L γ δ pw g s
      _ = spliceKerQMk B (transportPrescription F τ) Mk' f L γ δ pw g (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceKerQMk op.output τ _ f L γ δ pw g (slotCast e0 s) := ih τ h2 hB (slotCast e0 s)
      _ = _ := operation_spliceKerQMk hA op h1 f L γ δ pw g s

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

/-- The weighted kernels of every carried member agree on the literal common garden at the marking. -/
theorem commonShape_kerQMk (hG : (stSt S σ Mk).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt S σ Mk).G) :
    slotKerQ Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y) L γ δ (typeProfiles Y.layered f) pw g
      ((commonShapeMk hM σ D hS layer hLayer hr hn hT).iota Y.plain hG s) =
    slotKerQ D hS layer hLayer L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) f) pw g
      ((stShape hM σ Mk).iota hS hG s) := by
  let A := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer
  let h := batchMolIso_spec hr.batch
  change stateKerQ Y f L γ δ pw g _ = _
  unfold commonShapeMk
  erw [cast_iota _ _ Y.plain ((stSt _ _ Mk').plain Y.plain), endpointShape_iotaMk]
  change spliceKerQMk Y (transportPrescription (batchMolIso hr.batch) σ) Mk' f L γ δ pw g _ = _
  erw [batch_spliceKerQMk h σ hT (unitsFamily_isV0FamMk hM σ)]
  unfold spliceKerQMk
  erw [stateKerQ_eq A layer hLayer rfl]
  rfl

end Member

/-- **The weighted R-SLOT at a marking** on the representative's spliced garden (kernels with explicit weight
layers). -/
theorem memShape_kerQ {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin (2 * R) → Mom d → ℂ)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotKerQ y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ (typeProfiles y.1.layered f) pw g
      ((memShape a mk y hy).iota y.1.plain hG s) =
    slotKerQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ
      (typeProfiles a.layered f) pw g
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) := by
  have h := commonShape_kerQMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1
    (markTransported_imageMark _ (mk a.prime)) hG f L γ δ pw g s
  rw [sourceLayer_reconstructs] at h
  exact h

/-- The weight layers of the arguments of the outer slots are common to the class (at a marking). -/
theorem memShape_wLay {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2) (pw : ℕ) :
    wLay pw (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s) i) =
      wLay pw (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s)
          i) := by
  obtain ⟨M, hr, hbr, hlow⟩ := memShape_trace a mk y hy
  have hroute := congrFun (congrFun (memShape_route a mk y hy hG) s) i
  rcases hr' : (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route
      a.prime.prime.1 hG s i with y' | j
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inl _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inl _ hG hr']
    rcases y' with r | c
    · rfl
    · show stateLayer y.1 (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode =
        sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode
      rw [memShape_core_layer, shape_core_layerMk]
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inr _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inr _ hG hr']
    show stateLayer y.1 (y.1.data.coreBranch y.1.plain (y.2 j).blk.b).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower).toNode
    rw [hlow j]
    exact member_core_layerMk a mk y M hr _

/-- **The weighted R-SLOT at a marking**: the outer frontier-weighted slot kernels of a run-class member are the
representative's. -/
theorem memShape_slotFW {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin (2 * R) → Mom d → ℂ)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ f pw g
        ((memShape a mk y hy).iota y.1.plain hG s) =
      slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ f pw g
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) := by
  funext ts k
  rw [slotFW_eq_kerQ, slotFW_eq_kerQ]
  have hw : (fun i => wLay pw (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s) i)) =
      fun i => wLay pw (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s)
          i) :=
    funext fun i => memShape_wLay a mk y hy hG s i pw
  rw [hw, stateLayer_spec y.1, sourceLayer_reconstructs a]
  exact congrFun (congrFun (congrFun (memShape_kerQ a mk y hy hG f L γ δ pw g s) _) ts) k

end WaveTurbulence.Flower.MkUnits
