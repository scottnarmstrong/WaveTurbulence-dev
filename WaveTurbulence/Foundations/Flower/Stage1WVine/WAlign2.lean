/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign1

/-! # STAGE1W-VINE (weighted VINE-ALIGN, part 2): the weighted kernels with explicit weight layers are class-common

Main's R-SLOT chain (`operation_kernel` → `operation_spliceKernel` → `batch_spliceKernel` → `commonShape_slotFn` →
`classShape_slotFn` → `sourceShape_slotFn`, `Vine/Align/{OperationKernels,BatchKernels,MemberKernels,ClassKernels,
Export}.lean`, see `COPIED-SHA256SUMS`) with main's native kernel `slotFn` replaced by `slotKerQ` at an arbitrary vector of
root weight layers.  The only per-operation input is `ordinary_couple_kerQ`/`ordinary_tree_kerQ` (part 1).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed Finset WaveTurbulence.Represents Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.VineA WaveTurbulence.VineB WaveTurbulence.VineC
  WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist

variable {w p d : ℕ} {kind : Bool} {ι : Type*}

/-- The weighted kernel family of a state, with explicit root weight layers. -/
def stateKerQ (A : FamilyReconstruction w ι) (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ)
    (g : Fin w → Mom d → ℂ) : ReplacementSlot A.skeleton → (Fin 2 → ℕ) → (Fin 2 → ℝ) → Mom d → ℂ :=
  slotKerQ A.data A.plain (stateLayer A) (stateLayer_isLayering A) L γ δ (typeProfiles A.layered f) pw g

/-- Equality of the weighted kernel functions at an ordinary slot along one selected LF operation. -/
theorem operation_kerQ {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot A.skeleton)
    (hs : match s with
      | .inl q => q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      | .inr b => b ≠ (A.family.placement i).lower) :
    stateKerQ op.output f L γ δ pw g (operationSlotMap op s) = stateKerQ A f L γ δ pw g s := by
  cases op with
  | mk hc he ht hq ε C =>
    let B := (⟨hc, he, ht, hq, ε, C⟩ : FamilyOperation (p := p) (kind := kind) A i).output
    funext qv ts k
    cases s with
    | inl q =>
      exact ordinary_couple_kerQ C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) f L γ δ pw g q hs qv ts k
    | inr b =>
      exact ordinary_tree_kerQ C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) f L γ δ pw g b hs qv ts k

/-- The weighted kernel of a slot of the simultaneously spliced garden. -/
def spliceKerQ (A : FamilyReconstruction w ι) (σ : Prescription A.skeleton)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ).G) : (Fin 2 → ℕ) → (Fin 2 → ℝ) → Mom d → ℂ :=
  stateKerQ A f L γ δ pw g ((stShape (Mole.garden_isMolecule A.skeleton) σ).iota
    A.plain ((stSt _ _).plain A.plain) s)

/-- Every outer slot is ordinary: the exceptional pair and lower joint have been removed. -/
theorem operation_spliceKerQ {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    (hA : IsV0Fam A.family σ) (op : FamilyOperation (p := p) (kind := kind) A i)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ).G) :
    spliceKerQ op.output (transportPrescription (operationMolIso op) σ) f L γ δ pw g
      (slotCast (operation_splice_garden_eq hA op).symm s) = spliceKerQ A σ f L γ δ pw g s := by
  unfold spliceKerQ
  rw [operation_iota hA op]
  apply operation_kerQ
  cases s with
  | inl q =>
    exact surviving_pair_ne (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ A.plain (q.firstLeaf ((stSt _ _).plain A.plain))
  | inr b =>
    exact fun he => active_lower_not_surviving (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ ⟨b, he⟩

theorem spliceKerQ_congr (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ).G) (e' : G = (stSt A.skeleton τ).G)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ) (s : ReplacementSlot G) :
    spliceKerQ A σ f L γ δ pw g (slotCast e s) = spliceKerQ A τ f L γ δ pw g (slotCast e' s) := by
  subst τ
  rfl

/-- The weighted R-SLOT for an arbitrary actual selected-operation trace. -/
theorem batch_spliceKerQ {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt A.skeleton σ).G) :
    spliceKerQ B (transportPrescription F σ) f L γ δ pw g (slotCast (h.splice_garden_eq σ hA).symm s) =
      spliceKerQ A σ f L γ δ pw g s := by
  induction h with
  | nil A =>
    exact spliceKerQ_congr A (transportPrescription_refl σ) _ rfl f L γ δ pw g s
  | skip _ _ ih => exact ih σ hA s
  | @apply xs A B i op F h ih =>
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operation hA op
    let e0 := (operation_splice_garden_eq hA op).symm
    let e1 := (h.splice_garden_eq τ hB).symm
    calc
      _ = spliceKerQ B (transportPrescription F τ) f L γ δ pw g (slotCast (e0.trans e1) s) :=
        spliceKerQ_congr B (transportPrescription_trans _ _ σ).symm _ _ f L γ δ pw g s
      _ = spliceKerQ B (transportPrescription F τ) f L γ δ pw g (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceKerQ op.output τ f L γ δ pw g (slotCast e0 s) := ih τ hB (slotCast e0 s)
      _ = _ := operation_spliceKerQ hA op f L γ δ pw g s

/-- The canonical state layer may be replaced by any layering reconstructing that state. -/
theorem stateKerQ_eq (A : FamilyReconstruction w ι)
    (layer : GNode (A.data.forest A.plain) → ℕ) (hL : IsLayering (A.data.garden A.plain) layer)
    (hspec : layeredReconstruction A.data A.plain layer hL = A.layered)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ) :
    stateKerQ A f L γ δ pw g = slotKerQ A.data A.plain layer hL L γ δ (typeProfiles A.layered f) pw g := by
  have hl : layer = stateLayer A :=
    layeredReconstruction_inj A.data A.plain (hspec.trans (stateLayer_spec A).symm)
  subst layer
  rfl

section Member
variable {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {xs : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q xs
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
  (hn : xs.Nodup)

/-- The weighted kernels of every carried member agree on the literal common garden. -/
theorem commonShape_kerQ (hG : (stSt S σ).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt S σ).G) :
    slotKerQ Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y) L γ δ (typeProfiles Y.layered f) pw g
      ((commonShape hM σ D hS layer hLayer hr hn).iota Y.plain hG s) =
    slotKerQ D hS layer hLayer L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) f) pw g
      ((stShape hM σ).iota hS hG s) := by
  let A := unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer
  let h := batchMolIso_spec hr.batch
  change stateKerQ Y f L γ δ pw g _ = _
  unfold commonShape
  erw [cast_iota _ _ Y.plain ((stSt _ _).plain Y.plain), endpointShape_iota]
  change spliceKerQ Y (transportPrescription (batchMolIso hr.batch) σ) f L γ δ pw g _ = _
  erw [batch_spliceKerQ h σ (unitsFamily_isV0Fam hM σ)]
  unfold spliceKerQ
  erw [stateKerQ_eq A layer hLayer rfl]
  rfl

end Member

section Class
variable {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssembly hM σ)))
  (hy : y ∈ classU (unitsSplit (alignedAssembly hM σ)) p kind
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)))

/-- The weighted R-SLOT for every genuine member of the finite class. -/
theorem classShape_kerQ (hG : (stSt S σ).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)
    (s : ReplacementSlot (stSt S σ).G) :
    slotKerQ y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ (typeProfiles y.1.layered f) pw g
      ((classShape hM σ D hS layer hLayer hp y hy).iota y.1.plain hG s) =
    slotKerQ D hS layer hLayer L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) f) pw g
      ((stShape hM σ).iota hS hG s) :=
  commonShape_kerQ hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1 hG f L γ δ pw g s

end Class

/-- The weighted R-SLOT on the literal common profile garden of a prescribed point. -/
theorem sourceShape_kerQ {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin (2 * R) → Mom d → ℂ)
    (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotKerQ y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ (typeProfiles y.1.layered f) pw g
      ((sourceShape a y hy).iota y.1.plain hG s) =
    slotKerQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ
      (typeProfiles a.layered f) pw g ((profileShape a).iota a.prime.prime.1 hG s) := by
  have h := classShape_kerQ (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hG f L γ δ pw g s
  rw [sourceLayer_reconstructs] at h
  exact h

end WaveTurbulence.Flower.Stage1WVine
