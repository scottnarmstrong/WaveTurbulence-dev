/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamily
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceStructure
/-! VINE-A1: canonical prime-skeleton representatives of ordinary canonical
objects of either kind, and their full / sigma-selected LF family states.
REG-STRUCT provides source skeleton and replacement uniqueness. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
open WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton

variable {w : ℕ}

/-- The actual prime skeleton and literal replacements of a layered garden. -/
structure PrimeData (LG : LayeredGarden w) where
  skeleton : Garden w
  prime : IsPrimeGarden skeleton
  data : ReconstructionData skeleton
  decodes : data.Decodes prime.1 LG.garden

/-- Existence uses the proved source structure theorem; no witness is assumed. -/
theorem primeData_nonempty (LG : LayeredGarden w) (h : LG.garden.IsPlain) : Nonempty (PrimeData LG) := by
  obtain ⟨S, ⟨hS, D, hd, _⟩, _⟩ := existsUnique_prime_with_replacements LG.garden h
  exact ⟨⟨S, hS, D, hd⟩⟩

noncomputable def primeDataOf (LG : LayeredGarden w) (h : LG.garden.IsPlain) : PrimeData LG :=
  Classical.choice (primeData_nonempty LG h)

/-- Prime skeletons of two source representatives of the same garden agree literally. -/
theorem primeData_skeleton_unique {LG : LayeredGarden w} (A B : PrimeData LG) :
    A.skeleton = B.skeleton := by
  obtain ⟨S, _, hu⟩ := existsUnique_prime_with_replacements LG.garden A.decodes.1
  have hA : A.skeleton = S := hu A.skeleton
    ⟨A.prime, A.data, A.decodes, fun D hd => reconstructionData_unique D A.data A.prime hd A.decodes⟩
  have hB : B.skeleton = S := hu B.skeleton
    ⟨B.prime, B.data, B.decodes, fun D hd => reconstructionData_unique D B.data B.prime hd B.decodes⟩
  exact hA.trans hB.symm

/-- Literal replacement data are unique after transporting the skeleton equality. -/
theorem primeData_data_unique {LG : LayeredGarden w} (A B : PrimeData LG) : HEq A.data B.data := by
  have h := primeData_skeleton_unique A B
  cases A with
  | mk S hS D hd =>
    cases B with
    | mk T hT E he =>
      dsimp only at h
      subst T
      exact heq_of_eq (reconstructionData_unique D E hS hd he)

/-- An actual family state over the selected core subcollection. -/
noncomputable def PrimeData.state {LG : LayeredGarden w} (A : PrimeData LG)
    (U : Set (CLVine A.skeleton)) (hU : U ⊆ vinesV A.skeleton) :
    FamilyReconstruction w (CoreIndex U) where
  skeleton := A.skeleton
  family := coreFamilyOf U hU
  plain := A.prime.1
  data := A.data
  layered := LG
  decodes := A.decodes

/-- The coarse congruence state, using every core member of V. -/
noncomputable def PrimeData.coarseState {LG : LayeredGarden w} (A : PrimeData LG) :
    FamilyReconstruction w (CoreIndex (vinesV A.skeleton)) := A.state (vinesV A.skeleton) (fun _ h => h)

/-- The fine congruence state for a prescription uses precisely the core members of V0(sigma).  B1a: with the
trailing marked vine set `Mk` (default `∅`), the core members of the unmarked `𝒱₀♮ = vinesV0 A.skeleton σ Mk`
(twists only at unmarked vines). -/
noncomputable def PrimeData.fineState {LG : LayeredGarden w} (A : PrimeData LG)
    (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton) := ∅) :
    FamilyReconstruction w (CoreIndex (vinesV0 A.skeleton σ Mk)) :=
  A.state (vinesV0 A.skeleton σ Mk) (vinesV0_subsetMk A.skeleton σ Mk)

/-- Fine′ family state of the probe (copied by source from the B0 probe, lines 209–214): twists only at unmarked
vines. -/
noncomputable def fineStateMk {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton)
    (Mk : Set (Stage1.CLVine A.skeleton)) :
    LFTwist.FamilyReconstruction w (VineA.CoreIndex (vinesV0Mk A.skeleton σ Mk)) :=
  A.state (vinesV0Mk A.skeleton σ Mk) (fun _ h => (vinesV0_subset A.skeleton σ) h.1)

/-- Coarse′ family state of the probe (copied by source from the B0 probe, lines 216–219). -/
noncomputable def coarseStateMk {LG : LayeredGarden w} (A : PrimeData LG)
    (Mk : Set (Stage1.CLVine A.skeleton)) :
    LFTwist.FamilyReconstruction w (VineA.CoreIndex {c | c ∈ Stage1.vinesV A.skeleton ∧ c ∉ Mk}) :=
  A.state {c | c ∈ Stage1.vinesV A.skeleton ∧ c ∉ Mk} (fun _ h => h.1)

/-- B1a bridge: states over equal carriers are equal up to the carrier identification. -/
theorem PrimeData.state_heq {LG : LayeredGarden w} (A : PrimeData LG) {U V : Set (CLVine A.skeleton)}
    (hUV : U = V) (hU : U ⊆ vinesV A.skeleton) (hV : V ⊆ vinesV A.skeleton) :
    HEq (A.state U hU) (A.state V hV) := by
  subst hUV; rfl

/-- B1a bridge: the outputs of states over equal carriers agree. -/
theorem PrimeData.state_allCoreOutputs_congr {LG : LayeredGarden w} (A : PrimeData LG) {p : ℕ} {kind : Bool}
    {U V : Set (CLVine A.skeleton)} (hUV : U = V) (hU : U ⊆ vinesV A.skeleton) (hV : V ⊆ vinesV A.skeleton) :
    (A.state U hU).allCoreOutputs (p := p) (kind := kind) = (A.state V hV).allCoreOutputs (p := p) (kind := kind) := by
  subst hUV; rfl

/-- B1a bridge: the probe's fine′ state is main's threaded fine state. -/
theorem fineStateMk_heq {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton)
    (Mk : Set (CLVine A.skeleton)) : HEq (fineStateMk A σ Mk) (A.fineState σ Mk) :=
  A.state_heq (vinesV0Mk_eq A.skeleton σ Mk) _ _

/-- B1a bridge: the fine′ outputs are the threaded fine outputs. -/
theorem fineStateMk_outputs {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton)
    (Mk : Set (CLVine A.skeleton)) {p : ℕ} {kind : Bool} :
    (fineStateMk A σ Mk).allCoreOutputs (p := p) (kind := kind) =
      (A.fineState σ Mk).allCoreOutputs (p := p) (kind := kind) :=
  A.state_allCoreOutputs_congr (vinesV0Mk_eq A.skeleton σ Mk) _ _

/-- B1a bridge: the coarse′ state at `Mk = ∅` is main's coarse state. -/
theorem coarseStateMk_empty_heq {LG : LayeredGarden w} (A : PrimeData LG) :
    HEq (coarseStateMk A ∅) A.coarseState :=
  A.state_heq (by ext c; simp) _ _

/-- B1a bridge: the coarse′ outputs at `Mk = ∅` are main's coarse outputs. -/
theorem coarseStateMk_empty_outputs {LG : LayeredGarden w} (A : PrimeData LG) {p : ℕ} {kind : Bool} :
    (coarseStateMk A ∅).allCoreOutputs (p := p) (kind := kind) =
      A.coarseState.allCoreOutputs (p := p) (kind := kind) :=
  A.state_allCoreOutputs_congr (by ext c; simp) _ _

/-- The coarse state satisfies S1's actual V-family predicate. -/
theorem PrimeData.coarseState_isVFamily {LG : LayeredGarden w} (A : PrimeData LG) :
    IsVFamily A.coarseState := by
  constructor
  · intro i
    exact ⟨i.1, i.2.1, rfl, rfl, (corePlacementOf_spec _ i).1.symm⟩
  · intro c hc hcore
    exact ⟨⟨c, hc, hcore⟩, rfl, rfl, (corePlacementOf_spec _ ⟨c, hc, hcore⟩).1.symm⟩

/-- Both source canonical kinds provide the prime representative and LF states. -/
noncomputable def canonicalPrimeData {p : ℕ} {kind : Bool} (LG : LayeredGarden w)
    (hc : CanonicalObject p kind LG) : PrimeData LG := primeDataOf LG hc.plain

end WaveTurbulence.VineA
