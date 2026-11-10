/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRestrictionOutputs
public import WaveTurbulence.Foundations.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.Vine.A.VinePrimeUnique
/-! Actual fine garden output classes lie in their coarse class and rebase at every member. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 Twist RedSplice LFTwist Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- Include the exact canonical core coordinates of a smaller vine carrier. -/
def coreIndexInclusion {G : Garden w} {U V : Set (CLVine G)} (h : U ⊆ V) : CoreIndex U → CoreIndex V :=
  fun i => ⟨i.1, h i.2.1, i.2.2⟩

theorem coreIndexInclusion_injective {G : Garden w} {U V : Set (CLVine G)} (h : U ⊆ V) :
    Function.Injective (coreIndexInclusion h) := fun _ _ he => Subtype.ext (congrArg (fun j : CoreIndex V => j.1) he)

/-- Canonical geometric placements agree across a restriction of the exact vine carrier. -/
theorem coreFamilyOf_restrict {G : Garden w} (U V : Set (CLVine G)) (hU : U ⊆ vinesV G)
    (hV : V ⊆ vinesV G) (hUV : U ⊆ V) :
    coreFamilyOf U hU = familyRestrict (coreFamilyOf V hV)
      (coreIndexInclusion hUV) (coreIndexInclusion_injective hUV) := by
  apply CoreFamily.ext_data
  · exact funext fun i => core_kind_unique (coreKind_spec U i) (coreKind_spec V (coreIndexInclusion hUV i))
  · rfl
  · rfl
  · exact funext fun i => placement_unique (corePlacementOf_spec U i)
      (corePlacementOf_spec V (coreIndexInclusion hUV i))

/-- The entire actual smaller state is the restriction of the larger canonical state. -/
theorem PrimeData.state_eq_restrict (A : PrimeData LG) (U V : Set (CLVine A.skeleton))
    (hU : U ⊆ vinesV A.skeleton) (hV : V ⊆ vinesV A.skeleton) (hUV : U ⊆ V) :
    A.state U hU = stateRestrict (A.state V hV) (coreIndexInclusion hUV) (coreIndexInclusion_injective hUV) := by
  apply familyReconstruction_ext
  · rfl
  · exact heq_of_eq (coreFamilyOf_restrict U V hU hV hUV)
  · rfl
  · rfl

/-- Source-level containment uses actual restricted batches, rather than generated reachability. -/
theorem PrimeData.fine_outputs_subset_coarse (A : PrimeData LG) (σ : Prescription A.skeleton) :
    (A.fineState σ).allCoreOutputs (p := p) (kind := kind) ⊆
      A.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  change (A.state (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ)).allCoreOutputs ⊆ _
  rw [A.state_eq_restrict _ _ _ (fun _ h => h) (vinesV0_subset A.skeleton σ)]
  exact allCoreOutputs_restrict_subset _ _ _

/-- B1b (R11): the fine′ class (marked set `Mk`) lies in the coarse′ class of any smaller marked set `Mk0`
(o75: the coarse marking `markI0` is contained in the fine marking `markI`). -/
theorem PrimeData.fine_outputs_subset_coarseMk (A : PrimeData LG) (σ : Prescription A.skeleton)
    {Mk Mk0 : Set (CLVine A.skeleton)} (h : Mk0 ⊆ Mk) :
    (A.fineState σ Mk).allCoreOutputs (p := p) (kind := kind) ⊆
      (coarseStateMk A Mk0).allCoreOutputs (p := p) (kind := kind) := by
  change (A.state (vinesV0 A.skeleton σ Mk) (vinesV0_subsetMk A.skeleton σ Mk)).allCoreOutputs ⊆
    (A.state {c | c ∈ vinesV A.skeleton ∧ c ∉ Mk0} (fun _ h => h.1)).allCoreOutputs
  rw [A.state_eq_restrict (vinesV0 A.skeleton σ Mk) {c | c ∈ vinesV A.skeleton ∧ c ∉ Mk0} _ (fun _ h => h.1)
    (fun c hc => ⟨(mem_vinesV0.mp hc).1.1, fun hm => (mem_vinesV0.mp hc).2 (h hm)⟩)]
  exact allCoreOutputs_restrict_subset _ _ _

/-- B1b (R11): every prescribed garden belongs to its fine′ output class. -/
theorem PrimeData.mem_fine_outputs_selfMk (A : PrimeData LG) (σ : Prescription A.skeleton)
    (Mk : Set (CLVine A.skeleton)) :
    LG ∈ (A.fineState σ Mk).allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind (A.fineState σ Mk) LG).mpr
    ⟨A.fineState σ Mk, WaveTurbulence.Stage1.Congruent.refl p kind (A.fineState σ Mk), rfl⟩

/-- Every prescribed garden belongs to its actual fine output class. -/
theorem PrimeData.mem_fine_outputs_self (A : PrimeData LG) (σ : Prescription A.skeleton) :
    LG ∈ (A.fineState σ).allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind (A.fineState σ) LG).mpr
    ⟨A.fineState σ, WaveTurbulence.Stage1.Congruent.refl p kind (A.fineState σ), rfl⟩

end WaveTurbulence.VineA
