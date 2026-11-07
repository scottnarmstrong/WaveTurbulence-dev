/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalSlotFlow
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowCancellation
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLBoundaryIdentities

/-! # The actual local CL decoration satisfies the M9 internal flow fiber -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

open Classical in
theorem gardenInternalFlow_external {E : Type*} [AddCommGroup E] [Module ℝ E]
    (κ : GNode G.tree → E)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch G.tree) :
    flow G.molecule U (fun e => Mole.restrictLabels G κ e.1) v =
      Mole.slotSum G κ v-externalSlotSum G U κ v := by
  classical
  rw [gardenInternalFlow_slots κ hp]
  have he := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 4))
    (fun i => i ∈ Mole.internalPositions G U v) (fun i => Mole.slotWeight G v i • κ (Mole.slotNode G v i))
  have hf : Finset.univ.filter (fun i => i ∈ Mole.internalPositions G U v) = Mole.internalPositions G U v := by
    ext i
    exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  rw [hf] at he
  exact eq_sub_iff_add_eq.mpr he

open Classical in
theorem clInternalFlow_interior {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hU : G.molecule.IsBlock U a b) (κ : GNode G.tree → E)
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch G.tree) (hv : v ∈ U) (ha : v ≠ a) (hb : v ≠ b) :
    flow G.molecule U (fun e => Mole.restrictLabels G κ e.1) v = 0 := by
  rw [gardenInternalFlow_external κ hp,
    (Mole.slotSum_eq_zero_iff G κ v).mpr (hc v hv),cl_externalSlotSum_interior hU κ v hv ha hb,sub_self]

open Classical in
theorem clInternalFlow_lower {E : Type*} [AddCommGroup E] [Module ℝ E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (κ : GNode G.tree → E)
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    flow G.molecule U (fun e => Mole.restrictLabels G κ e.1) b =
      κ (b.child R.positive)-κ (b.child R.negative) := by
  have hb := hU.2.2.1
  rw [gardenInternalFlow_external κ hp,(Mole.slotSum_eq_zero_iff G κ b).mpr (hc b hb),
    cl_externalSlotSum_lower hU R κ,slotWeight_child,slotWeight_child,R.positive_sign,R.negative_sign]
  simp only [Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,neg_neg,neg_smul,one_smul,zero_sub]
  abel

open Classical in
/-- The upper and lower gap equations follow from local conservation and
internal matching alone. No exterior leaf matching is assumed. -/
noncomputable def clPhysicalFlowFiber {E : Type} [AddCommGroup E] [Module ℝ E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (κ : GNode G.tree → E)
    (hc : ∀ v ∈ U, κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    FlowFiber G.molecule U a b E (κ (b.child R.positive)-κ (b.child R.negative)) := by
  classical
  let k : Bond G.molecule U → E := fun e => Mole.restrictLabels G κ e.1
  have hd := hU
  have hsum : flow G.molecule U k a + flow G.molecule U k b = 0 := by
    have hs := sum_flow_zero G.molecule U k
    have hpair : ({a,b} : Finset (GBranch G.tree)) ⊆ U := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hd.2.1
      · exact (Finset.mem_singleton.mp hv) ▸ hd.2.2.1
    have he : (∑ v ∈ ({a,b} : Finset (GBranch G.tree)), flow G.molecule U k v) =
        ∑ v ∈ U, flow G.molecule U k v := by
      apply Finset.sum_subset hpair
      intro v hv hn
      have hne : v ≠ a ∧ v ≠ b := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hn
      exact clInternalFlow_interior hU κ hc hp v hv hne.1 hne.2
    rw [Finset.sum_pair hd.2.2.2.1] at he
    exact he.trans hs
  refine ⟨k,?_,clInternalFlow_lower hU R κ hc hp,?_⟩
  · rw [clInternalFlow_lower hU R κ hc hp] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  · intro v hv ha hb
    exact clInternalFlow_interior hU κ hc hp v hv ha hb

end WaveTurbulence.VineEstS2
