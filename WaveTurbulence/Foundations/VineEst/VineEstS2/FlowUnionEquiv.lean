/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowRestriction

/-! # A proper source concatenation has the exact product flow fiber -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset RegRed
variable {V D E : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E]
variable {M : Molecule V D} {S T : Finset V} {a b c : V} {r : E}

/-- The two joint currents cancel at the shared atom. Every other source
flow equation is inherited from its unique actual piece. -/
noncomputable def glueFlowFiber (hM : M.IsMolecule) (hS : M.IsBlock S a b)
    (hT : M.IsBlock T b c) (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c)
    (kS : FlowFiber M S a b E r) (kT : FlowFiber M T b c E r) :
    FlowFiber M (S ∪ T) a c E r := by
  let k := glueBondLabels hM hS hT hi hU kS.1 kT.1
  have he (v : V) : flow M (S ∪ T) k v = flow M S kS.1 v+flow M T kT.1 v :=
    flow_glueBondLabels hM hS hT hi hU kS.1 kT.1 v
  have hout := block_concat_outer_not_mem hS hT hi
  refine ⟨k,?_,?_,?_⟩
  · rw [he,kS.2.1,flow_eq_zero_of_not_mem M T _ hout.1,add_zero]
  · rw [he,flow_eq_zero_of_not_mem M S _ hout.2,kT.2.2.1,zero_add]
  · intro v hv hva hvc
    rw [he]
    by_cases hvb : v = b
    · subst v
      rw [kS.2.2.1,kT.2.1,add_neg_cancel]
    · rcases Finset.mem_union.mp hv with hv | hv
      · have hvT : v ∉ T := by
          intro ht
          exact hvb (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hv,ht⟩))
        rw [kS.2.2.2 v hv hva hvb,flow_eq_zero_of_not_mem M T _ hvT,add_zero]
      · have hvS : v ∉ S := by
          intro hs
          exact hvb (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs,hv⟩))
        rw [flow_eq_zero_of_not_mem M S _ hvS,kT.2.2.2 v hv hvb hvc,zero_add]

theorem glueFlowFiber_val (hM : M.IsMolecule) (hS : M.IsBlock S a b)
    (hT : M.IsBlock T b c) (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c)
    (kS : FlowFiber M S a b E r) (kT : FlowFiber M T b c E r) :
    (glueFlowFiber hM hS hT hi hU kS kT).1 = glueBondLabels hM hS hT hi hU kS.1 kT.1 := by
  dsimp only [glueFlowFiber]

/-- Both inverse identities are identities of actual edge labels. This
product decomposition is proved from current source blocks and the full
source fiber, rather than postulated as a garden reparametrization premise. -/
noncomputable def flowUnionEquiv (hM : M.IsMolecule) (hS : M.IsBlock S a b)
    (hT : M.IsBlock T b c) (hi : S ∩ T = {b}) (hU : M.IsBlock (S ∪ T) a c) :
    FlowFiber M (S ∪ T) a c E r ≃ (FlowFiber M S a b E r × FlowFiber M T b c E r) where
  toFun k := (restrictFlowFiber_left hM hS hT hi hU k,restrictFlowFiber_right hM hS hT hi hU k)
  invFun p := glueFlowFiber hM hS hT hi hU p.1 p.2
  left_inv k := by
    apply Subtype.ext
    rw [glueFlowFiber_val,restrictFlowFiber_left_val,restrictFlowFiber_right_val,glue_restrictBondLabels]
  right_inv p := by
    rcases p with ⟨kS,kT⟩
    apply Prod.ext
    · apply Subtype.ext
      rw [restrictFlowFiber_left_val,glueFlowFiber_val,restrict_glueBondLabels_left]
    · apply Subtype.ext
      rw [restrictFlowFiber_right_val,glueFlowFiber_val,restrict_glueBondLabels_right]

end WaveTurbulence.VineEstS2
