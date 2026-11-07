/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNodeBonds

/-! # Every internal bond origin is an actual pair or branch source label -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

abbrev CLSourceOrigin (R : CLRegionData G U a b) :=
  Fin (clLocalOrder1 R) ⊕ (Fin (clLocalOrder1 R) ⊕ Fin 4)

noncomputable def clSourceOriginValue {E : Type*} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (κ : GNode G.tree → E) : CLSourceOrigin R → E
  | .inl p => clOrderedPairValue hU R hG Ep κ p
  | .inr (.inl v) => clOrderedBranchValue hU R Ei κ v
  | .inr (.inr c) => κ (clBoundaryNodes R c)

/-- Classification depends only on original source geometry, and works
uniformly for every internally matched regional label assignment. -/
theorem clRealizedNode_sourceOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ o : CLSourceOrigin R, ∀ {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        κ x = clSourceOriginValue hU R hG Ei Ep κ o := by
  rcases (mem_clRealizationNodes x).mp hx with ⟨v,hv,rfl⟩ | ⟨ℓ,hℓ,rfl⟩
  · let z : ↥(clInteriorBranches R) := ⟨v,Finset.mem_erase.mpr
      ⟨fun he => hne (congrArg GBranch.toNode he),hv⟩⟩
    refine ⟨.inr (.inl (Ei.e z)),?_⟩
    intro E _ κ _
    simp only [clSourceOriginValue,clOrderedBranchValue,Equiv.symm_apply_apply]
    rfl
  · obtain ⟨l,hl⟩ := clInternalLeaf_surjective hU R ℓ hℓ
    cases ho : clLeafOrigin hU R hG l with
    | inl p =>
      refine ⟨.inl (Ep p),?_⟩
      intro E _ κ hp
      have he := clLeafOrigin_value hU R hG κ hp l
      rw [hl,ho] at he
      simpa only [clSourceOriginValue,clOrderedPairValue,Equiv.symm_apply_apply] using he
    | inr c =>
      refine ⟨.inr (.inr c),?_⟩
      intro E _ κ hp
      have he := clLeafOrigin_value hU R hG κ hp l
      rw [hl,ho] at he
      exact he

theorem clBond_sourceOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (e : Bond G.molecule U) :
    ∃ o : CLSourceOrigin R, ∀ {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        Mole.restrictLabels G κ e.1 = clSourceOriginValue hU R hG Ei Ep κ o := by
  let d := internalBondDart G.molecule U (e,false)
  exact clRealizedNode_sourceOrigin hU R hG Ei Ep (Mole.dartNode G d.1)
    ((mem_clRealizationNodes _).mpr (internalDart_node_realization d))
    (clInternalDart_node_ne_upper R d)

/-- The two remaining origin tags are exactly the actual lower boundary
nodes, not unspecified affine combinations. -/
theorem clOrigin_sourceOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (p : Bond G.molecule U ⊕ Fin 2) :
    ∃ o : CLSourceOrigin R, ∀ {E : Type*} [AddCommGroup E] (κ : GNode G.tree → E),
      (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
      origin G.molecule U (fun e => Mole.restrictLabels G κ e.1)
        (κ (clBoundaryNodes R 2)) (κ (clBoundaryNodes R 2)-κ (clBoundaryNodes R 3)) p =
        clSourceOriginValue hU R hG Ei Ep κ o := by
  cases p with
  | inl e => exact clBond_sourceOrigin hU R hG Ei Ep e
  | inr j =>
    by_cases hj : j = 0
    · refine ⟨.inr (.inr 2),?_⟩
      intro E _ κ _
      simp only [origin,hj,ite_true,clSourceOriginValue]
    · refine ⟨.inr (.inr 3),?_⟩
      intro E _ κ _
      simp only [origin,hj,ite_false,sub_sub_cancel,clSourceOriginValue]

end WaveTurbulence.VineEstS2
