/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSourceOrigins

/-! # Internal bond tags use only source pairs and interior branches -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

def interiorSourceTag (R : CLRegionData G U a b) :
    Fin (clLocalOrder1 R) ⊕ Fin (clLocalOrder1 R) → CLSourceOrigin R
  | .inl p => .inl p
  | .inr v => .inr (.inl v)

/-- An actual realization node contributes no artificial upper boundary
tag: it is an interior branch or one of the actual source leaf pairs. -/
theorem clRealizedNode_interiorOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ o : Fin (clLocalOrder1 R) ⊕ Fin (clLocalOrder1 R),
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        κ x = clSourceOriginValue hU R hG Ei Ep κ (interiorSourceTag R o) := by
  rcases (mem_clRealizationNodes x).mp hx with ⟨v,hv,rfl⟩ | ⟨ℓ,hℓ,rfl⟩
  · let z : ↥(clInteriorBranches R) := ⟨v,Finset.mem_erase.mpr
      ⟨fun he => hne (congrArg GBranch.toNode he),hv⟩⟩
    refine ⟨.inr (Ei.e z),?_⟩
    intro E _ κ _
    simp only [interiorSourceTag,clSourceOriginValue,clOrderedBranchValue,Equiv.symm_apply_apply]
    rfl
  · obtain ⟨l,hl⟩ := clInternalLeaf_surjective hU R ℓ hℓ
    obtain ⟨p,c,hside⟩ := clTreeLeaf_internal_side_exists hU R hG l ℓ hl hℓ
    have ho : clLeafOrigin hU R hG l = .inl p := by
      rw [← hside]
      fin_cases c
      · exact clLeafOrigin_first hU R hG p
      · exact clLeafOrigin_second hU R hG p
    refine ⟨.inl (Ep p),?_⟩
    intro E _ κ hp
    have he := clLeafOrigin_value hU R hG κ hp l
    rw [hl,ho] at he
    simpa only [interiorSourceTag,clSourceOriginValue,clOrderedPairValue,Equiv.symm_apply_apply] using he

theorem clBond_interiorOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (e : Bond G.molecule U) :
    ∃ o : Fin (clLocalOrder1 R) ⊕ Fin (clLocalOrder1 R),
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        Mole.restrictLabels G κ e.1 = clSourceOriginValue hU R hG Ei Ep κ (interiorSourceTag R o) := by
  let d := internalBondDart G.molecule U (e,false)
  exact clRealizedNode_interiorOrigin hU R hG Ei Ep (Mole.dartNode G d.1)
    ((mem_clRealizationNodes _).mpr (internalDart_node_realization d))
    (clInternalDart_node_ne_upper R d)

end WaveTurbulence.VineEstS2
