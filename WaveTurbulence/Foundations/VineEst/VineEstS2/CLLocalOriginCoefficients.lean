/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOriginIncidences

/-! # Precise garden consequence of the proposed M9 local witness -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Conditional geometry helper. Actual opposite-incidence origin tags
produce a unit inverse row in the original regional leaf-pair basis. -/
theorem clLocalOrigin_difference_coeffs (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (p q : Bond G.molecule U ⊕ Fin 2)
    (v : GBranch G.tree) (hv : v ∈ U) (out : Bool)
    (hp : OriginAt G.molecule U b p v out) (hq : OriginAt G.molecule U b q v (!out)) :
    ∃ σ : ↥(clRegionalPairs hG U) ⊕ Fin 4 → ℤ, (∀ o, IsUnitCoeff (σ o)) ∧
      ∀ {E : Type} [AddCommGroup E] (κ : GNode G.tree → E),
        (∀ z ∈ U, κ z.toNode = κ (z.child 0)-κ (z.child 1)+κ (z.child 2)) →
        (∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) →
        let labels := fun e : Bond G.molecule U => Mole.restrictLabels G κ e.1
        let g := κ (clBoundaryNodes R 2)
        let r := g-κ (clBoundaryNodes R 3)
        origin G.molecule U labels g r p-origin G.molecule U labels g r q =
          ∑ o, σ o • clOriginValue hU R hG κ o := by
  obtain ⟨i,hi,hpi⟩ := originAt_source_slot R p v out hp
  obtain ⟨j,hj,hqj⟩ := originAt_source_slot R q v (!out) hq
  have hs : Mole.slotWeight G v i = -Mole.slotWeight G v j := by
    rw [hi,hj]
    cases out <;> norm_num
  obtain ⟨σ,hσ,he⟩ := clSlot_difference_coeffs hU R hG v hv i j hs
  refine ⟨σ,hσ,?_⟩
  intro E _ κ hc hmatch
  exact (congrArg₂ (fun x y : E => x-y) (hpi κ hmatch) (hqj κ hmatch)).trans (he κ hc hmatch)

end WaveTurbulence.VineEstS2
