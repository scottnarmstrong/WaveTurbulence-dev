/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Shape
public import WaveTurbulence.Foundations.Vine.B.SlotMap
/-! An exact characterization of the route's unit-valued branch.
This removes the arbitrary existential witness in the definition of `route`;
the remaining class-invariance obligation is equality of lower-parent incidence. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineB VineA RedSplice Represents Reg.Skeleton
variable {w : ℕ} {S G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
  {blk : J → CLBlock S} (Φ : SpliceShape blk G) (hd : Disj blk)

include hd

omit [Fintype J] in
/-- Distinct disjoint units have distinct lower joints. -/
theorem lower_injective : Function.Injective (fun j => (blk j).lower) := by
  intro j k he
  by_contra hjk
  exact Finset.disjoint_left.mp (hd j k hjk) (lower_mem _)
    (Eq.mpr (congrArg (fun b => b ∈ (blk k).atoms) he) (lower_mem (blk k)))

/-- The route selects unit j exactly when the original slot argument reads its lower clock. -/
theorem route_inr_iff (hS : S.IsPlain) (hG : G.IsPlain) (s : ReplacementSlot G) (i : Fin 2) (j : J) :
    Φ.route hS hG s i = Sum.inr j ↔
      argSrc hS (Φ.iota hS hG s) i = Sum.inr (blk j).lower := by
  classical
  constructor
  · exact Φ.route_inr hS hG
  · intro hj
    have hx : ∃ k, argSrc hS (Φ.iota hS hG s) i = Sum.inr (blk k).lower := ⟨j, hj⟩
    unfold SpliceShape.route
    rw [dite_eq_left hx]
    apply congrArg Sum.inr
    apply lower_injective hd
    exact Sum.inr.inj (hx.choose_spec.symm.trans hj)

/-- Equality of lower-parent incidence determines the complete route, including its outer branch. -/
theorem route_eq_of_lower_incidence {S' : Garden w} {blk' : J → CLBlock S'}
    (Ψ : SpliceShape blk' G) (hd' : Disj blk') (hS : S.IsPlain) (hS' : S'.IsPlain) (hG : G.IsPlain)
    (hinc : ∀ s i j, argSrc hS (Φ.iota hS hG s) i = Sum.inr (blk j).lower ↔
      argSrc hS' (Ψ.iota hS' hG s) i = Sum.inr (blk' j).lower) :
    Φ.route hS hG = Ψ.route hS' hG := by
  funext s i
  rcases Φ.route_natural hS hG s i with h | ⟨j, hj⟩
  · rcases Ψ.route_natural hS' hG s i with h' | ⟨j, hj⟩
    · exact h.trans h'.symm
    · have he := (route_inr_iff Φ hd hS hG s i j).mpr
        ((hinc s i j).mpr ((route_inr_iff Ψ hd' hS' hG s i j).mp hj))
      have hh := h.symm.trans he
      cases hh
  · exact hj.trans ((route_inr_iff Ψ hd' hS' hG s i j).mpr
      ((hinc s i j).mp ((route_inr_iff Φ hd hS hG s i j).mp hj))).symm

end WaveTurbulence.VineAlign
