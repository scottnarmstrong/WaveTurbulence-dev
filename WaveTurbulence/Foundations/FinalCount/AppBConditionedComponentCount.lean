/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertConditioned
public import WaveTurbulence.Foundations.FinalCount.AppBComponentRestriction
public import WaveTurbulence.Foundations.FinalCount.AppBComponentAdmissibility
import Mathlib.Tactic

/-! # Right-component counting after the left labels and local tuple are fixed -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Conditional graph helper for sequential component counting. The side
is an actual closed side, and both fixed-label conditions are coordinates
of the source fiber; no counting estimate is an input. -/
theorem appb_conditioned_component_fiber_encard_le
    (M : Molecule V D) (P : AppbPattern) (r : AppbRealization M P)
    (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices)
    (hka : a ∉ P.removed) (hkb : b ∉ P.removed) (i : Fin P.edges.length)
    (S : Finset V) (hS : AppbClosedSide (r.directedPostWithBond a b i) S)
    {d : ℕ} (p : AppbCountParameters M d) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin P.edges.length → (Fin d → ℤ))
    (ζ : AppbSideDart (r.directedPostWithBond a b i) S → (Fin d → ℤ)) :
    {κ | κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q ∧
      appbSideLabels (r.directedPostWithBond a b i) S (r.reinsertedLabels κ i) = ζ}.encard ≤
    appbCountE (appbSideMolecule (r.directedPostWithBond a b i)
      ((r.directedPostWithBond a b i).atoms \ S) hS.complement) L γ δ w
      (appbSideAdmissibility (r.directedPostWithBond a b i)
        ((r.directedPostWithBond a b i).atoms \ S) (r.reinsertedPostAdmissibility Adm i)) := by
  let N := r.directedPostWithBond a b i
  let R := N.atoms \ S
  let AdmR := appbSideAdmissibility N R (r.reinsertedPostAdmissibility Adm i)
  let pp := appbSideParameters R hS.complement (r.reinsertedParameters p L w q a b i)
  let f := fun κ : D → (Fin d → ℤ) => appbSideLabels N R (r.reinsertedLabels κ i)
  let T := {κ | κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q ∧
    appbSideLabels N S (r.reinsertedLabels κ i) = ζ}
  have hm : Set.MapsTo f T (pp.decorations L γ δ w AdmR) := by
    intro κ hκ
    have hh := r.reinserted_maps_conditioned p L γ δ w Adm a b ha hb hka hkb i hκ.1 hκ.2.1
    exact ⟨appb_isDecoration_side R hS.complement L w _ _ hh.1,
      appb_isRestricted_side R hS.complement L γ δ w _ _ _ hh.2.1,
      r.reinsertedLabels κ i,hh.2.2,rfl⟩
  have hi : Set.InjOn f T := by
    intro κ hκ κ' hκ' he
    have hp : r.reinsertedLabels κ i = r.reinsertedLabels κ' i :=
      appbSideLabelsPair_injective N S (Prod.ext (hκ.2.2.trans hκ'.2.2.symm) he)
    apply r.labels_injective hκ.1.1.1 hκ'.1.1.1 (hκ.2.1.trans hκ'.2.1.symm)
    funext x
    exact congrFun hp (Sum.inl x)
  refine (Set.encard_le_encard_of_injOn hm hi).trans ?_
  rw [appbCountE_eq_iSup]
  exact le_iSup_of_le pp le_rfl

end WaveTurbulence.Mole
