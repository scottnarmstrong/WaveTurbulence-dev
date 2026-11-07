/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabels
import Mathlib.Tactic

/-! # Explicit post-deletion parameters determined by local labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Complete the deleted bond labels by zero away from deleted bonds.
Incoming labels use their unique outgoing mate representative. -/
noncomputable def completeLocalLabels [Zero K] (q : Fin P.edges.length → K) (x : D) : K := by
  classical
  exact if M.out x = true then
    if h : x ∈ appbRemovedBonds M r.removedAtoms then q (r.edge.symm ⟨x,h⟩) else 0
  else if h : M.mate x ∈ appbRemovedBonds M r.removedAtoms then
    q (r.edge.symm ⟨M.mate x,h⟩) else 0

private theorem localLabel_at_removed {κ : D → K} {q : Fin P.edges.length → K}
    (hq : r.localLabels κ = q) {x : D} (hx : x ∈ appbRemovedBonds M r.removedAtoms) :
    κ x = q (r.edge.symm ⟨x,hx⟩) := by
  have he := congrFun hq (r.edge.symm ⟨x,hx⟩)
  change κ (r.edge (r.edge.symm ⟨x,hx⟩)).val = _ at he
  simpa only [r.edge.apply_symm_apply] using he

/-- Every physically removed label agrees with the explicit local completion. -/
theorem completeLocalLabels_eq [Zero K] {κ : D → K} {q : Fin P.edges.length → K}
    (hκ : ∀ x, κ (M.mate x) = κ x) (hq : r.localLabels κ = q) {x : D}
    (hdel : M.atom x ∈ r.removedAtoms ∨ M.atom (M.mate x) ∈ r.removedAtoms) :
    κ x = r.completeLocalLabels q x := by
  classical
  cases ho : M.out x
  · have hm : M.mate x ∈ appbRemovedBonds M r.removedAtoms := by
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
      · rw [M.out_mate,ho]; rfl
      · simpa only [M.mate_mate,or_comm] using hdel
    have he := r.localLabel_at_removed hq hm
    rw [hκ x] at he
    simpa only [completeLocalLabels,ho,Bool.false_eq_true,ite_false,dite_eq_left hm] using he
  · have hx : x ∈ appbRemovedBonds M r.removedAtoms :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,hdel⟩
    simpa only [completeLocalLabels,ho,ite_true,dite_eq_left hx] using r.localLabel_at_removed hq hx

/-- Residual momentum parameters depend only on the local tuple q. -/
theorem residualMomentum_eq_local {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    {κ : D → (Fin d → ℤ)} {q : Fin P.edges.length → (Fin d → ℤ)}
    (hκ : ∀ x, κ (M.mate x) = κ x) (hq : r.localLabels κ = q) :
    Degen.residualMomentum M r.removedAtoms L w c κ =
      Degen.residualMomentum M r.removedAtoms L w c (r.completeLocalLabels q) := by
  funext v
  unfold Degen.residualMomentum
  congr 1
  apply sum_congr rfl
  intro x hx
  have hd := (mem_filter.mp hx).2
  rw [Molecule.kvec,r.completeLocalLabels_eq hκ hq (Or.inr hd)]
  rfl

/-- Residual energy centers likewise depend only on q. -/
theorem residualEnergy_eq_local {d : ℕ} (L : ℝ) (w : Mom d) (β : V → ℝ)
    {κ : D → (Fin d → ℤ)} {q : Fin P.edges.length → (Fin d → ℤ)}
    (hκ : ∀ x, κ (M.mate x) = κ x) (hq : r.localLabels κ = q) :
    Degen.residualEnergy M r.removedAtoms L w β κ =
      Degen.residualEnergy M r.removedAtoms L w β (r.completeLocalLabels q) := by
  funext v
  unfold Degen.residualEnergy
  congr 1
  apply sum_congr rfl
  intro x hx
  have hd := (mem_filter.mp hx).2
  rw [Molecule.kvec,r.completeLocalLabels_eq hκ hq (Or.inr hd)]
  rfl

end AppbRealization
end WaveTurbulence.Mole
