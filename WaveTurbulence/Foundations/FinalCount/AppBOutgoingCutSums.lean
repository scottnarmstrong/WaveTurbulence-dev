/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingSums
public import WaveTurbulence.Foundations.FinalCount.AppBLocalCuts
import Mathlib.Tactic

/-! # Cut conservation in the actual outgoing local coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_sum_cut_outgoing (M : Molecule V D) (S : Finset V)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ v ∈ S,∑ x ∈ M.dartsAt v,g x) = ∑ x ∈ M.bonds,
      ((if M.atom x ∈ S then g x else 0)-(if M.atom (M.mate x) ∈ S then g x else 0)) := by
  classical
  simp_rw [appb_sum_dartsAt_outgoing M _ g hg]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  rw [sum_sub_distrib]
  simp only [sum_ite_eq]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A cut crossing only enumerated local bonds has an exact momentum
identity in those actual labels. The right side depends only on old
source parameters and the concrete graph cut. -/
theorem cut_momentum {d : ℕ} (S : Finset V) (hS : S ⊆ M.atoms)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms)
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) :
    (∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val ∈ S then Molecule.kvec L w (r.localLabels κ) i else 0)-
        (if M.atom (M.mate (r.edge i).val) ∈ S then Molecule.kvec L w (r.localLabels κ) i else 0))) =
      ∑ v ∈ S,c v := by
  classical
  let g := fun x => M.dartSign x • Molecule.kvec L w κ x
  have hg : ∀ x,g (M.mate x) = -g x := by
    intro x
    dsimp only [g]
    rw [Degen.dartSign_mate,Molecule.kvec,hκ.1 x,neg_smul]
    rfl
  have hs := appb_sum_cut_outgoing M S g hg
  have hsource : (∑ v ∈ S,∑ x ∈ M.dartsAt v,g x) = ∑ v ∈ S,c v :=
    sum_congr rfl (fun v hv => hκ.2 v (hS hv))
  rw [hsource] at hs
  have hlocal : (∑ x ∈ appbRemovedBonds M r.removedAtoms,
      ((if M.atom x ∈ S then g x else 0)-(if M.atom (M.mate x) ∈ S then g x else 0))) =
      ∑ x ∈ M.bonds,((if M.atom x ∈ S then g x else 0)-(if M.atom (M.mate x) ∈ S then g x else 0)) := by
    apply sum_subset (filter_subset _ _)
    intro x hx hn
    by_cases h1 : M.atom x ∈ S <;> by_cases h2 : M.atom (M.mate x) ∈ S
    · simp only [h1,h2,ite_true,sub_self]
    · exact False.elim (hn (hcross (mem_filter.mpr ⟨hx,Or.inl ⟨h1,h2⟩⟩)))
    · exact False.elim (hn (hcross (mem_filter.mpr ⟨hx,Or.inr ⟨h1,h2⟩⟩)))
    · simp only [h1,h2,ite_false,sub_zero]
  rw [← hlocal,← r.removedBond_sum] at hs
  rw [hs]
  apply sum_congr rfl
  intro i hi
  have ho : M.out (r.edge i).val = true := (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  simp only [g,Molecule.dartSign,ho,ite_true,one_smul,Molecule.kvec,localLabels]

end AppbRealization
end WaveTurbulence.Mole
