/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingCutSums
import Mathlib.Tactic

/-! # Exact outgoing cut sums and their source energy windows -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem cut_incidence_sum (S : Finset V)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms)
    {E : Type*} [AddCommGroup E] (g : D → E) (hg : ∀ x,g (M.mate x) = -g x) :
    (∑ v ∈ S,∑ x ∈ M.dartsAt v,g x) = ∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val ∈ S then g (r.edge i).val else 0)-
        (if M.atom (M.mate (r.edge i).val) ∈ S then g (r.edge i).val else 0)) := by
  classical
  have hs := appb_sum_cut_outgoing M S g hg
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
  exact hs

/-- DH21 Lemma 9.14, in the actual local labels of a concrete cut. The
window has width card(S) times the original atomic window. -/
theorem cut_energy (S : Finset V) (hS : S ⊆ M.atoms)
    (hcross : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |(∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val ∈ S then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0)-
        (if M.atom (M.mate (r.edge i).val) ∈ S then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0)))-
      ∑ v ∈ S,β v| ≤ S.card*(δ⁻¹*L^(-2*γ)) := by
  have he := r.cut_incidence_sum S hcross
    (fun x => M.dartSign x*‖Molecule.kvec L w κ x‖^2) (fun x => by
      rw [Degen.dartSign_mate,Molecule.kvec,hκ.1 x,neg_mul]
      rfl)
  have hΓ : (∑ v ∈ S,M.Gamma L w κ v) = ∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val ∈ S then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0)-
        (if M.atom (M.mate (r.edge i).val) ∈ S then ‖Molecule.kvec L w (r.localLabels κ) i‖^2 else 0)) := by
    refine he.trans ?_
    apply sum_congr rfl
    intro i hi
    have ho : M.out (r.edge i).val = true := (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
    simp only [Molecule.dartSign,ho,ite_true,one_mul,Molecule.kvec,localLabels]
  rw [← hΓ,← sum_sub_distrib]
  calc
    _ ≤ ∑ v ∈ S,|M.Gamma L w κ v-β v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S,δ⁻¹*L^(-2*γ) := sum_le_sum (fun v hv => hres.1 v (hS hv))
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

end AppbRealization
end WaveTurbulence.Mole
