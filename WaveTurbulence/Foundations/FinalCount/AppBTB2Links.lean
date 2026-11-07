/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalMultiplicity
public import WaveTurbulence.Foundations.FinalCount.AppBLinkDeletion
import Mathlib.Tactic

/-! # TB-2N preserves the actual selected-link product -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_tb2_no_double_partner (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb2.pattern) :
    ∀ a ∈ r.removedAtoms,∀ b : V,M.bondsBetween a b ≠ 2 := by
  intro a ha b
  rw [r.bondsBetween_eq_local_sum ha b]
  change (∑ i : Fin 4,if M.ends (r.edge i).val = s(a,b) then 1 else 0) ≠ 2
  rw [Fin.sum_univ_four]
  change ((if M.ends (r.edge ⟨0,by decide⟩).val = s(a,b) then 1 else 0)+
    (if M.ends (r.edge ⟨1,by decide⟩).val = s(a,b) then 1 else 0)+
    (if M.ends (r.edge ⟨2,by decide⟩).val = s(a,b) then 1 else 0)+
    (if M.ends (r.edge ⟨3,by decide⟩).val = s(a,b) then 1 else 0)) ≠ 2
  simp only [r.endpoints]
  change ((if s(r.vertex 1,r.vertex 2) = s(a,b) then 1 else 0)+
    (if s(r.vertex 1,r.vertex 2) = s(a,b) then 1 else 0)+
    (if s(r.vertex 1,r.vertex 2) = s(a,b) then 1 else 0)+
    (if s(r.vertex 2,r.vertex 3) = s(a,b) then 1 else 0)) ≠ 2
  by_cases h1 : s(r.vertex 1,r.vertex 2) = s(a,b) <;>
    by_cases h2 : s(r.vertex 2,r.vertex 3) = s(a,b) <;> simp [h1,h2]

theorem appb_tb2_linkProduct (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb2.pattern) (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct r.post L γ δ P = appbLinkProduct M L γ δ P := by
  change appbLinkProduct (Degen.eraseAtoms M r.removedAtoms) L γ δ P = _
  unfold appbLinkProduct
  rw [appbLinks_eraseAtoms_no_double_partner M r.removedAtoms]
  intro a ha b hb hne
  exact appb_tb2_no_double_partner M r a ha b

end WaveTurbulence.Mole
