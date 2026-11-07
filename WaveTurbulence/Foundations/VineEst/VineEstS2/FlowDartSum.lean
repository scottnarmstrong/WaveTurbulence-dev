/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalFlowSum
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic

/-! # Exact M9 flow as a sum over the actual internal darts at one atom -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E]

noncomputable def internalDartValueAt (M : Molecule V D) (S : Finset V) (k : Bond M S → E) (x : D) : E := by
  classical
  exact if hx : M.InGroup S x then internalDartValue M S k ⟨x,hx⟩ else 0

theorem internalDartValueAt_apply (M : Molecule V D) (S : Finset V) (k : Bond M S → E)
    (x : InternalDart M S) : internalDartValueAt M S k x.1 = internalDartValue M S k x := by
  classical
  exact dite_eq_left x.2

open Classical in
/-- The atom filter is a literal raw dart family, with each incoming and
outgoing occurrence kept even for a loop. -/
theorem flow_eq_internalDartsAt (M : Molecule V D) (S : Finset V) (k : Bond M S → E) (v : V) :
    flow M S k v = ∑ x ∈ (M.dartsAt v).filter (M.InGroup S),
      (if M.out x = true then (1 : ℤ) else -1) • internalDartValueAt M S k x := by
  classical
  rw [← internalDartFlow_eq_flow]
  let F : InternalDart M S → E := fun x => internalDartCoeff M v x.1 • internalDartValue M S k x
  let A : Finset (InternalDart M S) := Finset.univ.filter (fun x => M.atom x.1 = v)
  have he : (∑ x, F x) = ∑ x ∈ A, F x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hn
    have hx : M.atom x.1 ≠ v := by
      intro hx
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    unfold F internalDartCoeff
    by_cases ho : M.out x.1 = true <;>
      simp only [ho,hx,Bool.false_eq_true,ite_true,ite_false,neg_zero,zero_smul]
  change (∑ x, F x) = _
  rw [he]
  apply Finset.sum_bij (fun x _ => x.1)
  · intro x hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v x.1).mpr (mem_filter.mp hx).2,x.2⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hv,hg⟩ := mem_filter.mp hx
    exact ⟨⟨x,hg⟩,mem_filter.mpr ⟨mem_univ _,(Mole.mem_dartsAt M v x).mp hv⟩,rfl⟩
  · intro x hx
    have hv := (mem_filter.mp hx).2
    unfold F internalDartCoeff
    rw [internalDartValueAt_apply]
    simp only [hv,ite_true]

end WaveTurbulence.VineEstS2
