/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowDartSum

/-! # Exact two-incidence joint flow in every abelian label group -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E]

/-- A joint with its actual two incidences has outgoing label minus incoming
label as its flow. A loop is also retained and cancels without an exception. -/
theorem flow_eq_outgoing_sub_incoming_of_deg_two (M : Molecule V D) (S : Finset V) (v : V)
    (hdeg : M.degIn S v = 2) (dOut dIn : InternalDart M S)
    (hOut : M.atom dOut.1 = v) (hIn : M.atom dIn.1 = v)
    (ho : M.out dOut.1 = true) (hi : M.out dIn.1 = false) (k : Bond M S → E) :
    flow M S k v = internalDartValue M S k dOut-internalDartValue M S k dIn := by
  classical
  have hne : dOut.1 ≠ dIn.1 := by
    intro he
    have h := congrArg M.out he
    rw [ho,hi] at h
    cases h
  let A := (M.dartsAt v).filter (M.InGroup S)
  have hpair : ({dOut.1,dIn.1} : Finset D) ⊆ A := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v dOut.1).mpr hOut,dOut.2⟩
    · have he := mem_singleton.mp hx
      subst x
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v dIn.1).mpr hIn,dIn.2⟩
  have hcard : A.card ≤ ({dOut.1,dIn.1} : Finset D).card := by
    change M.degIn S v ≤ _
    rw [hdeg,Finset.card_pair hne]
  have hA : A = {dOut.1,dIn.1} := (Finset.eq_of_subset_of_card_le hpair hcard).symm
  rw [flow_eq_internalDartsAt]
  change (∑ x ∈ A, (if M.out x = true then (1 : ℤ) else -1) • internalDartValueAt M S k x) = _
  rw [hA,Finset.sum_pair hne,internalDartValueAt_apply M S k dOut,
    internalDartValueAt_apply M S k dIn,ho,hi]
  simp only [ite_true,Bool.false_eq_true,ite_false,one_smul,neg_one_smul,sub_eq_add_neg]

end WaveTurbulence.VineEstS2
