/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionComponentEquiv
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # Removing one whole closed component lowers the global count by one -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem numComponents_erase_closed_component (M : Molecule V D) (Y : Finset V)
    (hboundary : Degen.boundaryDarts M Y = ∅) {a : V}
    (ha : a ∈ Y) (haM : a ∈ M.atoms) (hconn : ∀ c ∈ Y,M.SameComponent c a) :
    (Degen.eraseAtoms M Y).numComponents+1 = M.numComponents := by
  classical
  let q0 := appbComponent M ⟨a,haM⟩
  have hforget (q : AppbComponents (Degen.eraseAtoms M Y)) : eraseAtomsComponentForget M Y q ≠ q0 := by
    induction q using Quot.inductionOn with | h c =>
      intro he
      have hp := (quotient_eq_iff_sameComponent M ⟨c.val,(mem_sdiff.mp c.property).1⟩ ⟨a,haM⟩).mp he
      have hc := (Degen.sameComponent_mem_iff_of_boundary_empty M Y hboundary hp).mpr ha
      exact (mem_sdiff.mp c.property).2 hc
  let f : AppbComponents (Degen.eraseAtoms M Y) → {q : AppbComponents M // q ≠ q0} :=
    fun q => ⟨eraseAtomsComponentForget M Y q,hforget q⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro q q' he
      have he' := congrArg Subtype.val he
      induction q using Quot.inductionOn with | h c =>
        induction q' using Quot.inductionOn with | h d =>
          have hp := (quotient_eq_iff_sameComponent M
            ⟨c.val,(mem_sdiff.mp c.property).1⟩ ⟨d.val,(mem_sdiff.mp d.property).1⟩).mp he'
          apply (quotient_eq_iff_sameComponent (Degen.eraseAtoms M Y) c d).mpr
          apply eraseAtoms_sameComponent_of_boundary_connected M Y a ?_
            (mem_sdiff.mp c.property).2 (mem_sdiff.mp d.property).2 hp
          intro x hx
          rw [hboundary] at hx
          exact (notMem_empty x hx).elim
    · rintro ⟨q,hq⟩
      induction q using Quot.inductionOn with | h c =>
        have hc : c.val ∉ Y := by
          intro hy
          apply hq
          exact (quotient_eq_iff_sameComponent M c ⟨a,haM⟩).mpr (hconn c.val hy)
        refine ⟨appbComponent (Degen.eraseAtoms M Y) ⟨c.val,mem_sdiff.mpr ⟨c.property,hc⟩⟩,?_⟩
        exact Subtype.ext rfl
  letI : Fintype (AppbComponents M) := Fintype.ofFinite _
  letI : Fintype (AppbComponents (Degen.eraseAtoms M Y)) := Fintype.ofFinite _
  have he := Fintype.card_congr (Equiv.ofBijective f hbij)
  have hc := Fintype.card_subtype_compl (fun q : AppbComponents M => q = q0)
  have hq : Fintype.card {q : AppbComponents M // q = q0} = 1 := by simp
  rw [hq] at hc
  change Fintype.card (AppbComponents (Degen.eraseAtoms M Y)) =
    Fintype.card {q : AppbComponents M // ¬q = q0} at he
  rw [hc] at he
  have hp : 0 < Fintype.card (AppbComponents M) := Fintype.card_pos_iff.mpr ⟨q0⟩
  change Nat.card (AppbComponents (Degen.eraseAtoms M Y))+1 = Nat.card (AppbComponents M)
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
