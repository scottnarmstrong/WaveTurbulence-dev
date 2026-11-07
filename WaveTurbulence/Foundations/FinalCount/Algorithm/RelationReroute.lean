/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DeletionReroute
import Mathlib.Tactic

/-! # Rerouting paths while retaining an explicit excluded-bond relation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Conditional path helper: each retained edge and each crossing is
realized in the target relation. This does not assume a bridge conclusion. -/
theorem reroute_path_in_relation (M : Molecule V D) (Y : Finset V) (b : V)
    (R : V → V → Prop) (e : D)
    (hret : ∀ x : D,M.atom x ∉ Y → M.atom (M.mate x) ∉ Y →
      x ≠ e → x ≠ M.mate e → Relation.EqvGen R (M.atom x) (M.atom (M.mate x)))
    (hboundary : ∀ x : D,M.atom x ∈ Y → M.atom (M.mate x) ∉ Y →
      Relation.EqvGen R b (M.atom (M.mate x)))
    {a c : V} (hp : Relation.EqvGen (Degen.AdjWithoutBond M e) a c) :
    Relation.EqvGen R (rerouteAtom Y b a) (rerouteAtom Y b c) := by
  have hstep (a c : V) (h : Degen.AdjWithoutBond M e a c) :
      Relation.EqvGen R (rerouteAtom Y b a) (rerouteAtom Y b c) := by
    obtain ⟨x,rfl,rfl,hxe,hxm⟩ := h
    by_cases hx : M.atom x ∈ Y <;> by_cases hy : M.atom (M.mate x) ∈ Y
    · simp only [rerouteAtom,hx,hy,ite_true]
      exact Relation.EqvGen.refl _
    · simpa only [rerouteAtom,hx,hy,ite_true,ite_false] using hboundary x hx hy
    · have hh := hboundary (M.mate x) hy (by simpa only [M.mate_mate] using hx)
      rw [M.mate_mate] at hh
      simpa only [rerouteAtom,hx,hy,ite_true,ite_false] using hh.symm
    · simpa only [rerouteAtom,hx,hy,ite_false] using hret x hx hy hxe hxm
  induction hp with
  | rel a c h => exact hstep a c h
  | refl a => exact Relation.EqvGen.refl _
  | symm a c hp ih => exact ih.symm
  | trans a c d hp hp' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

end WaveTurbulence.Mole.AppbAlgorithm
