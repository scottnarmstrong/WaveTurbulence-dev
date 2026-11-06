/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSpliceCut
public import WaveTurbulenceVineParam.VineParamGraphSpliceCell
import Mathlib.Tactic

/-! # Global source conservation forces the inserted rung's physical gap

The gap is determined by the cap's joint memberships. It is derived from
source cut flow and both fresh conservation rows, never supplied as an
additional parametrization premise.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- The signed root gap read from the two old joint memberships. -/
@[expose] def spliceGap (C : Finset V) (a b : V) (r : E) : E :=
  ((if a ∈ C then (1 : ℤ) else 0)-(if b ∈ C then (1 : ℤ) else 0)) • r

/-- Root/interior conservation forces exactly the incoming physical gap
required by the local rung chart. -/
theorem rungSplice_preceding_gap (ends : β → V×V) (i j : β) (σ : V ≃ V)
    (p q c d a b : V) (hab : a ≠ b) (P : RungPattern) (C : Finset V)
    (hσ : ∀ v,σ v ∈ C ↔ v ∈ C)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (old : {e : β // e ≠ i ∧ e ≠ j} → E) (z : Fin 6 → E) (r : E)
    (ha : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl a) (rungSpliceLabels i j old z)= -r)
    (hb : directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl b) (rungSpliceLabels i j old z)=r)
    (hzero : ∀ v,v ≠ .inl a → v ≠ .inl b →
      directedFlow (rungSpliceEnds ends i j σ p q c d P) v (rungSpliceLabels i j old z)=0) :
    z 0=P.upperBefore (spliceGap C a b r) (z 1) := by
  have hcut := cap_flow_from_joints (rungSpliceEnds ends i j σ p q c d P)
    (spliceCap C) (rungSpliceLabels i j old z) (.inl a) (.inl b)
    (by intro h; exact hab (Sum.inl.inj h)) (by intro v _hv hva hvb; exact hzero v hva hvb)
  rw [rungSpliceCut_flux ends i j σ p q c d P C hσ hrest hp hq hc hd old z] at hcut
  simp only [mem_spliceCap_inl,ha,hb] at hcut
  have hcut' : -(P.signs 3) • z 4+P.signs 3 • z 5= -spliceGap C a b r := by
    rw [hcut]
    by_cases hca : a ∈ C <;> by_cases hcb : b ∈ C <;>
      simp [spliceGap,hca,hcb]
  have hu := hzero (.inr 0) (by simp) (by simp)
  have hl := hzero (.inr 1) (by simp) (by simp)
  rw [rungSpliceFlow_upper] at hu
  rw [rungSpliceFlow_lower] at hl
  have hprev := P.oriented_gap_transport (z 2) (z 3) (z 0) (z 1) (z 4) (z 5)
    hu (neg_eq_zero.mp hl)
  apply P.upperBefore_of_gap
  exact hprev.trans (P.outgoing_gap_of_cut_flux _ _ _ hcut')

end WaveTurbulence.Vine.Param
