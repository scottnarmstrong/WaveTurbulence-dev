/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Appendix B large-gap predicates and literal deletion

The lower gap threshold is a parameter, permitting the source's controlled
loss from L^(-gamma+eta) to half that value over a sequence of operations.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- All oppositely oriented incidences have physical label separation at
least g. No same-bond pair is included; Appendix B also excludes loops. -/
def AppbLargeGap (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (g : ℝ) : Prop :=
  ∀ v ∈ M.atoms, ∀ x ∈ M.dartsAt v, ∀ y ∈ M.dartsAt v,
    M.out x ≠ M.out y → y ≠ M.mate x →
    g ≤ ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖

/-- Exact LG preservation for deletion, with no threshold loss. -/
theorem appb_largeGap_eraseAtoms (M : Molecule V D) (Y : Finset V) {d : ℕ}
    {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {g : ℝ}
    (h : AppbLargeGap M L w κ g) :
    AppbLargeGap (Degen.eraseAtoms M Y) L w (fun x => κ x.val) g := by
  intro v hv x hx y hy hdir hmate
  have hv' := (mem_sdiff.mp hv).1
  have hx' : x.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have hy' : y.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
  have hm : y.val ≠ M.mate x.val := by
    intro he
    exact hmate (Subtype.ext he)
  exact h v hv' x.val hx' y.val hy' hdir hm

/-- The triangle estimate used when the reinserted boundary label differs
from the old one by at most epsilon. This is the exact additive LG loss. -/
theorem appb_gap_after_label_change {d : ℕ} {a b c : Mom d} {g ε : ℝ}
    (hgap : g ≤ ‖a - b‖) (hchange : ‖a - c‖ ≤ ε) : g - ε ≤ ‖c - b‖ := by
  have htri : ‖a-b‖ ≤ ‖a-c‖ + ‖c-b‖ := by
    calc
      ‖a-b‖ = ‖(a-c)+(c-b)‖ := by congr 1; module
      _ ≤ _ := norm_add_le _ _
  linarith only [hgap,hchange,htri]

/-- Source iteration bookkeeping: n successive additive errors epsilon
leave at least half the initial gap when n*epsilon ≤ initialGap/2. -/
theorem appb_iterated_gap_half (initialGap ε : ℝ) (n : ℕ)
    (h : (n : ℝ) * ε ≤ initialGap / 2) : initialGap / 2 ≤ initialGap - n * ε := by
  linarith only [h]

end WaveTurbulence.Mole
