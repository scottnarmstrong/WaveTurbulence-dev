/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Additive large-gap transport for an actual reinserted bond

The old boundary darts are removed by the atomic deletion. The new dart
at either endpoint has the same direction as its old boundary dart and
its physical label differs by at most epsilon. These are local source
data, rather than a post large-gap assumption.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_reinsert_largeGap (M : Molecule V D) (Y : Finset V) (a b : V)
    (ha : a ∈ M.atoms \ Y) (hb : b ∈ M.atoms \ Y)
    (ref : Bool → D) (hat : ∀ t,M.atom (ref t) = if t then a else b)
    (hdir : ∀ t,M.out (ref t) = t) (hdel : ∀ t,M.atom (M.mate (ref t)) ∈ Y)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (z : Fin d → ℤ)
    (g ε : ℝ) (hε : 0 ≤ ε) (hgap : AppbLargeGap M L w κ g)
    (hclose : ∀ t,‖Molecule.kvec L w κ (ref t) - (w + latticePoint L z)‖ ≤ ε) :
    AppbLargeGap (addBond (Degen.eraseAtoms M Y) a b) L w
      (Sum.elim (fun x : Degen.RetainedDart M Y => κ x.val) (fun _ : Bool => z)) (g-ε) := by
  intro v hv x hx y hy hxy hmate
  have hvat : v ∈ M.atoms := by
    change v ∈ insert a (insert b (M.atoms \ Y)) at hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (mem_sdiff.mp ha).1
    rcases mem_insert.mp hv with rfl | hv
    · exact (mem_sdiff.mp hb).1
    · exact (mem_sdiff.mp hv).1
  have hnew (t : Bool) (ht : (Sum.inr t : Degen.RetainedDart M Y ⊕ Bool) ∈
      (addBond (Degen.eraseAtoms M Y) a b).dartsAt v) : M.atom (ref t) = v := by
    have hh := (mem_filter.mp ht).2
    rw [hat]
    cases t <;> exact hh
  have hold (t : Bool) (u : Degen.RetainedDart M Y) : ref t ≠ M.mate u.val := by
    intro he
    have hh := hdel t
    rw [he,M.mate_mate u.val] at hh
    exact u.property.1 hh
  rcases x with x | t <;> rcases y with y | u
  · have hx' : x.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    have hy' : y.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
    have hh := hgap v hvat x.val hx' y.val hy' hxy (fun he => hmate (congrArg Sum.inl (Subtype.ext he)))
    exact (sub_le_self g hε).trans hh
  · have hx' : x.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
    have hu : ref u ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,hnew u hy⟩
    have hd : M.out x.val ≠ M.out (ref u) := by
      rw [hdir]
      exact hxy
    have hh := hgap v hvat x.val hx' (ref u) hu hd (hold u x)
    have ht := appb_gap_after_label_change (a := Molecule.kvec L w κ (ref u))
      (b := Molecule.kvec L w κ x.val) (by simpa only [norm_sub_rev] using hh) (hclose u)
    simpa only [Molecule.kvec,Sum.elim_inl,Sum.elim_inr,norm_sub_rev] using ht
  · have hy' : y.val ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
    have ht : ref t ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,hnew t hx⟩
    have hd : M.out (ref t) ≠ M.out y.val := by
      rw [hdir]
      exact hxy
    have hm : y.val ≠ M.mate (ref t) := by
      intro he
      exact hold t y (by rw [he,M.mate_mate])
    exact appb_gap_after_label_change (hgap v hvat (ref t) ht y.val hy' hd hm) (hclose t)
  · cases t <;> cases u
    · exact (hxy rfl).elim
    · exact (hmate rfl).elim
    · exact (hmate rfl).elim
    · exact (hxy rfl).elim

end WaveTurbulence.Mole
