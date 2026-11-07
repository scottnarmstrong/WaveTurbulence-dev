/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideLinks
public import WaveTurbulence.Foundations.FinalCount.AppBComponentAdmissibility
public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
import Mathlib.Tactic

/-! # Component projection preserves the physical input hypotheses -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem largeGap_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {g : ℝ}
    (h : AppbLargeGap M L w κ g) :
    AppbLargeGap (appbSideMolecule M S hS) L w (appbSideLabels M S κ) g := by
  intro a ha x hx y hy hdir hmate
  have hx' : x.val ∈ M.dartsAt a := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have hy' : y.val ∈ M.dartsAt a := mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
  have hm : y.val ≠ M.mate x.val := fun he => hmate (Subtype.ext he)
  exact h a (hS.subset_atoms ha) x.val hx' y.val hy' hdir hm

theorem projected_largeGap_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L : ℝ} {w : Mom d} {A : (D → (Fin d → ℤ)) → Prop} {g : ℝ}
    (h : ∀ κ,A κ → AppbLargeGap M L w κ g) :
    ∀ ζ,appbSideAdmissibility M S A ζ →
      AppbLargeGap (appbSideMolecule M S hS) L w ζ g := by
  rintro ζ ⟨κ,hκ,rfl⟩
  exact largeGap_closed_side M S hS (h κ hκ)

theorem validLinkScales_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L c : ℝ} {w : Mom d} {A : (D → (Fin d → ℤ)) → Prop} {P : Finset V → ℝ}
    (h : AppbValidLinkScales M L w A c P) :
    AppbValidLinkScales (appbSideMolecule M S hS) L w (appbSideAdmissibility M S A) c P := by
  constructor
  · intro T hT
    exact h.1 T ((link_closed_side_iff M S hS T).mp hT).1
  · intro u v hL ζ hζ g hg hp
    obtain ⟨κ,hκ,rfl⟩ := hζ
    obtain ⟨x,y,hx,hy,hax,hay,hg⟩ := hg
    exact h.2 u v ((sourceLadder_closed_side_iff M S hS u v).mp hL).1 κ hκ g
      ⟨x.val,y.val,hx,hy,hax,hay,hg⟩ hp

theorem projected_mate_labels_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {A : (D → (Fin d → ℤ)) → Prop}
    (h : ∀ κ,A κ → ∀ x,κ (M.mate x) = κ x) :
    ∀ ζ,appbSideAdmissibility M S A ζ →
      ∀ x,ζ ((appbSideMolecule M S hS).mate x) = ζ x := by
  rintro ζ ⟨κ,hκ,rfl⟩ x
  exact h κ hκ x.val

end WaveTurbulence.Mole.AppbAlgorithm
