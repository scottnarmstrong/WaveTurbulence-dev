/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkIntervals
import Mathlib.Tactic

/-! # Unique maximal source parent of each selected link -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Finite maximal extension is fixed once for each actual link. -/
noncomputable def appbLinkParent (M : Molecule V D) (S : Finset V) : Finset V := by
  classical
  exact if h : AppbLink M S then
    (Degen.exists_sourceMaximalLadder_superset M h.sourceLadderSet).choose else ∅

theorem appbLinkParent_spec {M : Molecule V D} {S : Finset V} (hS : AppbLink M S) :
    appbLinkParent M S ∈ Degen.sourceMaximalLadders M ∧ S ⊆ appbLinkParent M S := by
  unfold appbLinkParent
  rw [dif_pos hS]
  exact (Degen.exists_sourceMaximalLadder_superset M hS.sourceLadderSet).choose_spec

theorem appbLinkParent_unique {M : Molecule V D} (hM : M.IsMolecule)
    {S T : Finset V} (hS : AppbLink M S) (hT : T ∈ Degen.sourceMaximalLadders M)
    (hST : S ⊆ T) : appbLinkParent M S = T := by
  by_contra hne
  have hd := Degen.sourceMaximalLadders_pairwiseDisjoint M hM
    (appbLinkParent_spec hS).1 hT hne
  have hnon : S.Nonempty := card_pos.mp (by rw [hS.card]; omega)
  obtain ⟨x,hx⟩ := hnon
  exact disjoint_left.mp hd ((appbLinkParent_spec hS).2 hx) (hST hx)

/-- The parent fiber is exactly the family of links contained in it. -/
theorem appbLinkParent_fiber {M : Molecule V D} (hM : M.IsMolecule)
    {T : Finset V} (hT : T ∈ Degen.sourceMaximalLadders M) :
    (appbLinks M).filter (fun S => appbLinkParent M S = T) =
      (appbLinks M).filter (fun S => S ⊆ T) := by
  classical
  apply filter_congr
  intro S hS
  have hlink := (mem_appbLinks M S).mp hS
  exact ⟨fun he => he ▸ (appbLinkParent_spec hlink).2,
    fun hsub => appbLinkParent_unique hM hlink hT hsub⟩

/-- The number of links assigned to a maximal ladder is its source length. -/
theorem appbLinkParent_fiber_card {M : Molecule V D} (hM : M.IsMolecule)
    {T : Finset V} (hT : T ∈ Degen.sourceMaximalLadders M) :
    ((appbLinks M).filter (fun S => appbLinkParent M S = T)).card = Molecule.ladderLength T := by
  classical
  rw [appbLinkParent_fiber hM hT]
  obtain ⟨m,u,v,hL,hT'⟩ := (mem_filter.mp hT).2.1
  rw [← hT',appbLinks_within_ladder_card hM hL]
  unfold Molecule.ladderLength
  rw [Degen.ladderAtoms_card_of_injective hL.2.1]
  omega

/-- On the source input, inheriting the maximal parent's prescribed scale
makes the refined link product exactly the DH23 defcounta2 ladder product. -/
theorem appbLinkProduct_eq_sourceLadderProduct (M : Molecule V D) (hM : M.IsMolecule)
    (L γ δ : ℝ) (P : Finset V → ℝ) :
    appbLinkProduct M L γ δ (fun S => P (appbLinkParent M S)) =
      Degen.sourceLadderProduct M L γ δ P := by
  classical
  unfold appbLinkProduct Degen.sourceLadderProduct
  rw [← prod_fiberwise_of_maps_to' (s := appbLinks M)
    (t := Degen.sourceMaximalLadders M)
    (fun S hS => (appbLinkParent_spec ((mem_appbLinks M S).mp hS)).1)
    (fun T => Molecule.ladderWeight L γ δ (P T))]
  apply prod_congr rfl
  intro T hT
  rw [prod_const,appbLinkParent_fiber_card hM hT]

end WaveTurbulence.Mole
