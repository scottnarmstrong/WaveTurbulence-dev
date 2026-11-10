/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Partition
import Mathlib.Tactic

/-! # The2^n expansion size in DH23 Prop6.1 -/

public section
namespace WaveTurbulence.RegAsymp
open Finset Links

/-- The independent link count is exactly half the source order. -/
theorem links_length_eq_half {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2*n) :
    Q.links.length = n := by
  have h := couple_linksAt_length Q ((0 : Fin 2),[]) ((1 : Fin 2),[])
  change Q.links.length * 2 = Q.size at h
  omega

theorem chosenSet_card_eq_half {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2*n) :
    (chosenSet Q.links).card = n := by
  have h := card_chosenSet Q
  omega

/-- J3's powerset expansion has precisely2^n indices before zero terms
are removed; in particular the count has no factorial order loss. -/
theorem coefficient_index_card {Q : RegCpl} {n : ℕ} (hsize : Q.size = 2*n) :
    (chosenSet Q.links).powerset.card = 2^n := by
  rw [card_powerset,chosenSet_card_eq_half hsize]

end WaveTurbulence.RegAsymp
