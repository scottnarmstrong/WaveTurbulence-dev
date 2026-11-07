/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Same

/-! # V5 Step 4d-B: the untwisted half of the geometry (`SLow`)

`SLow P RS`: the upper block `S` has lower joint `b = P.lower` and kept slot `P.keep`.  Then the lower joint belongs to
`S.erase a`, and the pair of the retained leaf is a regional pair of `S`.  `STw.toSLow`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (RS : CLRegionData G S a b)

structure SLow : Prop where
  block : G.molecule.IsBlock S a b
  lower : b = P.lower
  keep : RS.kept = P.keep

variable {P RS} (h : SLow P RS)
include h

namespace SLow

theorem lower_mem : P.lower ∈ S := h.lower ▸ h.block.2.2.1

theorem lower_mem_erase : P.lower ∈ S.erase a := Finset.mem_erase.mpr ⟨fun he => h.block.2.2.2.1 (h.lower ▸ he.symm), h.lower_mem⟩

theorem b_mem_erase : b ∈ S.erase a := h.lower ▸ h.lower_mem_erase

theorem placement : IsPlacementAt G S P.lower P := by
  obtain ⟨hb, hl, hk⟩ := h
  subst hl
  refine ⟨rfl, fun i => ?_⟩
  rw [RS.lower i, hk]

theorem retained_internal : Mole.IsInternalLeaf G S P.retained := by
  have hpp := placement_paired_parent_mem G P h.placement
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  refine ⟨P.unmarked, retained_nonroot G P, P.paired_nonroot, ?_, hpp⟩
  show G.molecule.atom (retainedLP G P) ∈ S
  rw [ha]; exact h.lower_mem

theorem partner_internal : Mole.IsInternalLeaf G S (G.pair P.retained) :=
  (Mole.internal_leaf_pair_iff G S P.retained).mpr h.retained_internal

theorem p0_mem {hG : G.IsPlain} : pairOfLeaf G hG P.retained ∈ clRegionalPairs hG S := by
  rw [mem_clRegionalPairs]
  rcases LFTwist.pairOfLeaf_first_or_partner G hG P.retained with e | e
  · rw [e]; exact h.retained_internal
  · rw [e]; exact h.partner_internal

theorem pairedAt_ext {d : ℕ} {L : ℝ} {base β0 β1 : Mom d} (x : ExtS RS L base β0 β1) : PairedAt P x.1 :=
  x.2.1.2.2 P.retained h.retained_internal

end SLow

theorem STw.toSLow {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)}
    (h : STw P RS RS') : SLow P RS := ⟨h.block, h.lower, h.keep⟩

end WaveTurbulence.VineEstS5B
