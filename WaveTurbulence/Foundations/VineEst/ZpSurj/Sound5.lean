/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound4

/-! # ZP-SURJ soundness: every LF construction yields an exceptional datum -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (con : LFConstruction s ε)

theorem conLX_pattern :
    TreePatternN (conLX con) (parAt (s.base ε) p (tA s ε)) con.newTree (srcSign s ε) ((0 : Fin 1), ([] : Path)) := by
  have hpat := con.treeInsertion.pattern
  rw [treePattern_eq_N] at hpat
  have hT := con.treeInsertion.outside
  have n1 : (tA s ε).2 ∈ ((conMid con).garden.tree (tA s ε).1).nodes :=
    ((s.midData ε con.newCouple con.couple_wf).decodedNode (s.chosen_plain ε)
      ((s.midData ε con.newCouple con.couple_wf).garden_decodes _) (s.branches ε s.placement.lower).toNode).2
  have n2 : (tA s ε).2 ∈ (con.output.garden.tree (tA s ε).1).nodes :=
    by
      have hp := pos_final (s := s) (ε := ε) con.newCouple con.couple_wf con.newTree con.tree_wf
      have h := (con.data.decodedNode (s.chosen_plain ε) (con.data.garden_decodes _)
        (s.branches ε s.placement.lower).toNode).2
      have hdn : (con.data.decodedNode (s.chosen_plain ε) (con.data.garden_decodes _)
        (s.branches ε s.placement.lower).toNode).1 = tA s ε := hp
      rw [hdn] at h
      exact h
  have e1 : parAt (conMid con) p (tA s ε) = parAt con.output p (tA s ε) := hT.parAt_root_eq n1 n2
  have e2 := conMid_parAt_tA con
  change TreePatternN con.output (parAt con.output p (tA s ε)) con.newTree (srcSign s ε) (tA s ε) at hpat
  rw [← e1, e2] at hpat
  exact (treePatternN_native (X := con.newTree) (ζ := srcSign s ε) (LX := conLX con) _
    (fun r hr => conLX_layer con hr)).1 hpat

/-- **Soundness**: the native exceptional objects of any LF construction form an exceptional datum. -/
theorem con_excDatum : ExcDatum s ε con.newCouple con.newTree (conLQ con) (conLX con) where
  hQ := con.couple_wf
  hX := con.tree_wf
  dQ := conLQ_decodes con
  dX := conLX_decodes con
  sig := conLX_sig con
  patQ := conLQ_pattern con
  patX := conLX_pattern con
  lone := conLX_lone con
  size := con.combinedOrder

end WaveTurbulence.ZpSurj
