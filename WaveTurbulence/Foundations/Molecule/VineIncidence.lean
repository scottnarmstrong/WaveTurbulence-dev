/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Incidence algebra for rung insertion (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- Incidences in an edge list, counting both ends of each edge. -/
@[expose] def edgeDegree (es : List (ℕ×ℕ)) (v : ℕ) : ℕ :=
  (es.map Prod.fst).count v + (es.map Prod.snd).count v

/-- Incidences add over edge lists. -/
theorem edgeDegree_append (es fs : List (ℕ×ℕ)) (v : ℕ) :
    edgeDegree (es++fs) v = edgeDegree es v+edgeDegree fs v := by
  simp only [edgeDegree,List.map_append,List.count_append]
  omega

/-- Reordering bonds changes no degree. -/
theorem edgeDegree_perm {es fs : List (ℕ×ℕ)} (h : es.Perm fs) (v : ℕ) :
    edgeDegree es v = edgeDegree fs v := by
  rw [edgeDegree,edgeDegree,(h.map Prod.fst).count_eq,(h.map Prod.snd).count_eq]

/-- Removing one present edge removes precisely its endpoint incidences. -/
theorem edgeDegree_erase {es : List (ℕ×ℕ)} {e : ℕ×ℕ} (he : e ∈ es) (v : ℕ) :
    edgeDegree (es.erase e) v + (if e.1=v then 1 else 0) +
      (if e.2=v then 1 else 0) = edgeDegree es v := by
  have hp := edgeDegree_perm (List.perm_cons_erase he) v
  simp only [edgeDegree,List.map_cons,List.count_cons,beq_iff_eq] at hp ⊢
  omega

/-- A rail contributes its endpoints once and every intermediate atom twice. -/
theorem railBonds_degree (a b v : ℕ) (ws : List ℕ) :
    edgeDegree (railBonds a ws b) v =
      (if a=v then 1 else 0)+(if b=v then 1 else 0)+2*ws.count v := by
  have hl : (a::ws).length = (ws++[b]).length := by simp
  simp only [edgeDegree,railBonds,List.map_fst_zip hl.le,List.map_snd_zip hl.symm.le,
    List.count_cons,List.count_append,List.count_nil]
  simp only [beq_iff_eq]
  split_ifs <;> omega

end WaveTurbulence.Vine
