/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Cell
public import WaveTurbulence.Foundations.FinalCount.C4Route
import Mathlib.Tactic

/-! # G8-XROUTE (c), (d): `X`-routes

`YRouteX k N`: a route of `k` complete (Y2) sequences from `N` to a terminal molecule `IsXFinal` (`X`, or the
quadrilateral of double bonds when `k = 0`).  `smallCell_route` mirrors `reach_cases`: a regular molecule without cut
vertex and with at most `j` triple pairs that `YReachesSmallCell` has an `X`-route of at most `j` sequences.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

/-- **A route of `k` complete (Y2) sequences ending in `X`** (or the quadrilateral, when `k = 0`). -/
inductive YRouteX : ℕ → {V : Type u} → {D : Type v} → [DecidableEq V] → [Fintype D] → [DecidableEq D] →
    Molecule V D → Prop where
  | done {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) :
      IsXFinal M → YRouteX 0 M
  | y2 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (k : ℕ) (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      YRouteX k (E.toTwoExit hcap).post → YRouteX (k + 1) M

/-- **(d) `smallCell_route`.** -/
theorem smallCell_route : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D},
    YReachesSmallCell N → ∀ (j : ℕ), RegCore N → (tripSet N).card ≤ j → ∃ k ≤ j, YRouteX k N := by
  intro V D _ _ _ N hN
  induction hN with
  | here M hcap C E hcomp hcard hcell =>
    intro j hR hj
    have hcardt := tripSet_post_card E hcap hcomp
    have hP := hR.post E
    have hX : IsX (E.toTwoExit hcap).post := isX_of_smallCell hP.loop hP.reg hcard hcell
    exact ⟨1, by omega, YRouteX.y2 0 M hcap C E hcomp (YRouteX.done _ (Or.inl hX))⟩
  | y2 M hcap C E hcomp _ ih =>
    intro j hR hj
    have hcardt := tripSet_post_card E hcap hcomp
    obtain ⟨k, hk, hrt⟩ := ih (j - 1) (hR.post E) (by omega)
    exact ⟨k + 1, by omega, YRouteX.y2 k M hcap C E hcomp hrt⟩

end WaveTurbulence.FinalCountG8
