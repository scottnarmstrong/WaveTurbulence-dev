/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVineEst
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
public import WaveTurbulence.Foundations.Stage1.Represents.RepFinal1

/-!
# S2 REPRESENTS, VINE-E (1): the elementary premises of VINEEST for a unit

* `N_le_N_one`: `N_q ≤ N_1` for `q ≥ 1` (`R_p` decreases in `p`, TARGET (parameters2)).
* `clLocalOrder1_le_order`, `clLocalOrder1_le_N1`: the interior of a CL region has at most `|G| ≤ N_{p+1}^4 ≤ N_1^4`
  branches (VINEEST's premise `clLocalOrder1 R ≤ P.N 1 ^ 4`).
* `unitProfile_bound`: the vine-region profile of a pair-type family, `r ↦ U.h i r j j`, obeys VINEEST's input bound with
  the one constant `B₀ = U.b i` (TARGET L1752 / R46: one constant for all layers; design P*, Q1: vine-region pairs have
  type `(q, j₁, j₁)`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed TTree

theorem N_le_N_one (P : WTParams) {q : ℕ} (hq : 1 ≤ q) : P.N q ≤ P.N 1 := by
  induction q with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact le_rfl
    · exact (P.N_le_N_pred (q := k + 1) (by omega)).trans (by simpa using ih hk)

theorem clLocalOrder1_le_order {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) : clLocalOrder1 R ≤ G.order := by
  unfold clLocalOrder1
  have hb : Fintype.card (GBranch G.tree) = G.order := Comb.card_gbranch G.tree
  rw [← hb]
  exact Finset.card_le_univ _

theorem clLocalOrder1_le_N1 (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) {p : ℕ} (h : G.order ≤ P.N (p + 1) ^ 4) :
    clLocalOrder1 R ≤ P.N 1 ^ 4 :=
  (clLocalOrder1_le_order R).trans (h.trans (Nat.pow_le_pow_left (N_le_N_one P (by omega)) 4))

end WaveTurbulence.Represents
