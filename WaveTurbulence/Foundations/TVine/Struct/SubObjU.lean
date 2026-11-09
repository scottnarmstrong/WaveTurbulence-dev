/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Kinds
public import WaveTurbulence.Foundations.TVine.Struct.PiecesC
public import WaveTurbulence.Foundations.TVine.Struct.F1
public import WaveTurbulence.Foundations.TVine.Core.SubObj
public import WaveTurbulence.Foundations.TVine.Core.Statements
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F3), (F4), (F5) for single sub-objects, at U level (packet L3)

The induction of N2 L397–L402 (with REF2's R1 patch, N3 §2.1), in the KINDS form: for every T-vine `G` and every
vine-like sub-object `U` with ingredient kinds `ks`,
* (F3) `ks` is `[I]`, `[I, I]` or `[T]` (no (II) ingredient, at most two ingredients);
* (F4) `U` is gap free;
* (F5) removing `U` (sources' semantics, L1's `removeAll`) leaves `G` connected.

Inputs:
* NAMED INPUTS (owner L1; defined as L1's published `Core.Statements` (`phiU` is definitionally L1's
  `SubObj.phi`): `JointsInRungsInput` (N2 1.11), `PhiSubObjInput` (1.14(b)), `PhiTypeInput` (1.14(c′)),
  `PhiGapInput` (1.14(d)), `PhiRemovalInput` (1.14(e)); `DeleteRungInput` (1.9(1)); `PendantPolesInput` (N3 6.2);
* L2's published bases: `Checker.SizeBoundStatement`, `Checker.SubObjBaseStatement`,
  `Checker.PieceShapeBaseStatement`.
The all-out case of N2 1.14(c) ("nothing changes when `U` is all-out") is proved here (`vineLike_phi_allOut`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u

/-- `Φ(U)` (N2 Lemma 1.14(b)): `U` with the rung atoms removed, same joints and kind (= L1's `SubObj.phi`). -/
def phiU {V : Type u} [DecidableEq V] (U : SubObj V) (a b : V) : SubObj V :=
  ⟨(U.atoms.erase a).erase b, U.k₁, U.k₂, U.hyper⟩

/-- **NAMED INPUT (N2 Lemma 1.11, joints in rungs; owner L1).** Verbatim body of L1's `JointsInRungsStatement`. -/
def JointsInRungsInput : Prop := Core.JointsInRungsStatement.{u}

/-- **NAMED INPUT (N2 Lemma 1.14(b); owner L1).** Verbatim body of L1's `PhiSubObjStatement`. -/
def PhiSubObjInput : Prop := Core.PhiSubObjStatement.{u}

/-- **NAMED INPUT (N2 Lemma 1.14(c′), N3 §2.1 / REF2 R1; owner L1).** Verbatim body of L1's `PhiTypeStatement`. -/
def PhiTypeInput : Prop := Core.PhiTypeStatement.{u}

/-- **NAMED INPUT (N2 Lemma 1.14(d); owner L1).** Verbatim body of L1's `PhiGapStatement`. -/
def PhiGapInput : Prop := Core.PhiGapStatement.{u}

/-- **NAMED INPUT (N2 Lemma 1.14(e), sources' semantics; owner L1).** Verbatim body of L1's `PhiRemovalStatement`. -/
def PhiRemovalInput : Prop := Core.PhiRemovalStatement.{u}

variable {V : Type*} [DecidableEq V]

/-- The allowed kinds of N2 Thm 1.15 (F3). -/
def AllowedKinds (ks : List EnlKind) : Prop := ks = [.I] ∨ ks = [.I, .I] ∨ ks = [.T]

/-! ## The all-out case of N2 1.14(c) -/

section allOut

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}

theorem core_verts (G : UMultigraph V) (U : SubObj V) : (U.core G).verts = U.atoms := by
  unfold SubObj.core; split_ifs <;> rfl

theorem core_mult_le (G : UMultigraph V) (U : SubObj V) (e : Sym2 V) : (U.core G).mult e ≤ (induce G U.atoms).mult e := by
  unfold SubObj.core SubObj.edges; split_ifs
  · show (if e = s(U.k₁, U.k₂) then (induce G U.atoms).mult e - 1 else (induce G U.atoms).mult e) ≤ _
    split_ifs <;> omega
  · exact le_rfl

/-- A connected sub-object avoiding a 2-cut rung lies in one pole. -/
theorem atoms_in_one_pole (hR : IsRungAt G a b xm xp ym yp Km Kp) {U : SubObj V} (hU : IsSubObjU G U)
    (ha : a ∉ U.atoms) (hb : b ∉ U.atoms) : U.atoms ⊆ Km ∨ U.atoms ⊆ Kp := by
  have hsub : U.atoms ⊆ Km ∪ Kp := by
    intro x hx
    have hxV : x ∈ G.verts := hU.1.1 hx
    have := (RungFacts.verts_eq hR) ▸ hxV
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with h | rfl | rfl
    · exact h
    · exact absurd hx ha
    · exact absurd hx hb
  by_contra hc
  rw [not_or] at hc
  obtain ⟨x, hxU, hxm⟩ := Finset.not_subset.mp hc.1
  obtain ⟨y, hyU, hyp⟩ := Finset.not_subset.mp hc.2
  have hxp : x ∈ Kp := (Finset.mem_union.mp (hsub hxU)).resolve_left hxm
  have hym : y ∈ Km := (Finset.mem_union.mp (hsub hyU)).resolve_right hyp
  -- a path in the core from `y ∈ Km` to `x ∈ Kp` crosses from `Km` to `Kp` along a bond of `G`
  have hconn := hU.2.2.2.2.2.2.2.2 y (by rw [core_verts]; exact hyU) x (by rw [core_verts]; exact hxU)
  have key : ∀ z, Relation.ReflTransGen (AdjIn (U.core G) (U.core G).verts) y z → z ∈ Km := by
    intro z hz
    induction hz with
    | refl => exact hym
    | @tail z w _ hzw ih =>
      have hw : w ∈ U.atoms := by rw [← core_verts G U]; exact hzw.2.1
      rcases Finset.mem_union.mp (hsub hw) with h | h
      · exact h
      · exfalso
        have h1 := core_mult_le G U s(z, w)
        have hz' : z ∈ U.atoms := by rw [← core_verts G U]; exact hzw.1
        rw [induce_mult_of_mem G hz' hw, hR.noBond z ih w h] at h1
        exact hzw.2.2 (by omega)
  exact hxm (key x hconn)

theorem phiU_eq_self {U : SubObj V} (ha : a ∉ U.atoms) (hb : b ∉ U.atoms) : phiU U a b = U := by
  unfold phiU
  rw [Finset.erase_eq_of_notMem ha, Finset.erase_eq_of_notMem hb]

/-- The core of an all-out sub-object is unchanged by the rung deletion. -/
theorem core_rungDel_allOut (hR : IsRungAt G a b xm xp ym yp Km Kp) {U : SubObj V} (hU : IsSubObjU G U)
    (ha : a ∉ U.atoms) (hb : b ∉ U.atoms) : U.core (rungDel G a b xm xp ym yp true) = U.core G := by
  have hpole := atoms_in_one_pole hR hU ha hb
  have hind : induce (rungDel G a b xm xp ym yp true) U.atoms = induce G U.atoms := by
    refine Core.ext rfl fun e => ?_
    show (if e ∈ U.atoms.sym2 then _ else 0) = (if e ∈ U.atoms.sym2 then _ else 0)
    split_ifs with he
    · induction e using Sym2.ind with
      | h x y =>
        have hx := (Finset.mk_mem_sym2_iff.mp he).1
        have hy := (Finset.mk_mem_sym2_iff.mp he).2
        rcases hpole with h | h
        · rw [RungFacts.mult_del hR (Or.inl (h hx)) (Or.inl (h hy)),
            RungFacts.adds_count_same hR (Or.inl ⟨h hx, h hy⟩), add_zero]
        · rw [RungFacts.mult_del hR (Or.inr (h hx)) (Or.inr (h hy)),
            RungFacts.adds_count_same hR (Or.inr ⟨h hx, h hy⟩), add_zero]
    · rfl
  unfold SubObj.core SubObj.edges
  rw [hind]

/-- **The all-out case of N2 1.14(c)**: a vine-like sub-object avoiding the rung stays vine-like (with the same
kinds) in `G/R`. -/
theorem vineLike_phi_allOut (hR : IsRungAt G a b xm xp ym yp Km Kp) {U : SubObj V} {ks : List EnlKind}
    (hU : IsVineLikeU G U ks) (ha : a ∉ U.atoms) (hb : b ∉ U.atoms) :
    IsVineLikeU (rungDel G a b xm xp ym yp true) (phiU U a b) ks := by
  rw [phiU_eq_self ha hb]
  have hcore := core_rungDel_allOut hR hU.1 ha hb
  have hpole := atoms_in_one_pole hR hU.1 ha hb
  refine ⟨⟨?_, fun hh => ?_, by rw [hcore]; exact hU.1.2.2⟩, by rw [hcore]; exact hU.2⟩
  · rw [RungFacts.verts_del hR]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, fun he => ?_⟩
    · rcases hpole with h | h
      · exact Finset.mem_union_left _ (h hx)
      · exact Finset.mem_union_right _ (h hx)
    · rcases hpole with h | h
      · exact Finset.disjoint_left.mp hR.disj (h (he ▸ Finset.mem_union_right _ hR.xp_mem)) hR.xp_mem
      · exact Finset.disjoint_left.mp hR.disj hR.xm_mem (h (he ▸ Finset.mem_union_left _ hR.xm_mem))
  · have hne := hU.1.2.1 hh
    have hk₁ : U.k₁ ∈ U.atoms := by rw [← core_verts G U]; exact hU.1.2.2.1
    have hk₂ : U.k₂ ∈ U.atoms := by rw [← core_verts G U]; exact hU.1.2.2.2.1
    rcases hpole with h | h
    · rw [RungFacts.mult_del hR (Or.inl (h hk₁)) (Or.inl (h hk₂)),
        RungFacts.adds_count_same hR (Or.inl ⟨h hk₁, h hk₂⟩), add_zero]; exact hne
    · rw [RungFacts.mult_del hR (Or.inr (h hk₁)) (Or.inr (h hk₂)),
        RungFacts.adds_count_same hR (Or.inr ⟨h hk₁, h hk₂⟩), add_zero]; exact hne

end allOut

end WaveTurbulence.TVine.Struct
