/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.MemberF23
public import WaveTurbulence.Foundations.TVine.Struct.IITemplate
import Mathlib.Tactic

/-!
# N3 Corollary 1.16′ for a single-vine container (packet L3)

* `cor116_I`: a vine (I) has no proper member;
* `cor116_II`: a member of a vine (II) avoids its joints, is of block type and is a block I (a rung);
* `conn_II`: removing any family of members of a vine (II) keeps it connected (the rails remain);
* `TVineFamiliesStatement`: (3) for a T-vine container (N2 Thm 1.15 (F5) for families, sources' semantics);
* **`cor116Single_of`**: `Cor116SingleStatement` from `Thm115Inputs`, `ContainerJointsInput` and
  `TVineFamiliesStatement`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

/-- **(3) for a T-vine container** (N2 Thm 1.15 (F5) for families, sources' removal semantics; N3 §2.2 Case A). -/
def TVineFamiliesStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (γ : ℝ),
    γ ≤ 1 / 2 → ∀ (S : Finset V) (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      ∀ (n : ℕ) (U : Fin n → Src.Object γ M), (∀ i, (U i).atoms ⊂ S) →
        (∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) →
        ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem containsDart_inGroup {γ : ℝ} {M : Molecule V D} (C : Src.Object γ M) {x : D} (h : C.ContainsDart x) :
    M.InGroup C.atoms x := by
  obtain ⟨A, a, b, sh⟩ := C
  cases sh with
  | vc _ => exact h
  | hyper _ => exact h.2.2

theorem subObj_suOf {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} (U : Src.Object γ M)
    (hUS : U.atoms ⊂ S) : IsSubObjU (groupGraph M S) (suOf U) :=
  (vineLike_suOf hγ U hUS).choose_spec.1

/-- **A vine (I) has no proper member.** -/
theorem cor116_I {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hI : M.IsVine .I S j₁ j₂) (U : Src.Object γ M) (hUS : U.atoms ⊂ S) : False := by
  have hc := card_isVineXU_I ((isVine_iff M .I).mp hI).2
  rw [groupGraph_verts] at hc
  have hU := subObj_suOf hγ U hUS
  have hk₁ := k₁_mem hU
  have hk₂ := k₂_mem hU
  have hne : (suOf U).k₁ ≠ (suOf U).k₂ := hU.2.2.2.2.1
  have h2 : 2 ≤ U.atoms.card := by
    have : ({(suOf U).k₁, (suOf U).k₂} : Finset V) ⊆ U.atoms :=
      Finset.insert_subset hk₁ (Finset.singleton_subset_iff.mpr hk₂)
    have := Finset.card_le_card this
    rwa [Finset.card_pair hne] at this
  have := Finset.card_lt_card hUS
  omega

/-- **A member of a vine (II) is a rung** (N3 L570–L576). -/
theorem cor116_II {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hII : M.IsVine .II S j₁ j₂) (U : Src.Object γ M) (hUS : U.atoms ⊂ S) :
    j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms ∧ (∃ h, U.shape = .vc h) ∧ M.IsVine .I U.atoms U.upper U.lower := by
  obtain ⟨hBM, hX⟩ := (isVine_iff M .II).mp hII
  obtain ⟨Dd⟩ := nonempty_iiData hX
  obtain ⟨ks, hks⟩ := vineLike_suOf hγ U hUS
  obtain ⟨hj₁, hj₂⟩ := Dd.joints_not_mem hX.1 hks.1
  obtain ⟨hh, x, hx⟩ := Dd.member_shape hX.1 hks.1
  refine ⟨hj₁, hj₂, ?_⟩
  have hxA : x ∈ U.atoms := by rw [show U.atoms = (suOf U).atoms from rfl, hx]; simp
  have hxS : x ∈ (groupGraph M S).verts := hUS.subset hxA
  have hxj₁ : x ≠ j₁ := fun h => hj₁ (h ▸ hxA)
  have hxj₂ : x ≠ j₂ := fun h => hj₂ (h ▸ hxA)
  have hpx := (Dd.inner x hxS hxj₁ hxj₂).2.1.2.1
  have hcard : U.atoms.card = 2 := by
    rw [show U.atoms = (suOf U).atoms from rfl, hx, Finset.card_pair (Ne.symm hpx)]
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | hyper R => exact absurd hh (by simp [suOf])
  | vc h =>
    refine ⟨⟨h, rfl⟩, ?_⟩
    show M.IsVine .I A a b
    have hch : ChainU (groupGraph M A) A a b ks := by
      have := hks.2; rw [core_suOf_vc h hUS.subset] at this; exact this
    have hk := kinds_of_card_two hch hcard
    subst hk
    have hXI := chain_single_inv hch
    rw [groupGraph_induce M (subset_refl A)] at hXI
    exact (isVine_iff M .I).mpr ⟨h.1, hXI⟩

/-- **Removing members of a vine (II) keeps it connected**: every atom reaches `j₁` through rails and joint
bonds, which no member contains. -/
theorem conn_II {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hII : M.IsVine .II S j₁ j₂) {n : ℕ} (U : Fin n → Src.Object γ M) (hsub : ∀ i, (U i).atoms ⊂ S) :
    ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b := by
  obtain ⟨hBM, hX⟩ := (isVine_iff M .II).mp hII
  obtain ⟨Dd⟩ := nonempty_iiData hX
  -- members are level sets
  have hlev : ∀ i, ∀ p ∈ (U i).atoms, ∀ q ∈ (U i).atoms, Dd.lev p = Dd.lev q := by
    intro i p hp q hq
    obtain ⟨ks, hks⟩ := vineLike_suOf hγ (U i) (hsub i)
    obtain ⟨hj₁, hj₂⟩ := Dd.joints_not_mem hX.1 hks.1
    obtain ⟨-, x, hx⟩ := Dd.member_shape hX.1 hks.1
    have hxA : x ∈ (U i).atoms := by rw [show (U i).atoms = (suOf (U i)).atoms from rfl, hx]; simp
    have hxS : x ∈ (groupGraph M S).verts := (hsub i).subset hxA
    have hp3 := (Dd.inner x hxS (fun h => hj₁ (h ▸ hxA)) (fun h => hj₂ (h ▸ hxA))).2.1.2.2.1
    have hall : ∀ w ∈ (U i).atoms, Dd.lev w = Dd.lev x := by
      intro w hw
      rw [show (U i).atoms = (suOf (U i)).atoms from rfl, hx] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · rfl
      · exact hp3
    rw [hall p hp, hall q hq]
  -- a bond between two levels is a step of `remAdj`
  have hstep : ∀ p ∈ S, ∀ q ∈ S, 1 ≤ (groupGraph M S).mult s(p, q) → Dd.lev p ≠ Dd.lev q → remAdj M S U q p := by
    intro p hp q hq hm hl
    have hsw : (groupGraph M S).mult s(q, p) = (groupGraph M S).mult s(p, q) := by rw [Sym2.eq_swap]
    obtain ⟨x, hx, hxq, hxp⟩ := (adjIn_groupGraph_iff M).mp ⟨hq, hp, by omega⟩
    refine ⟨x, hx, fun i hc => ?_, hxq, hxp⟩
    have hg := containsDart_inGroup (U i) hc
    exact hl (hlev i p (hxp ▸ hg.2) q (hxq ▸ hg.1))
  have key : ∀ m, ∀ p ∈ S, Dd.lev p = m → Relation.EqvGen (remAdj M S U) j₁ p := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro p hp hm
    by_cases h1 : p = j₁
    · subst h1; exact .refl _
    by_cases h2 : p = j₂
    · subst h2
      obtain ⟨z, hz, hzl, hzm⟩ := Dd.jt_dn
      have hlt : Dd.lev z < m := by rw [← hm, Dd.lev_jt]; exact hzl
      exact .trans _ _ _ (ih _ hlt z hz rfl) (.rel _ _ (hstep p hp z hz hzm (by omega)))
    · obtain ⟨-, -, ⟨d1, d2, d3⟩, -⟩ := Dd.inner p hp h1 h2
      have hlt : Dd.lev (Dd.dn p) < m := by omega
      exact .trans _ _ _ (ih _ hlt _ d1 rfl) (.rel _ _ (hstep p hp _ d1 d3 (by omega)))
  intro a ha b hb
  have haS : a ∈ S := (Finset.mem_sdiff.mp ha).1
  have hbS : b ∈ S := (Finset.mem_sdiff.mp hb).1
  exact .trans _ _ _ (.symm _ _ (key _ a haS rfl)) (key _ b hbS rfl)

/-- Removing no member from a vine (I) keeps it connected. -/
theorem conn_I {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {j₁ j₂ : V}
    (hI : M.IsVine .I S j₁ j₂) {n : ℕ} (U : Fin n → Src.Object γ M) (hsub : ∀ i, (U i).atoms ⊂ S) :
    ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b := by
  have hno : ∀ i, False := fun i => cor116_I hγ hI (U i) (hsub i)
  have hconn : Connected (groupGraph M S) := (isBlockU_of_isBlock M hI.1).2.2.2.2.2.2
  intro a ha b hb
  have haS : a ∈ S := (Finset.mem_sdiff.mp ha).1
  have hbS : b ∈ S := (Finset.mem_sdiff.mp hb).1
  have hr := hconn a haS b hbS
  clear ha hb hbS
  induction hr with
  | refl => exact .refl _
  | tail _ hbc ih =>
    obtain ⟨x, hx, h1, h2⟩ := (adjIn_groupGraph_iff M).mp hbc
    exact .trans _ _ _ ih (.rel _ _ ⟨x, hx, fun i => (hno i).elim, h1, h2⟩)

/-- **N3 Corollary 1.16′ (1)–(3) for a single-vine container.** -/
theorem cor116Single_of (I : Thm115Inputs.{u}) (hcj : ContainerJointsInput.{u})
    (hF : TVineFamiliesStatement.{u, v}) : Cor116SingleStatement.{u, v} := by
  intro V D _ _ _ M γ hγ S j₁ j₂ hE
  refine ⟨fun U hUS => ?_, fun n U hsub hdisj => ?_⟩
  · rcases hE with hI | hII | hT
    · exact (cor116_I hγ hI U hUS).elim
    · obtain ⟨h1, h2, h3, h4⟩ := cor116_II hγ hII U hUS
      refine ⟨h1, h2, fun hT => ?_, fun _ => ⟨h3, h4⟩⟩
      exfalso
      have hc₁ := card_isVineXU_II ((isVine_iff M .II).mp hII).2
      have hc₂ := card_isTVineU ((isTVine_iff M).mp hT).2
      rw [groupGraph_verts] at hc₁ hc₂
      exact (Nat.not_even_iff_odd.mpr hc₂.1) hc₁.1
    · obtain ⟨h1, h2, h3⟩ := tvine_member I hcj hγ hT U hUS
      refine ⟨h1, h2, fun _ => h3, fun hII => ?_⟩
      exfalso
      have hc₁ := card_isVineXU_II ((isVine_iff M .II).mp hII).2
      have hc₂ := card_isTVineU ((isTVine_iff M).mp hT).2
      rw [groupGraph_verts] at hc₁ hc₂
      exact (Nat.not_even_iff_odd.mpr hc₂.1) hc₁.1
  · rcases hE with hI | hII | hT
    · exact conn_I hγ hI U hsub
    · exact conn_II hγ hII U hsub
    · exact hF M γ hγ S j₁ j₂ hT n U hsub hdisj

end WaveTurbulence.TVine.Struct
