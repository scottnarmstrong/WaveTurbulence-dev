/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjU
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F3)–(F5) for single sub-objects: the induction (packet L3)

* `Thm115Inputs`: the named inputs (L1) and the published bases (L2) used by the induction;
* `allowedKinds_of_allowedType`: L2's structural types give the kinds (base conversion);
* `exists_deletable_avoiding`: a large T-vine has a deletable rung containing no joint of a given sub-object (size
  bound + N2 1.11);
* `allIn_of_mem_b`: N2 1.14(a), the direction used (a rung atom inside `U` drags the other one in);
* **`subObj_single`**: for every T-vine and every vine-like sub-object: allowed kinds, gap free, removal connected.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

universe u

/-- The inputs of the Thm 1.15 induction: L1's named inputs and L2's published bases. -/
structure Thm115Inputs : Prop where
  del : DeleteRungInput.{u}
  pend : PendantPolesInput.{u}
  joints : JointsInRungsInput.{u}
  phiSub : PhiSubObjInput.{u}
  phiType : PhiTypeInput.{u}
  phiGap : PhiGapInput.{u}
  phiRem : PhiRemovalInput.{u}
  size : Checker.SizeBoundStatement.{u}
  basePS : Checker.PieceShapeBaseStatement.{u}
  baseSO : Checker.SubObjBaseStatement.{u}
  baseFam : Checker.FamiliesBaseStatement.{u}

variable {V : Type u} [DecidableEq V]

theorem pieces_card_ge_two_U {G : UMultigraph V} {j₁ j₂ : V} (h : PieceShapeU G j₁ j₂) :
    ∀ P ∈ piecesU G j₁ j₂, 2 ≤ P.card := by
  obtain ⟨core, -, hcs, hrest⟩ := h
  intro P hP
  by_cases hc : P = core
  · obtain ⟨x, y, z, hxy, hyz, hxz, hP3, -⟩ := hcs
    rw [hc, hP3, Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩]; omega
  · obtain ⟨a, b, hab, rfl, -⟩ := hrest P hP hc
    rw [Finset.card_pair hab]

/-- A T-vine (given the inputs) has no interior cut atom. -/
theorem noCut_of_inputs (I : Thm115Inputs.{u}) {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) :
    ∀ v ∈ Core.interior G j₁ j₂, ConnOn G (G.verts.erase v) := fun v hv =>
  erase_connOn (t6Ctx_of_isTVineU I.pend h)
    (pieces_card_ge_two_U (pieceShapeU_of_isTVineU I.del I.size I.basePS _ G j₁ j₂ rfl h)) hv

/-- **Base conversion**: a vine-like sub-object of one of the structural types has allowed kinds. -/
theorem allowedKinds_of_allowedType (I : Thm115Inputs.{u}) {G : UMultigraph V} {U : SubObj V}
    {ks : List EnlKind} (hU : IsVineLikeU G U ks) (hA : AllowedTypeU G U) : AllowedKinds ks := by
  rcases hA with ⟨-, hne, hS, -⟩ | ⟨c, h1, h2, h3, hS, -, -⟩ | hT
  · left
    exact kinds_of_card_two hU.2 (by rw [hS, Finset.card_pair hne])
  · right; left
    exact kinds_of_card_three hU.2 (by rw [hS, Finset.card_eq_three.mpr ⟨U.k₁, c, U.k₂, h1, h3, h2, rfl⟩])
  · right; right
    exact kinds_of_tvine hU.2 hT (core_verts G U) (noCut_of_inputs I hT)

theorem mult_removeAll_of_N (G : UMultigraph V) (U : SubObj V) {p q : V}
    (hm : (Checker.removeAllN G [U]).mult s(p, q) ≠ 0) : (removeAll G [U]).mult s(p, q) ≠ 0 := by
  show (if s(p, q) ∈ (G.verts \ U.inner).sym2 then G.mult s(p, q) - (U.core G).mult s(p, q) else 0) ≠ 0
  have hm' : (if s(p, q) ∈ (G.verts \ Checker.innerAll [U]).sym2 ∧ ∀ W ∈ [U], s(p, q) ∉ W.atoms.sym2 then
      G.mult s(p, q) else 0) ≠ 0 := hm
  split_ifs at hm' with hc
  · have hset : G.verts \ Checker.innerAll [U] = G.verts \ U.inner := by simp [Checker.innerAll]
    rw [hset] at hc
    rw [if_pos hc.1]
    have hnot : s(p, q) ∉ U.atoms.sym2 := hc.2 U (List.mem_singleton_self U)
    have h0 : (U.core G).mult s(p, q) = 0 := by
      have := core_mult_le G U s(p, q)
      have h1 : (induce G U.atoms).mult s(p, q) = 0 := by
        show (if s(p, q) ∈ U.atoms.sym2 then _ else 0) = 0; rw [if_neg hnot]
      omega
    omega
  · exact absurd rfl hm'


/-- Removal in N2's semantics leaves fewer bonds than the sources' removal. -/
theorem connected_removeAll_of_N (G : UMultigraph V) (U : SubObj V)
    (h : Connected (Checker.removeAllN G [U])) : Connected (removeAll G [U]) := by
  have hv : (Checker.removeAllN G [U]).verts = (removeAll G [U]).verts := by
    show G.verts \ Checker.innerAll [U] = G.verts \ U.inner
    simp [Checker.innerAll]
  have hstep : ∀ p q, AdjIn (Checker.removeAllN G [U]) (Checker.removeAllN G [U]).verts p q →
      AdjIn (removeAll G [U]) (removeAll G [U]).verts p q := by
    intro p q hpq
    rw [← hv]
    exact ⟨hpq.1, hpq.2.1, mult_removeAll_of_N G U hpq.2.2⟩
  intro x hx y hy
  rw [← hv] at hx hy
  have hr := h x hx y hy
  clear hx hy
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih (hstep _ _ hbc)

/-- N2 1.14(a), the direction used: if one rung atom is an inner atom of `U`, so is the other. -/
theorem mem_of_rung_partner {G : UMultigraph V} {j₁ j₂ a b : V} (hB : IsBlockU G j₁ j₂) (hl : G.Loopless)
    (hmab : G.mult s(a, b) = 2) {U : SubObj V} (hU : IsSubObjU G U) (hb : b ∈ U.atoms) (hbk₁ : b ≠ U.k₁)
    (hbk₂ : b ≠ U.k₂) (hbj₁ : b ≠ j₁) (hbj₂ : b ≠ j₂) : a ∈ U.atoms := by
  by_contra ha
  have hbV : b ∈ G.verts := hU.1.1 hb
  have haV : a ∈ G.verts := G.supp _ (by omega) a (Sym2.mem_mk_left a b)
  have hdc : deg (U.core G) b = 4 := hU.2.2.2.2.2.2.2.1 b (by rw [core_verts]; exact hb) hbk₁ hbk₂
  have hdG : deg G b = 4 := hB.2.2.2.2.2.1 b hbV hbj₁ hbj₂
  -- the core's degree at `b` is at most the weight of `G` from `b` into the atoms
  have hle : deg (U.core G) b ≤ ∑ w ∈ U.atoms, G.mult s(b, w) + G.mult s(b, b) := by
    unfold deg; rw [core_verts]
    refine add_le_add (Finset.sum_le_sum fun w hw => ?_) ?_
    · exact (core_mult_le G U _).trans (by rw [induce_mult_of_mem G hb hw])
    · exact (core_mult_le G U _).trans (by rw [induce_mult_of_mem G hb hb])
  have hsplit : deg G b = ∑ w ∈ U.atoms, G.mult s(b, w) + ∑ w ∈ G.verts \ U.atoms, G.mult s(b, w) + G.mult s(b, b) := by
    unfold deg; rw [← Finset.sum_sdiff hU.1.1]; ring
  have hout : 2 ≤ ∑ w ∈ G.verts \ U.atoms, G.mult s(b, w) := by
    have := Finset.single_le_sum (f := fun w => G.mult s(b, w)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_sdiff.mpr ⟨haV, ha⟩)
    rw [Sym2.eq_swap] at hmab
    omega
  omega

/-- **A large T-vine has a deletable rung avoiding the joints of a given sub-object.** -/
theorem exists_deletable_avoiding (I : Thm115Inputs.{u}) {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂)
    (hn : 14 ≤ G.verts.card) {U : SubObj V} (hU : IsSubObjU G U) :
    ∃ a b xm xp ym yp : V, ∃ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp ∧
      U.k₁ ≠ a ∧ U.k₁ ≠ b ∧ U.k₂ ≠ a ∧ U.k₂ ≠ b := by
  classical
  have hsz := I.size G j₁ j₂ hT
  have hD : 2 ≤ deletableCount G j₁ j₂ := by omega
  unfold deletableCount at hD
  obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hD)
  have hl : G.Loopless := loopless_of_isTVineU hT
  have key : ∀ a b : V, IsDeletable G j₁ j₂ a b → s(a, b) ≠ s(U.k₁, U.k₂) →
      ∃ a b xm xp ym yp : V, ∃ Km Kp : Finset V,
        IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp ∧ U.k₁ ≠ a ∧ U.k₁ ≠ b ∧ U.k₂ ≠ a ∧ U.k₂ ≠ b := by
    intro a b hdel hzne
    obtain ⟨xm, xp, ym, yp, Km, Kp, hDel⟩ := hdel
    refine ⟨a, b, xm, xp, ym, yp, Km, Kp, hDel, ?_⟩
    by_contra hc
    have hin : U.k₁ = a ∨ U.k₁ = b ∨ U.k₂ = a ∨ U.k₂ = b := by tauto
    exact hzne (I.joints G j₁ j₂ a b xm xp ym yp Km Kp U hT.1 hl hDel.1 hU hin).1.symm
  obtain ⟨-, a₁, b₁, rfl, hd₁⟩ := Finset.mem_filter.mp hz₁
  obtain ⟨-, a₂, b₂, rfl, hd₂⟩ := Finset.mem_filter.mp hz₂
  by_cases h1 : s(a₁, b₁) = s(U.k₁, U.k₂)
  · exact key a₂ b₂ hd₂ (fun h2 => hz (h1.trans h2.symm))
  · exact key a₁ b₁ hd₁ h1

/-- **N2 Theorem 1.15 (F3)–(F5) for single vine-like sub-objects** (kinds form), by induction on the size. -/
theorem subObj_single (I : Thm115Inputs.{u}) : ∀ (n : ℕ) (G : UMultigraph V) (j₁ j₂ : V), G.verts.card = n →
    IsTVineU G j₁ j₂ → ∀ (U : SubObj V) (ks : List EnlKind), IsVineLikeU G U ks →
      AllowedKinds ks ∧ Core.GapFree G U ∧ Connected (removeAll G [U]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G j₁ j₂ hn hT U ks hU
    by_cases hsmall : n ≤ 13
    · obtain ⟨-, -, hA, hgap, -, hconn⟩ := I.baseSO G j₁ j₂ hT (by omega) U hU.1
      exact ⟨allowedKinds_of_allowedType I hU hA, hgap, connected_removeAll_of_N G U hconn⟩
    · obtain ⟨a, b, xm, xp, ym, yp, Km, Kp, hDel, h1a, h1b, h2a, h2b⟩ :=
        exists_deletable_avoiding I hT (by omega) hU.1
      obtain ⟨⟨hR, ha1, ha2, hb1, hb2⟩, hcap⟩ := hDel
      have hl : G.Loopless := loopless_of_isTVineU hT
      have hT' := I.del G j₁ j₂ a b xm xp ym yp Km Kp hT ⟨⟨hR, ha1, ha2, hb1, hb2⟩, hcap⟩ true
      have hcard : (rungDel G a b xm xp ym yp true).verts.card = n - 2 := by
        rw [hR.verts_rungDel true, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hR.ne, hR.b_mem⟩),
          Finset.card_erase_of_mem hR.a_mem, hn]
        try omega
      have hIH := ih (n - 2) (by omega) _ j₁ j₂ hcard hT' (phiU U a b)
      -- the image is vine-like with the same kinds (or the excluded II → I case)
      have hkinds : AllowedKinds ks ∧ Core.GapFree (rungDel G a b xm xp ym yp true) (phiU U a b) ∧
          Connected (removeAll (rungDel G a b xm xp ym yp true) [phiU U a b]) := by
        by_cases ha : a ∈ U.atoms
        · rcases I.phiType G j₁ j₂ a b xm xp ym yp Km Kp U ks true hT.1 hl ⟨⟨hR, ha1, ha2, hb1, hb2⟩, hcap⟩ hU
            h1a h1b h2a h2b ha with
            hV | ⟨i, -, hV, hcut⟩
          · exact hIH ks hV
          · exact absurd hcut (hIH _ hV).2.1
        · have hb : b ∉ U.atoms := fun hb => ha (mem_of_rung_partner hT.1 hl hR.mult_ab hU.1 hb
            (Ne.symm h1b) (Ne.symm h2b) hb1 hb2)
          exact hIH ks (vineLike_phi_allOut hR hU ha hb)
      obtain ⟨hks, hgap', hconn'⟩ := hkinds
      refine ⟨hks, I.phiGap G j₁ j₂ a b xm xp ym yp Km Kp U true hT.1 hl ⟨hR, ha1, ha2, hb1, hb2⟩ hU.1
        h1a h1b h2a h2b hgap', ?_⟩
      exact I.phiRem G j₁ j₂ a b xm xp ym yp Km Kp [U] true hT.1 hl ⟨hR, ha1, ha2, hb1, hb2⟩
        (fun W hW => by rw [List.mem_singleton] at hW; subst hW; exact ⟨hU.1, h1a, h1b, h2a, h2b⟩)
        (List.pairwise_singleton _ _) hconn'

end WaveTurbulence.TVine.Struct
