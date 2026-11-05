/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.AdjacentGeneration

/-! # Pairing-closed ordered blocks (DH21 Proposition 4.5(2)) -/

@[expose] public section

namespace WaveTurbulence.Reg
namespace PairPartition
open Finset
variable {n : ℕ} (P : PairPartition n)

/-- An actual order-preserving label map for a selected block. -/
noncomputable def blockEmbedding (S : Finset (Fin n)) : Fin S.card ↪o Fin n :=
  (S.orderIsoOfFin rfl).toOrderEmbedding.trans (OrderEmbedding.subtype _)

theorem blockEmbedding_mem (S : Finset (Fin n)) (i) : blockEmbedding S i ∈ S :=
  (S.orderIsoOfFin rfl i).2

/-- The partner involution induced on an arbitrary pairing-closed block. -/
noncomputable def onBlock (S : Finset (Fin n)) (hc : ∀ x ∈ S, P.pair x ∈ S) :
    PairPartition S.card :=
  P.restrict (blockEmbedding S) (fun i =>
    ⟨(S.orderIsoOfFin rfl).symm ⟨P.pair (blockEmbedding S i), hc _ (blockEmbedding_mem S i)⟩,
      congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)⟩)

/-- The selected partition retains every source partner. -/
theorem onBlock_pair (S : Finset (Fin n)) (hc : ∀ x ∈ S, P.pair x ∈ S) (i) :
    blockEmbedding S ((P.onBlock S hc).pair i) = P.pair (blockEmbedding S i) :=
  P.restrict_pair _ _ _

/-- A pairing-closed restriction of a legal partition is legal. -/
theorem onBlock_legal (hP : P.Legal) (S : Finset (Fin n))
    (hc : ∀ x ∈ S, P.pair x ∈ S) : (P.onBlock S hc).Legal := P.restrict_legal hP _ _

/-- Transport a forbidden crossing back to a selected block's actual indices. -/
theorem no_crossing_of_onBlock_legal (S : Finset (Fin n))
    (hc : ∀ x ∈ S, P.pair x ∈ S) (hS : (P.onBlock S hc).Legal)
    {a b c d : Fin n} (ha : a ∈ S) (hb : b ∈ S) (hc' : c ∈ S) (hd : d ∈ S)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hac : P.pair a = c) (hbd : P.pair b = d) :
    False := by
  let e := S.orderIsoOfFin rfl
  let A := e.symm ⟨a,ha⟩
  let B := e.symm ⟨b,hb⟩
  let C := e.symm ⟨c,hc'⟩
  let D := e.symm ⟨d,hd⟩
  have heA : blockEmbedding S A = a := congrArg Subtype.val (e.apply_symm_apply _)
  have heB : blockEmbedding S B = b := congrArg Subtype.val (e.apply_symm_apply _)
  have heC : blockEmbedding S C = c := congrArg Subtype.val (e.apply_symm_apply _)
  have heD : blockEmbedding S D = d := congrArg Subtype.val (e.apply_symm_apply _)
  apply hS A B C D (e.symm.strictMono hab) (e.symm.strictMono hbc) (e.symm.strictMono hcd)
  · apply (blockEmbedding S).injective
    rw [P.onBlock_pair, heA, hac, heC]
  · apply (blockEmbedding S).injective
    rw [P.onBlock_pair, heB, hbd, heD]

/-- A pairing-closed block has a pairing-closed complement. -/
theorem complement_closed (S : Finset (Fin n)) (hc : ∀ x ∈ S, P.pair x ∈ S) :
    ∀ x ∈ Sᶜ, P.pair x ∈ Sᶜ := by
  intro x hx
  simp only [Finset.mem_compl] at hx ⊢
  intro he
  exact hx (P.involutive x ▸ hc _ he)

/-- Concatenation criterion: a closed initial block and its complement are legal
exactly when their ordered union is legal (DH21 Prop 4.5(2), concatenation). -/
theorem legal_iff_blocks (S : Finset (Fin n))
    (hi : ∀ x ∈ S, ∀ y, y ≤ x → y ∈ S) (hc : ∀ x ∈ S, P.pair x ∈ S) :
    P.Legal ↔ (P.onBlock S hc).Legal ∧
      (P.onBlock Sᶜ (P.complement_closed S hc)).Legal := by
  constructor
  · intro h
    exact ⟨P.onBlock_legal h _ _, P.onBlock_legal h _ _⟩
  · rintro ⟨hS,hT⟩ a b c d hab hbc hcd hac hbd
    by_cases ha : a ∈ S
    · have hc' : c ∈ S := hac ▸ hc a ha
      have hb : b ∈ S := hi c hc' b (le_of_lt hbc)
      have hd : d ∈ S := hbd ▸ hc b hb
      exact P.no_crossing_of_onBlock_legal S hc hS ha hb hc' hd hab hbc hcd hac hbd
    · have hnb : b ∉ S := fun h => ha (hi b h a (le_of_lt hab))
      have hnc : c ∉ S := fun h => ha (hi c h a (le_of_lt (hab.trans hbc)))
      have hnd : d ∉ S := fun h => ha (hi d h a (le_of_lt (hab.trans (hbc.trans hcd))))
      exact P.no_crossing_of_onBlock_legal Sᶜ (P.complement_closed S hc) hT
        (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr hnb)
        (Finset.mem_compl.mpr hnc) (Finset.mem_compl.mpr hnd) hab hbc hcd hac hbd

/-- The first pair closes an initial block; this is the canonical Catalan cut. -/
theorem first_pair_closed (hP : P.Legal) (hn : 0 < n) :
    ∀ x ∈ (Finset.univ.filter fun x : Fin n => x ≤ P.pair ⟨0,hn⟩),
      P.pair x ∈ (Finset.univ.filter fun x : Fin n => x ≤ P.pair ⟨0,hn⟩) := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  let a : Fin n := ⟨0,hn⟩
  by_cases hx₀ : x = a
  · subst x
    exact le_rfl
  by_cases hxb : x = P.pair a
  · rw [hxb, P.involutive]
    change 0 ≤ (P.pair a).val
    exact Nat.zero_le _
  have hax : a < x := by
    have hnv : x.val ≠ 0 := fun h => hx₀ (Fin.ext h)
    change 0 < x.val
    omega
  exact le_of_lt (P.partner_inside hP rfl hax (lt_of_le_of_ne hx hxb)).2

end PairPartition
end WaveTurbulence.Reg
