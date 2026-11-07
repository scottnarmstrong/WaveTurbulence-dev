/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.BiBridgeRank
import Mathlib.Tactic

/-! # Chains of degree-two atoms (`in = out = 1`)

Local facts for operation (c)/(d) (DH23 L1861, L1865): the two darts of a chain atom, the conservation law and the energy at it,
propagation of one label along a connected chain, and the absence of ladder cells in a set of degree-two atoms.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An atom with `out = in = 1` has exactly two darts, one outgoing and one incoming. -/
theorem chain_darts (M : Molecule V D) {v : V} (ho : M.outdeg v = 1) (hi : M.indeg v = 1) :
    ∃ w w' : D, M.out w = true ∧ M.out w' = false ∧ M.atom w = v ∧ M.atom w' = v ∧ M.dartsAt v = {w, w'} := by
  classical
  unfold Molecule.outdeg at ho
  unfold Molecule.indeg at hi
  obtain ⟨w, hw⟩ := card_eq_one.mp ho
  obtain ⟨w', hw'⟩ := card_eq_one.mp hi
  have hwm : w ∈ (M.dartsAt v).filter fun x => M.out x = true := by rw [hw]; simp
  have hwm' : w' ∈ (M.dartsAt v).filter fun x => M.out x = false := by rw [hw']; simp
  simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hwm hwm'
  refine ⟨w, w', hwm.2, hwm'.2, hwm.1, hwm'.1, ?_⟩
  ext x
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hx
    cases hxo : M.out x
    · right
      have : x ∈ (M.dartsAt v).filter fun x => M.out x = false := by
        simp [Molecule.dartsAt, hx, hxo]
      rw [hw'] at this; simpa using this
    · left
      have : x ∈ (M.dartsAt v).filter fun x => M.out x = true := by
        simp [Molecule.dartsAt, hx, hxo]
      rw [hw] at this; simpa using this
  · rintro (rfl | rfl)
    exacts [hwm.1, hwm'.1]

theorem chain_conservation (M : Molecule V D) {v : V} {w w' : D} (hw : M.out w = true) (hw' : M.out w' = false)
    (hd : M.dartsAt v = {w, w'}) {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hdec : (∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L 0 κ x) = c v) :
    Molecule.kvec L 0 κ w - Molecule.kvec L 0 κ w' = c v := by
  have hne : w ≠ w' := by rintro rfl; rw [hw] at hw'; exact absurd hw' (by simp)
  rw [hd, sum_pair hne] at hdec
  simpa [Molecule.dartSign, hw, hw', sub_eq_add_neg] using hdec

theorem chain_gamma (M : Molecule V D) {v : V} {w w' : D} (hw : M.out w = true) (hw' : M.out w' = false)
    (hd : M.dartsAt v = {w, w'}) {d : ℕ} (L : ℝ) (κ : D → (Fin d → ℤ)) :
    M.Gamma L 0 κ v = ‖Molecule.kvec L 0 κ w‖ ^ 2 - ‖Molecule.kvec L 0 κ w'‖ ^ 2 := by
  have hne : w ≠ w' := by rintro rfl; rw [hw] at hw'; exact absurd hw' (by simp)
  unfold Molecule.Gamma
  rw [hd, sum_pair hne]
  simp [Molecule.dartSign, hw, hw', sub_eq_add_neg]

/-- If one dart of a chain atom has the same label in two decorations (same charges), all of its darts do. -/
theorem chain_atom_agree (M : Molecule V D) {v : V} (ho : M.outdeg v = 1) (hi : M.indeg v = 1) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hκ : ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L 0 κ x = c v)
    (hκ' : ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L 0 κ' x = c v) {z : D} (hz : M.atom z = v)
    (hag : κ z = κ' z) : ∀ x, M.atom x = v → κ x = κ' x := by
  obtain ⟨w, w', hw, hw', hwv, hw'v, hd⟩ := chain_darts M ho hi
  have h1 := chain_conservation M hw hw' hd hκ
  have h2 := chain_conservation M hw hw' hd hκ'
  have hzm : z ∈ M.dartsAt v := by simp [Molecule.dartsAt, hz]
  rw [hd] at hzm
  have hboth : κ w = κ' w ∧ κ w' = κ' w' := by
    have key : κ w = κ' w ↔ κ w' = κ' w' := by
      have e : Molecule.kvec L 0 κ w' = Molecule.kvec L 0 κ w - c v := by rw [← h1]; abel
      have e' : Molecule.kvec L 0 κ' w' = Molecule.kvec L 0 κ' w - c v := by rw [← h2]; abel
      constructor
      · intro h
        have : Molecule.kvec L 0 κ w' = Molecule.kvec L 0 κ' w' := by
          rw [e, e']; simp only [Molecule.kvec, zero_add, h]
        simp only [Molecule.kvec, zero_add] at this
        exact latticePoint_injective hL this
      · intro h
        have : Molecule.kvec L 0 κ w = Molecule.kvec L 0 κ' w := by
          have a1 : Molecule.kvec L 0 κ w = Molecule.kvec L 0 κ w' + c v := by rw [← h1]; abel
          have a2 : Molecule.kvec L 0 κ' w = Molecule.kvec L 0 κ' w' + c v := by rw [← h2]; abel
          rw [a1, a2]; simp only [Molecule.kvec, zero_add, h]
        simp only [Molecule.kvec, zero_add] at this
        exact latticePoint_injective hL this
    simp only [mem_insert, mem_singleton] at hzm
    rcases hzm with rfl | rfl
    · exact ⟨hag, key.mp hag⟩
    · exact ⟨key.mpr hag, hag⟩
  intro x hx
  have hxm : x ∈ M.dartsAt v := by simp [Molecule.dartsAt, hx]
  rw [hd] at hxm
  simp only [mem_insert, mem_singleton] at hxm
  rcases hxm with rfl | rfl
  exacts [hboth.1, hboth.2]

/-- **Propagation along a connected chain**: one agreeing label forces all labels on darts at the chain atoms. -/
theorem chain_agree (M : Molecule V D) {Y : Finset V} (hY : Y ⊆ M.atoms)
    (hch : ∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hconn : ∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b) {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d}
    {κ κ' : D → (Fin d → ℤ)} (hκ : M.IsDecoration L 0 c κ) (hκ' : M.IsDecoration L 0 c κ') {z0 : D}
    (hz0 : M.atom z0 ∈ Y) (hag : κ z0 = κ' z0) : ∀ z, M.atom z ∈ Y → κ z = κ' z := by
  classical
  set Zp : V → Prop := fun u => ∀ x, M.atom x = u → κ x = κ' x with hZp
  have hat : ∀ u ∈ Y, (∑ x ∈ M.dartsAt u, M.dartSign x • Molecule.kvec L 0 κ x = c u) ∧
      (∑ x ∈ M.dartsAt u, M.dartSign x • Molecule.kvec L 0 κ' x = c u) :=
    fun u hu => ⟨hκ.2 u (hY hu), hκ'.2 u (hY hu)⟩
  have step : ∀ u ∈ Y, ∀ v ∈ Y, (∃ x, M.atom x = u ∧ M.atom (M.mate x) = v) → Zp u → Zp v := by
    rintro u hu v hv ⟨x, hxu, hxv⟩ hZ
    have hxx : κ x = κ' x := hZ x hxu
    have hm : κ (M.mate x) = κ' (M.mate x) := by rw [hκ.1 x, hκ'.1 x]; exact hxx
    exact chain_atom_agree M (hch v hv).1 (hch v hv).2 hL (hat v hv).1 (hat v hv).2 hxv hm
  have key : ∀ u v, Relation.EqvGen (piece M Y).Adj u v → (u ∈ Y ↔ v ∈ Y) ∧ (u ∈ Y → (Zp u ↔ Zp v)) := by
    intro u v h
    induction h with
    | rel a b hab =>
      obtain ⟨x, hxa, hxb⟩ := hab
      have h1 := piece_dart_mem x
      have ha : a ∈ Y := hxa ▸ h1.1
      have hb : b ∈ Y := hxb ▸ h1.2
      have hxa' : M.atom x.val = a := hxa
      have hxb' : M.atom (M.mate x.val) = b := hxb
      refine ⟨⟨fun _ => hb, fun _ => ha⟩, fun _ => ⟨fun hz => step a ha b hb ⟨x.val, hxa', hxb'⟩ hz, fun hz => ?_⟩⟩
      exact step b hb a ha ⟨M.mate x.val, by simpa using hxb', by simpa [M.mate_mate] using hxa'⟩ hz
    | refl a => exact ⟨Iff.rfl, fun _ => Iff.rfl⟩
    | symm a b _ ih =>
      refine ⟨ih.1.symm, fun hb => ?_⟩
      have ha : a ∈ Y := ih.1.mpr hb
      exact (ih.2 ha).symm
    | trans a b c _ _ ih1 ih2 =>
      refine ⟨ih1.1.trans ih2.1, fun ha => ?_⟩
      exact (ih1.2 ha).trans (ih2.2 (ih1.1.mp ha))
  have hZ0 : Zp (M.atom z0) :=
    chain_atom_agree M (hch _ hz0).1 (hch _ hz0).2 hL (hat _ hz0).1 (hat _ hz0).2 rfl hag
  intro z hz
  exact ((key _ _ (hconn _ hz0 _ hz)).2 hz0).mp hZ0 z rfl

/-- An atom with two distinct neighbours, one of them by a double bond, has degree at least three. -/
theorem three_le_deg_of_double (M : Molecule V D) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h2 : 2 ≤ M.bondsBetween a b) (h1 : 1 ≤ M.bondsBetween a c) : 3 ≤ M.deg a := by
  classical
  have e1 := Degen.card_neighborDarts M hab
  have e2 := Degen.card_neighborDarts M hac
  have hdisj : Disjoint (Degen.neighborDarts M a b) (Degen.neighborDarts M a c) := by
    rw [disjoint_left]
    intro x hx hx'
    have := ((Degen.mem_neighborDarts M a b x).mp hx).2
    have := ((Degen.mem_neighborDarts M a c x).mp hx').2
    exact hbc (by simp_all)
  have hsub : Degen.neighborDarts M a b ∪ Degen.neighborDarts M a c ⊆ M.dartsAt a := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · exact (mem_filter.mp h).1
    · exact (mem_filter.mp h).1
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at this
  unfold Molecule.deg
  omega

/-- A set of atoms of degree at most two contains no ladder cell. -/
theorem no_cell_of_deg_le_two (M : Molecule V D) {S : Finset V} (hS : MoleProp.IsLadderCell M S)
    (hdeg : ∀ a ∈ S, M.deg a ≤ 2) : False := by
  classical
  obtain ⟨u, v, hL, rfl⟩ := hS
  obtain ⟨_, hinj, _, hrung, hrail⟩ := hL
  have h0 := (hrail 0).1
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0
  have hr0 := hrung 0
  have hne1 : u 0 ≠ v 0 := fun h => by
    have := hinj (a₁ := Sum.inl 0) (a₂ := Sum.inr 0) (by simpa using h); simp at this
  have hne2 : u 0 ≠ u 1 := fun h => by
    have := hinj (a₁ := Sum.inl 0) (a₂ := Sum.inl 1) (by simpa using h); simp at this
  have hne3 : v 0 ≠ u 1 := fun h => by
    have := hinj (a₁ := Sum.inr 0) (a₂ := Sum.inl 1) (by simpa using h); simp at this
  have h3 := three_le_deg_of_double M hne1 hne2 hne3 (by omega) (by omega)
  have hm : u 0 ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  have := hdeg _ hm
  omega

end WaveTurbulence.FinalCountG8
