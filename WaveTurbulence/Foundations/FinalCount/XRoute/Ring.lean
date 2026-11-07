/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.XRoute.Route
import Mathlib.Tactic

/-! # G8-XROUTE: a ring of two triple bonds on four atoms (Y)-reduces to `Q`

`p ≡ q`, `r ≡ t`, `p – r`, `q – t`: the chain `{p, q}` (a (Y2) sequence with `n = 0`) leaves `Q`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem bonds_card_reg {M : Molecule V D} (hreg : ∀ a ∈ M.atoms, M.deg a = 4) :
    M.bonds.card * 2 = 4 * M.atoms.card := by
  have h := Mole.sum_degrees_eq_two_mul_bonds M
  rw [sum_congr rfl hreg, sum_const, smul_eq_mul] at h
  omega

theorem exists_dart_of_bb {M : Molecule V D} {a b : V} (hab : a ≠ b) (h : 1 ≤ M.bondsBetween a b) :
    ∃ x, M.atom x = a ∧ M.atom (M.mate x) = b := by
  rw [← Degen.card_neighborDarts M hab] at h
  obtain ⟨z, hz⟩ := card_pos.mp h
  exact ⟨z, (Degen.mem_neighborDarts M a b z).mp hz⟩

theorem triple_to_Q {N : Molecule V D} (hR : RegCore N) {p q r t : V}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpt : p ≠ t) (hqr : q ≠ r) (hqt : q ≠ t) (hrt : r ≠ t)
    (hs : N.atoms = {p, q, r, t}) (h3 : N.bondsBetween p q = 3) (h1 : N.bondsBetween p r = 1)
    (h2 : N.bondsBetween q t = 1) (h4 : N.bondsBetween r t = 3) : YReachesQT N := by
  classical
  have hp : p ∈ N.atoms := by rw [hs]; simp
  have hq : q ∈ N.atoms := by rw [hs]; simp
  have hr : r ∈ N.atoms := by rw [hs]; simp
  have ht : t ∈ N.atoms := by rw [hs]; simp
  let C : YChain N :=
    { n := 0, a := fun _ => p, b := fun _ => q
      inj_a := fun i hi j hj _ => by omega
      inj_b := fun i hi j hj _ => by omega
      ne_ab := fun _ _ _ _ => hpq
      mem := fun _ _ => ⟨hp, hq⟩
      triple := h3
      rung := fun i hi hi' => by omega
      rail := fun i hi => by omega
      sat := fun i hi => by omega }
  have hset : C.set = {p, q} := by
    ext z; simp [YChain.set, C]
  obtain ⟨x, hx1, hx2⟩ := exists_dart_of_bb hpr h1.ge
  obtain ⟨y, hy1, hy2⟩ := exists_dart_of_bb hqt h2.ge
  let E : Y2End C :=
    { x := x, y := y, hx := hx1, hy := hy1
      hxo := by rw [hx2, hset]; simp [hpr.symm, hqr.symm]
      hyo := by rw [hy2, hset]; simp [hpt.symm, hqt.symm]
      far := by rw [hx2, hy2]; exact hrt
      deg_a := hR.reg p hp
      deg_b := hR.reg q hq }
  have hcomp : N.bondsBetween (N.atom (N.mate E.x)) (N.atom (N.mate E.y)) ≠ 2 := by
    show N.bondsBetween (N.atom (N.mate x)) (N.atom (N.mate y)) ≠ 2
    rw [hx2, hy2, h4]; omega
  refine YReachesQT.y2 N hR.cap C E hcomp ?_
  obtain ⟨hcapP, hloopP, hregP, hconnP⟩ := E.post_props hR.cap hR.loop hR.reg hR.conn
  set T := E.toTwoExit hR.cap with hT
  have hY : T.Y = {p, q} := by rw [hT, E.toTwoExit_Y hR.cap, hset]
  have hpa : T.post.atoms = {r, t} := by
    rw [T.post_atoms, hY, hs]
    ext z
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨(rfl | rfl | rfl | rfl), h1, h2⟩
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hpr.symm, hqr.symm⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hpt.symm, hqt.symm⟩
  have hpair : s(T.d, T.c) = s(r, t) := by
    have := toTwoExit_pair E hR.cap
    rw [← hT] at this
    rw [this]
    show s(N.atom (N.mate x), N.atom (N.mate y)) = _
    rw [hx2, hy2]
  have hrY : r ∉ T.Y := by rw [hY]; simp [hpr.symm, hqr.symm]
  have htY : t ∉ T.Y := by rw [hY]; simp [hpt.symm, hqt.symm]
  have hbb : T.post.bondsBetween r t = 4 := by
    have : T.post.bondsBetween r t = N.bondsBetween r t + (if s(T.d, T.c) = s(r, t) then 1 else 0) := by
      change (Mole.addBond (Degen.eraseAtoms N T.Y) T.d T.c).bondsBetween r t = _
      rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq N T.Y hrY htY]
    rw [this, if_pos hpair, h4]
  have hbc : T.post.bonds.card = 4 := by
    have := bonds_card_reg hregP
    rw [hpa, card_pair hrt] at this
    omega
  refine YReachesQT.done _ ?_ (Or.inl ⟨r, t, hrt, hpa, hbb, hbc⟩)
  intro a b
  by_cases ha : a ∈ T.post.atoms
  · by_cases hb : b ∈ T.post.atoms
    · rw [hpa] at ha hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rw [bondsBetween_self_eq_zero hloopP]; omega
      · omega
      · rw [bondsBetween_symm]; omega
      · rw [bondsBetween_self_eq_zero hloopP]; omega
    · rw [bondsBetween_symm, bb_zero_of_notMem' _ hb]; omega
  · rw [bb_zero_of_notMem' _ ha]; omega

end WaveTurbulence.FinalCountG8
