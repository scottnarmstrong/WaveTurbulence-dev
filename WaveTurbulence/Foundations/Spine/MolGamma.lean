/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolRung
import Mathlib.Tactic
/-! The rung identity `Γ_a + Γ_b = ⟨ρ, Y⟩` for an interior ladder rung (TARGET L2013–L2014,
`Γ_v + Γ_w = 2 r · y_w`), from the molecule structure and charge conservation. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LadderDisjoint
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem directed_single (M : Molecule V D) {a b : V} {p : D} (h : neighborDarts M a b = {p}) :
    M.Directed a b ↔ M.out p = true := by
  constructor
  · rintro ⟨z, hz1, hz2, hz3⟩
    have : z ∈ neighborDarts M a b := (mem_neighborDarts' M a b z).mpr ⟨hz2, hz3⟩
    rw [h, Finset.mem_singleton] at this
    rwa [this] at hz1
  · intro hp
    have hp' : p ∈ neighborDarts M a b := by rw [h]; exact Finset.mem_singleton_self p
    obtain ⟨h1, h2⟩ := (mem_neighborDarts' M a b p).mp hp'
    exact ⟨p, hp, h1, h2⟩

theorem neighborDarts_swap_single (M : Molecule V D) {a b : V} {p : D}
    (h : neighborDarts M a b = {p}) : neighborDarts M b a = {M.mate p} := by
  ext z
  rw [Finset.mem_singleton, mem_neighborDarts']
  constructor
  · rintro ⟨h1, h2⟩
    have : M.mate z ∈ neighborDarts M a b := (mem_neighborDarts' M a b _).mpr ⟨h2, by rw [M.mate_mate]; exact h1⟩
    rw [h, Finset.mem_singleton] at this
    rw [← this, M.mate_mate]
  · rintro rfl
    have hp : p ∈ neighborDarts M a b := by rw [h]; exact Finset.mem_singleton_self p
    obtain ⟨h1, h2⟩ := (mem_neighborDarts' M a b p).mp hp
    exact ⟨h2, by rw [M.mate_mate]; exact h1⟩

theorem dartSign_eq_neg_of_iff (M : Molecule V D) {a la b lb : V} {p q : D}
    (hp : neighborDarts M a la = {p}) (hq : neighborDarts M b lb = {q})
    (h : M.Directed la a ↔ M.Directed b lb) : M.dartSign q = - M.dartSign p := by
  have h1 := directed_single M (neighborDarts_swap_single M hp)
  have h2 := directed_single M hq
  rw [h1, h2] at h
  unfold Molecule.dartSign
  rw [M.out_mate] at h
  by_cases hop : M.out p = true
  · have : M.out q = false := by
      by_contra hc
      have hc' : M.out q = true := by simpa using hc
      have := h.mpr hc'
      simp [hop] at this
    simp [hop, this]
  · have hop' : M.out p = false := by simpa using hop
    have : M.out q = true := h.mp (by simp [hop'])
    simp [hop', this]

theorem dartSign_eq_neg_of_iff' (M : Molecule V D) {a ra b rb : V} {p q : D}
    (hp : neighborDarts M a ra = {p}) (hq : neighborDarts M b rb = {q})
    (h : M.Directed a ra ↔ M.Directed rb b) : M.dartSign q = - M.dartSign p := by
  have h1 := directed_single M hp
  have h2 := directed_single M (neighborDarts_swap_single M hq)
  rw [h1, h2] at h
  unfold Molecule.dartSign
  rw [M.out_mate] at h
  by_cases hop : M.out p = true
  · have : M.out q = false := by simpa using h.mp hop
    simp [hop, this]
  · have hop' : M.out p = false := by simpa using hop
    have : M.out q = true := by
      by_contra hc
      have hc' : M.out q = false := by simpa using hc
      have := h.mpr (by simp [hc'])
      simp [hop'] at this
    simp [hop', this]

theorem norm_sq_sub_eq {d : ℕ} (x y : Mom d) :
    ‖x‖ ^ 2 - ‖y‖ ^ 2 = inner ℝ (x - y) (x + y) := by
  rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm x y]
  ring

theorem gamma_rung {d : ℕ} (M : Molecule V D) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x, κ (M.mate x) = κ x) {a b la ra lb rb : V}
    (hab : a ≠ b) (hala : a ≠ la) (hara : a ≠ ra) (hbla : b ≠ la) (hbra : b ≠ ra) (hlara : la ≠ ra)
    (hbalb : b ≠ lb) (hbrb : b ≠ rb) (haab : a ≠ lb) (haarb : a ≠ rb) (hlbrb : lb ≠ rb)
    (h2 : M.bondsBetween a b = 2) (hla : M.bondsBetween a la = 1) (hra : M.bondsBetween a ra = 1)
    (hlb : M.bondsBetween b lb = 1) (hrb : M.bondsBetween b rb = 1)
    (hda : M.deg a ≤ 4) (hdb : M.deg b ≤ 4)
    (hdirL : M.Directed la a ↔ M.Directed b lb) (hdirR : M.Directed a ra ↔ M.Directed rb b)
    (ca : ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x = 0)
    (cb : ∑ x ∈ M.dartsAt b, M.dartSign x • Molecule.kvec L w κ x = 0) :
    ∃ pL pR qL qR : D, neighborDarts M a la = {pL} ∧ neighborDarts M a ra = {pR} ∧
      neighborDarts M b lb = {qL} ∧ neighborDarts M b rb = {qR} ∧
      M.dartSign pR • (Molecule.kvec L w κ pR - Molecule.kvec L w κ qR) =
        - (M.dartSign pL • (Molecule.kvec L w κ pL - Molecule.kvec L w κ qL)) ∧
      M.Gamma L w κ a + M.Gamma L w κ b =
        inner ℝ (M.dartSign pL • (Molecule.kvec L w κ pL - Molecule.kvec L w κ qL))
          ((Molecule.kvec L w κ pL + Molecule.kvec L w κ qL) -
            (Molecule.kvec L w κ pR + Molecule.kvec L w κ qR)) := by
  have hkm : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := fun x => by
    simp [Molecule.kvec, hκ x]
  have hsm : ∀ x, M.dartSign (M.mate x) = - M.dartSign x := fun x => by
    unfold Molecule.dartSign; rw [M.out_mate]; cases M.out x <;> simp
  obtain ⟨pL, pR, qL, qR, hpL, hpR, hqL, hqR, hsum⟩ := rung_sum M hab hala hara hbla hbra hlara hbalb
    hbrb haab haarb hlbrb h2 hla hra hlb hrb hda hdb
  have s1 := hsum (fun x => M.dartSign x • Molecule.kvec L w κ x) (fun x => by simp [hsm, hkm])
  have s2 := hsum (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) (fun x => by simp [hsm, hkm])
  rw [ca, cb, add_zero] at s1
  have σL := dartSign_eq_neg_of_iff M hpL hqL hdirL
  have σR := dartSign_eq_neg_of_iff' M hpR hqR hdirR
  have hΓ : M.Gamma L w κ a + M.Gamma L w κ b = _ := s2
  refine ⟨pL, pR, qL, qR, hpL, hpR, hqL, hqR, ?_, ?_⟩
  · rw [σL, σR] at s1
    simp only [neg_smul] at s1
    rw [smul_sub, smul_sub]
    have : M.dartSign pL • Molecule.kvec L w κ pL + M.dartSign pR • Molecule.kvec L w κ pR +
        -(M.dartSign pL • Molecule.kvec L w κ qL) + -(M.dartSign pR • Molecule.kvec L w κ qR) = 0 := by
      simpa using s1.symm
    rw [eq_neg_iff_add_eq_zero]
    rw [← this]; abel
  · rw [hΓ, σL, σR]
    set ζL := M.dartSign pL
    set ζR := M.dartSign pR
    have hζL : ζL * ζL = 1 := by
      simp only [ζL, Molecule.dartSign]; split_ifs <;> norm_num
    have hζR : ζR * ζR = 1 := by
      simp only [ζR, Molecule.dartSign]; split_ifs <;> norm_num
    have hflux : ζR • (Molecule.kvec L w κ pR - Molecule.kvec L w κ qR) =
        - (ζL • (Molecule.kvec L w κ pL - Molecule.kvec L w κ qL)) := by
      rw [σL, σR] at s1
      simp only [neg_smul] at s1
      rw [smul_sub, smul_sub]
      have : ζL • Molecule.kvec L w κ pL + ζR • Molecule.kvec L w κ pR +
          -(ζL • Molecule.kvec L w κ qL) + -(ζR • Molecule.kvec L w κ qR) = 0 := by
        simpa using s1.symm
      rw [eq_neg_iff_add_eq_zero, ← this]; abel
    set kp := Molecule.kvec L w κ pL
    set kq := Molecule.kvec L w κ qL
    set rp := Molecule.kvec L w κ pR
    set rq := Molecule.kvec L w κ qR
    have e1 := norm_sq_sub_eq kp kq
    have e2 := norm_sq_sub_eq rp rq
    have hin : inner ℝ (ζR • (rp - rq)) (rp + rq) = - inner ℝ (ζL • (kp - kq)) (rp + rq) := by
      rw [hflux, inner_neg_left]
    have hin' : ζR * inner ℝ (rp - rq) (rp + rq) = -(ζL * inner ℝ (kp - kq) (rp + rq)) := by
      rw [real_inner_smul_left, real_inner_smul_left] at hin; exact hin
    rw [real_inner_smul_left, inner_sub_right, ← e1]
    linear_combination ζR * e2 + hin'

end WaveTurbulence.Ladder
