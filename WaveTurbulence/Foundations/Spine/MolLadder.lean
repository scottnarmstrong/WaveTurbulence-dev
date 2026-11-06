/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolGamma
import Mathlib.Tactic
/-! Ladder presentations indexed by `ℕ`, the rail darts, and the interior-rung identity. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LadderDisjoint
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A row of a presentation extended to `ℕ` (junk beyond `m`). -/
def rowN {m : ℕ} (u : Fin (m + 1) → V) (j : ℕ) : V := u ⟨min j m, by omega⟩

theorem rowN_of_le {m : ℕ} (u : Fin (m + 1) → V) {j : ℕ} (h : j ≤ m) :
    rowN u j = u ⟨j, by omega⟩ := by
  unfold rowN; simp [min_eq_left h]

section
variable (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V}

theorem ladderN_rail (hL : M.IsLadder u v) {j : ℕ} (hj : j < m) :
    M.bondsBetween (rowN u j) (rowN u (j + 1)) = 1 ∧ M.bondsBetween (rowN v j) (rowN v (j + 1)) = 1 ∧
      (M.Directed (rowN u j) (rowN u (j + 1)) ↔ M.Directed (rowN v (j + 1)) (rowN v j)) := by
  have := hL.2.2.2.2 ⟨j, hj⟩
  rw [rowN_of_le u hj.le, rowN_of_le v hj.le, rowN_of_le u hj, rowN_of_le v hj]
  exact this

theorem ladderN_rung (hL : M.IsLadder u v) {j : ℕ} (hj : j ≤ m) :
    M.bondsBetween (rowN u j) (rowN v j) = 2 := by
  rw [rowN_of_le u hj, rowN_of_le v hj]; exact hL.2.2.2.1 ⟨j, by omega⟩

theorem ladderN_uu (hL : M.IsLadder u v) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (h : i ≠ j) :
    rowN u i ≠ rowN u j := by
  rw [rowN_of_le u hi]
  intro he
  have := hL.2.1 (a₁ := Sum.inl ⟨i, by omega⟩) (a₂ := Sum.inl ⟨j, by omega⟩)
    (by rw [rowN_of_le u hj] at he; simpa using he)
  simp at this; exact h this

theorem ladderN_vv (hL : M.IsLadder u v) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (h : i ≠ j) :
    rowN v i ≠ rowN v j := by
  rw [rowN_of_le v hi]
  intro he
  have := hL.2.1 (a₁ := Sum.inr ⟨i, by omega⟩) (a₂ := Sum.inr ⟨j, by omega⟩)
    (by rw [rowN_of_le v hj] at he; simpa using he)
  simp at this; exact h this

theorem ladderN_uv (hL : M.IsLadder u v) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    rowN u i ≠ rowN v j := by
  rw [rowN_of_le u hi, rowN_of_le v hj]
  intro he
  have := hL.2.1 (a₁ := Sum.inl ⟨i, by omega⟩) (a₂ := Sum.inr ⟨j, by omega⟩) (by simpa using he)
  simp at this

end

section Gam
variable {d : ℕ} (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V}

theorem exists_rails (hL : M.IsLadder u v) :
    ∃ uR vR : ℕ → D, ∀ j < m, neighborDarts M (rowN u j) (rowN u (j + 1)) = {uR j} ∧
      neighborDarts M (rowN v j) (rowN v (j + 1)) = {vR j} := by
  have hex : ∀ j : ℕ, ∃ p q : D, j < m → neighborDarts M (rowN u j) (rowN u (j + 1)) = {p} ∧
      neighborDarts M (rowN v j) (rowN v (j + 1)) = {q} := by
    intro j
    by_cases hj : j < m
    · have h1 := ladderN_rail M hL hj
      have e1 := card_neighborDarts M (ladderN_uu M hL (by omega : j ≤ m) (by omega : j + 1 ≤ m)
        (by omega))
      have e2 := card_neighborDarts M (ladderN_vv M hL (by omega : j ≤ m) (by omega : j + 1 ≤ m)
        (by omega))
      rw [h1.1] at e1; rw [h1.2.1] at e2
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp e1
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp e2
      exact ⟨p, q, fun _ => ⟨hp, hq⟩⟩
    · have h0 : 0 < m := hL.1
      have e1 := card_neighborDarts M (ladderN_uu M hL (by omega : 0 ≤ m) (by omega : 1 ≤ m)
        (by omega))
      have h1 := ladderN_rail M hL h0
      rw [h1.1] at e1
      obtain ⟨p, _⟩ := Finset.card_eq_one.mp e1
      exact ⟨p, p, fun h => absurd h hj⟩
  choose uR vR h using hex
  exact ⟨uR, vR, fun j hj => h j hj⟩

/-- The flux through the `i`-th pair of rails. -/
noncomputable def flux (M : Molecule V D) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (uR vR : ℕ → D)
    (i : ℕ) : Mom d :=
  M.dartSign (uR i) • (Molecule.kvec L w κ (uR i) - Molecule.kvec L w κ (vR i))

/-- The vector `Y_j` of the rung identity. -/
noncomputable def Yrung (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (uR vR : ℕ → D) (j : ℕ) : Mom d :=
  (Molecule.kvec L w κ (uR (j - 1)) + Molecule.kvec L w κ (vR (j - 1))) -
    (Molecule.kvec L w κ (uR j) + Molecule.kvec L w κ (vR j))

theorem ladder_gamma_rung (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) (hL : M.IsLadder u v) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (uR vR : ℕ → D)
    (huR : ∀ j < m, neighborDarts M (rowN u j) (rowN u (j + 1)) = {uR j} ∧
      neighborDarts M (rowN v j) (rowN v (j + 1)) = {vR j})
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m)
    (ca : ∑ x ∈ M.dartsAt (rowN u j), M.dartSign x • Molecule.kvec L w κ x = 0)
    (cb : ∑ x ∈ M.dartsAt (rowN v j), M.dartSign x • Molecule.kvec L w κ x = 0) :
    M.Gamma L w κ (rowN u j) + M.Gamma L w κ (rowN v j) =
      inner ℝ (- flux M L w κ uR vR (j - 1)) (Yrung L w κ uR vR j) ∧
    flux M L w κ uR vR j = flux M L w κ uR vR (j - 1) := by
  have hkm : ∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := fun x => by
    simp [Molecule.kvec, hκ x]
  have hsm : ∀ x, M.dartSign (M.mate x) = - M.dartSign x := fun x => by
    unfold Molecule.dartSign; rw [M.out_mate]; cases M.out x <;> simp
  have hjm1 : j - 1 + 1 = j := by omega
  have hl := ladderN_rail M hL (show j - 1 < m by omega)
  rw [hjm1] at hl
  have hr := ladderN_rail M hL hjm
  have hu := huR (j - 1) (by omega)
  rw [hjm1] at hu
  have hu' := huR j hjm
  have hau : rowN u j ∈ M.atoms := by rw [rowN_of_le u hjm.le]; exact (hL.2.2.1 _).1
  have hav : rowN v j ∈ M.atoms := by rw [rowN_of_le v hjm.le]; exact (hL.2.2.1 _).2
  have hjle : j ≤ m := hjm.le
  have hd1 : j - 1 ≤ m := by omega
  have hd2 : j + 1 ≤ m := by omega
  obtain ⟨pL, pR, qL, qR, hpL, hpR, hqL, hqR, hflux, hΓ⟩ := gamma_rung M L w κ hκ
    (a := rowN u j) (b := rowN v j) (la := rowN u (j - 1)) (ra := rowN u (j + 1))
    (lb := rowN v (j - 1)) (rb := rowN v (j + 1))
    (ladderN_uv M hL hjle hjle) (ladderN_uu M hL hjle hd1 (by omega)) (ladderN_uu M hL hjle hd2 (by omega))
    (Ne.symm (ladderN_uv M hL hd1 hjle)) (Ne.symm (ladderN_uv M hL hd2 hjle))
    (ladderN_uu M hL hd1 hd2 (by omega)) (ladderN_vv M hL hjle hd1 (by omega))
    (ladderN_vv M hL hjle hd2 (by omega)) (ladderN_uv M hL hjle hd1) (ladderN_uv M hL hjle hd2)
    (ladderN_vv M hL hd1 hd2 (by omega)) (ladderN_rung M hL hjle)
    (by rw [LadderDisjoint.bondsBetween_comm]; exact hl.1) hr.1
    (by rw [LadderDisjoint.bondsBetween_comm]; exact hl.2.1) hr.2.1 (hM _ hau) (hM _ hav)
    hl.2.2 hr.2.2 ca cb
  have e1 : pL = M.mate (uR (j - 1)) := by
    have := neighborDarts_swap_single M hu.1
    rw [hpL] at this; exact Finset.singleton_inj.mp this
  have e2 : qL = M.mate (vR (j - 1)) := by
    have := neighborDarts_swap_single M hu.2
    rw [hqL] at this; exact Finset.singleton_inj.mp this
  have e3 : pR = uR j := by rw [hu'.1] at hpR; exact (Finset.singleton_inj.mp hpR).symm
  have e4 : qR = vR j := by rw [hu'.2] at hqR; exact (Finset.singleton_inj.mp hqR).symm
  subst e1 e2 e3 e4
  simp only [hkm, hsm, flux, Yrung] at hflux hΓ ⊢
  refine ⟨?_, ?_⟩
  · rw [hΓ, neg_smul]
  · rw [hflux, neg_smul, neg_neg]

theorem flux_const (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) (hL : M.IsLadder u v) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (uR vR : ℕ → D)
    (huR : ∀ j < m, neighborDarts M (rowN u j) (rowN u (j + 1)) = {uR j} ∧
      neighborDarts M (rowN v j) (rowN v (j + 1)) = {vR j})
    (hca : ∀ j, 1 ≤ j → j < m →
      ∑ x ∈ M.dartsAt (rowN u j), M.dartSign x • Molecule.kvec L w κ x = 0 ∧
      ∑ x ∈ M.dartsAt (rowN v j), M.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ i < m, flux M L w κ uR vR i = flux M L w κ uR vR 0 := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have := (ladder_gamma_rung M hM hL L w κ hκ uR vR huR (j := i + 1) (by omega) hi
      (hca _ (by omega) hi).1 (hca _ (by omega) hi).2).2
    rw [this]; simpa using ih (by omega)

theorem flux_zero_eq_gap (hL : M.IsLadder u v) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (uR vR : ℕ → D)
    (huR : ∀ j < m, neighborDarts M (rowN u j) (rowN u (j + 1)) = {uR j} ∧
      neighborDarts M (rowN v j) (rowN v (j + 1)) = {vR j})
    (hm : 1 ≤ m) {r : Mom d} (hr : M.IsLadderGap L w κ u v hm r) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ flux M L w κ uR vR 0 = s • r := by
  obtain ⟨x, y, hx, hy, hxa, hya, hr⟩ := hr
  have h0 := huR 0 (by omega)
  have hu0 : rowN u 0 = u 0 := by rw [rowN_of_le u (Nat.zero_le _)]; rfl
  have hv0 : rowN v 0 = v 0 := by rw [rowN_of_le v (Nat.zero_le _)]; rfl
  have hu1 : rowN u 1 = u ⟨1, by omega⟩ := rowN_of_le u hm
  have hv1 : rowN v 1 = v ⟨1, by omega⟩ := rowN_of_le v hm
  have hne : u 0 ≠ u ⟨1, by omega⟩ := by
    have := ladderN_uu M hL (Nat.zero_le m) hm (by omega)
    rwa [hu0, hu1] at this
  have hne' : v 0 ≠ v ⟨1, by omega⟩ := by
    have := ladderN_vv M hL (Nat.zero_le m) hm (by omega)
    rwa [hv0, hv1] at this
  have hxm : M.atom (M.mate x) = u ⟨1, by omega⟩ := by
    unfold Molecule.ends at hx
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hxa.symm.trans h1) hne
  have hym : M.atom (M.mate y) = v ⟨1, by omega⟩ := by
    unfold Molecule.ends at hy
    rw [Sym2.eq_iff] at hy
    rcases hy with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd (hya.symm.trans h1) hne'
  have hxN : x ∈ neighborDarts M (rowN u 0) (rowN u (0 + 1)) := by
    rw [mem_neighborDarts', hu0]; simpa [hu1] using ⟨hxa, hxm⟩
  have hyN : y ∈ neighborDarts M (rowN v 0) (rowN v (0 + 1)) := by
    rw [mem_neighborDarts', hv0]; simpa [hv1] using ⟨hya, hym⟩
  rw [h0.1, Finset.mem_singleton] at hxN
  rw [h0.2, Finset.mem_singleton] at hyN
  refine ⟨M.dartSign (uR 0), ?_, ?_⟩
  · unfold Molecule.dartSign; split_ifs <;> simp
  · unfold flux
    rw [← hxN, ← hyN, hr]
    rfl

end Gam

end WaveTurbulence.Ladder
