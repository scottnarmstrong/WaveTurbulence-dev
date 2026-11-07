/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAdm
public import WaveTurbulence.Foundations.WaveB.Ladders
/-! # VINE-COUNT part 35: realisation independence of a sub-ladder's gap (R21 (2)(a)).

Let `(U, V)` be a ladder of a molecule with a decoration (conservation, `c = 0` at degree-`4` atoms), and let `(u, v)` be a
ladder whose first rung atom `u 0` lies in the atom set of `(U, V)`.  Then every first-rail gap of `(u, v)` has the same
norm as the first-rail gap of `(U, V)`.  Proof: the rung `(u 0, v 0)` is a rung `(U a, W a)` or `(W a, U a)` of `(U, V)`
(unique double partner); the atom `U a` has the degree-`4` neighbourhood `W a (×2)`, `U a'` (the standard rail) and the
first rail `u 1` of `(u, v)`.  If this rail is the standard one the gaps agree; otherwise conservation at the rung
(`Stage1.rung_conservation`) with the opposite directions of the two rail pairs gives equal norms. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.Stage1

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section SubLadder
variable {M : Molecule V D}

theorem dart_dir {a b : V} {z : D} (h1 : M.bondsBetween a b = 1) (hab : a ≠ b) (hz : M.atom z = a)
    (hz' : M.atom (M.mate z) = b) : M.Directed a b ↔ M.out z = true := by
  constructor
  · rintro ⟨x, hxo, hxa, hxb⟩
    have := uniq_dart hab h1 hxa hxb hz hz'
    rw [← this]; exact hxo
  · intro ho; exact ⟨z, ho, hz, hz'⟩

theorem sign_opp {p p1 q q1 : V} {x y : D} (hp : p ≠ p1) (hq : q ≠ q1) (h1 : M.bondsBetween p p1 = 1)
    (h2 : M.bondsBetween q q1 = 1) (hdir : M.Directed p p1 ↔ M.Directed q1 q) (hx : M.atom x = p)
    (hx' : M.atom (M.mate x) = p1) (hy : M.atom y = q) (hy' : M.atom (M.mate y) = q1) :
    M.dartSign y = - M.dartSign x := by
  have d1 := dart_dir h1 hp hx hx'
  have h2' : M.bondsBetween q1 q = 1 := by rw [Mole.bondsBetween_symm M]; exact h2
  have d2 := dart_dir h2' hq.symm hy' (by rw [M.mate_mate]; exact hy) 
  rw [d1, d2, M.out_mate] at hdir
  unfold Molecule.dartSign
  cases hx : M.out x <;> cases hy : M.out y <;> simp_all

theorem dartSign_abs (x : D) : M.dartSign x = 1 ∨ M.dartSign x = -1 := by
  unfold Molecule.dartSign; split_ifs <;> simp

theorem norm_eq_of_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s1 s2 : ℝ} (h1 : s1 = 1 ∨ s1 = -1)
    (h2 : s2 = 1 ∨ s2 = -1) {a b : E} (h : s1 • a + s2 • b = 0) : ‖a‖ = ‖b‖ := by
  have e : s1 • a = -(s2 • b) := eq_neg_of_add_eq_zero_left h
  have n1 : ‖s1 • a‖ = ‖a‖ := by rcases h1 with h | h <;> simp [h]
  have n2 : ‖s2 • b‖ = ‖b‖ := by rcases h2 with h | h <;> simp [h]
  rw [← n1, ← n2, e, norm_neg]

/-- **Local rung exchange.**  At a rung `(p, q)` of two degree-`4` atoms with two oppositely directed rail pairs
`(p → p1, q → q1)` and `(p → p2, q → q2)`, both pairs have the same gap norm (conservation at `p` and `q`). -/
theorem pair_gap_norm_eq (hMol : M.IsMolecule) {L : ℝ} {w : Mom d} {c : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hdec : M.IsDecoration L w c κ) (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0)
    {p q p1 p2 q1 q2 : V} (hpa : p ∈ M.atoms) (hqa : q ∈ M.atoms)
    (hpq : M.bondsBetween p q = 2) (hp1 : M.bondsBetween p p1 = 1) (hp2 : M.bondsBetween p p2 = 1)
    (hq1 : M.bondsBetween q q1 = 1) (hq2 : M.bondsBetween q q2 = 1)
    (hqp1 : q ≠ p1) (hqp2 : q ≠ p2) (hp12 : p1 ≠ p2) (hpq1 : p ≠ q1) (hpq2 : p ≠ q2) (hq12 : q1 ≠ q2)
    (hpq' : p ≠ q) (hpp1 : p ≠ p1) (hpp2 : p ≠ p2) (hqq1 : q ≠ q1) (hqq2 : q ≠ q2)
    (hd1 : M.Directed p p1 ↔ M.Directed q1 q) (hd2 : M.Directed p p2 ↔ M.Directed q2 q)
    {x1 y1 x2 y2 : D} (ax1 : M.atom x1 = p) (bx1 : M.atom (M.mate x1) = p1) (ay1 : M.atom y1 = q)
    (by1 : M.atom (M.mate y1) = q1) (ax2 : M.atom x2 = p) (bx2 : M.atom (M.mate x2) = p2)
    (ay2 : M.atom y2 = q) (by2 : M.atom (M.mate y2) = q2) :
    ‖Molecule.kvec L w κ x1 - Molecule.kvec L w κ y1‖ = ‖Molecule.kvec L w κ x2 - Molecule.kvec L w κ y2‖ := by
  have hpq2' : M.bondsBetween q p = 2 := by rw [Mole.bondsBetween_symm M]; exact hpq
  have hdp : M.deg p = 4 := deg_eq_four_of_counts hMol hpa hpq hp1 hp2 hqp1 hqp2 hp12 hpq' hpp1 hpp2
  have hdq : M.deg q = 4 := deg_eq_four_of_counts hMol hqa hpq2' hq1 hq2 hpq1 hpq2 hq12 hpq'.symm hqq1 hqq2
  have hcp : ∑ x ∈ M.dartsAt p, M.dartSign x • Molecule.kvec L w κ x = 0 :=
    (hdec.2 _ hpa).trans (hc _ hpa hdp)
  have hcq : ∑ x ∈ M.dartsAt q, M.dartSign x • Molecule.kvec L w κ x = 0 :=
    (hdec.2 _ hqa).trans (hc _ hqa hdq)
  have hk (x : D) : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec, hdec.1 x]
  obtain ⟨X1, X2, Y1, Y2, aX1, bX1, aX2, bX2, aY1, bY1, aY2, bY2, hsum⟩ :=
    rung_conservation (M := M) hk hpq hp1 hp2 hq1 hq2 hqp1 hqp2 hp12 hpq1 hpq2 hq12 hpq' hpp1 hpp2 hqq1 hqq2
      hdp hdq hcp hcq
  have e1 : x1 = X1 := uniq_dart hpp1 hp1 ax1 bx1 aX1 bX1
  have e2 : x2 = X2 := uniq_dart hpp2 hp2 ax2 bx2 aX2 bX2
  have f1 : y1 = Y1 := uniq_dart hqq1 hq1 ay1 by1 aY1 bY1
  have f2 : y2 = Y2 := uniq_dart hqq2 hq2 ay2 by2 aY2 bY2
  subst e1 e2 f1 f2
  have s1 := sign_opp hpp1 hqq1 hp1 hq1 hd1 ax1 bx1 ay1 by1
  have s2 := sign_opp hpp2 hqq2 hp2 hq2 hd2 ax2 bx2 ay2 by2
  rw [s1, s2] at hsum
  refine norm_eq_of_sum (dartSign_abs (M := M) x1) (dartSign_abs (M := M) x2) (a := Molecule.kvec L w κ x1 - Molecule.kvec L w κ y1)
    (b := Molecule.kvec L w κ x2 - Molecule.kvec L w κ y2) ?_
  rw [smul_sub, smul_sub]
  rw [neg_smul, neg_smul] at hsum
  rw [← hsum]; abel

section Std
variable {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}

theorem lad_ne_u {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W) {a b : Fin (m + 1)} (hab : a ≠ b) :
    U a ≠ U b := fun he => hab (by
  have := h.2.1 (show Sum.elim U W (Sum.inl a) = Sum.elim U W (Sum.inl b) from he)
  simpa using this)

theorem lad_ne_v {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W) {a b : Fin (m + 1)} (hab : a ≠ b) :
    W a ≠ W b := fun he => hab (by
  have := h.2.1 (show Sum.elim U W (Sum.inr a) = Sum.elim U W (Sum.inr b) from he)
  simpa using this)

theorem lad_ne_uv {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W) (a b : Fin (m + 1)) : U a ≠ W b :=
  fun he => by
  have := h.2.1 (show Sum.elim U W (Sum.inl a) = Sum.elim U W (Sum.inr b) from he)
  simp at this

/-- **The standard rail pair at a rung.**  Every rung `(U a, W a)` of a ladder has a neighbouring rung `a'` joined by
the two rails; the gap of the rail pair (computed with any darts) is the gap of a rail of the ladder. -/
theorem std_rail (hdec : M.IsDecoration L w c κ) {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W)
    (a : Fin (m + 1)) :
    ∃ a' : Fin (m + 1), a' ≠ a ∧ M.bondsBetween (U a) (U a') = 1 ∧ M.bondsBetween (W a) (W a') = 1 ∧
      (M.Directed (U a) (U a') ↔ M.Directed (W a') (W a)) ∧
      ∀ x y : D, M.atom x = U a → M.atom (M.mate x) = U a' → M.atom y = W a → M.atom (M.mate y) = W a' →
        ∃ (j : Fin m) (r0 : Mom d), IsRailGap M L w κ U W j r0 ∧
          ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖ = ‖r0‖ := by
  have hk (x : D) : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec, hdec.1 x]
  have hm := h.1
  by_cases hj : a.val < m
  · obtain ⟨i, rfl⟩ : ∃ i : Fin m, a = i.castSucc := ⟨⟨a.val, hj⟩, Fin.ext rfl⟩
    have hne : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
    obtain ⟨h1, h2, hd⟩ := h.2.2.2.2 i
    refine ⟨i.succ, hne.symm, h1, h2, hd, fun x y ax bx ay by' => ?_⟩
    obtain ⟨r0, hr0⟩ := railGap_exists h L w κ i
    obtain ⟨X, Y, aX, bX, aY, bY, hr⟩ := railGap_dart (lad_ne_u h hne) (lad_ne_v h hne) hr0
    have e1 : x = X := uniq_dart (lad_ne_u h hne) h1 ax bx aX bX
    have e2 : y = Y := uniq_dart (lad_ne_v h hne) h2 ay by' aY bY
    exact ⟨i, r0, hr0, by rw [hr, e1, e2]⟩
  · obtain ⟨i, rfl⟩ : ∃ i : Fin m, a = i.succ := ⟨⟨m - 1, by omega⟩, Fin.ext (by
      have := a.isLt; simp only [Fin.val_succ]; omega)⟩
    have hne : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
    obtain ⟨h1, h2, hd⟩ := h.2.2.2.2 i
    refine ⟨i.castSucc, hne, by rw [Mole.bondsBetween_symm M]; exact h1,
      by rw [Mole.bondsBetween_symm M]; exact h2, ?_, fun x y ax bx ay by' => ?_⟩
    · exact (LadderDisjoint.opposite_single_rails_flip M (lad_ne_u h hne) (lad_ne_v h hne) h1 h2 hd).symm
    · obtain ⟨r0, hr0⟩ := railGap_exists h L w κ i
      obtain ⟨X, Y, aX, bX, aY, bY, hr⟩ := railGap_dart (lad_ne_u h hne) (lad_ne_v h hne) hr0
      have e1 : M.mate x = X := uniq_dart (lad_ne_u h hne) h1 bx (by rw [M.mate_mate]; exact ax) aX bX
      have e2 : M.mate y = Y := uniq_dart (lad_ne_v h hne) h2 by' (by rw [M.mate_mate]; exact ay) aY bY
      exact ⟨i, r0, hr0, by rw [hr, ← e1, ← e2, hk, hk]⟩

/-- Swapping the two rows of a ladder negates every rail gap. -/
theorem railGap_swap_exists {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W) {j : Fin m} {r0 : Mom d}
    (hr : IsRailGap M L w κ W U j r0) : ∃ r1, IsRailGap M L w κ U W j r1 ∧ ‖r1‖ = ‖r0‖ := by
  obtain ⟨r1, h1⟩ := railGap_exists h L w κ j
  have hne : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
  obtain ⟨X, Y, aX, bX, aY, bY, hX⟩ := railGap_dart (lad_ne_u h hne) (lad_ne_v h hne) h1
  obtain ⟨X', Y', aX', bX', aY', bY', hX'⟩ := railGap_dart (lad_ne_v h hne) (lad_ne_u h hne) hr
  have e1 : X = Y' := uniq_dart (lad_ne_u h hne) (h.2.2.2.2 j).1 aX bX aY' bY'
  have e2 : Y = X' := uniq_dart (lad_ne_v h hne) (h.2.2.2.2 j).2.1 aY bY aX' bX'
  refine ⟨r1, h1, ?_⟩
  rw [hX, hX', e1, e2, ← norm_neg]; congr 1; abel

/-- **Rail pairs at a rung of a ladder have the gap of a rail of the ladder.**  `(p', q')` is any double-bonded pair
joined to the rung `(U a, W a)` by a single bond each, with opposite directions. -/
theorem rung_pair_gap (hMol : M.IsMolecule) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) {m : ℕ} {U W : Fin (m + 1) → V} (h : M.IsLadder U W)
    (a : Fin (m + 1)) {p' q' : V} (hpp : U a ≠ p') (hqq : W a ≠ q') (b1 : M.bondsBetween (U a) p' = 1)
    (b2 : M.bondsBetween (W a) q' = 1) (hd : M.Directed (U a) p' ↔ M.Directed q' (W a))
    (hb : M.bondsBetween p' q' = 2) (hpq : p' ≠ q') {x y : D} (ax : M.atom x = U a)
    (bx : M.atom (M.mate x) = p') (ay : M.atom y = W a) (by' : M.atom (M.mate y) = q') :
    ∃ (j : Fin m) (r0 : Mom d), IsRailGap M L w κ U W j r0 ∧
      ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖ = ‖r0‖ := by
  have hM : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => LadderDisjoint.deg_le_four M hMol hx
  obtain ⟨a', hne, b1', b2', hd', hstd⟩ := std_rail hdec h a
  by_cases hp : p' = U a'
  · subst hp
    have hq : q' = W a' := LadderDisjoint.sourceLadder_double_partner_eq M hM h a' hpq hb
    subst hq
    exact hstd x y ax bx ay by'
  · have hpb : M.bondsBetween (W a) (U a) = 2 := by rw [Mole.bondsBetween_symm M]; exact h.2.2.2.1 a
    obtain ⟨x1, hx1, hx1'⟩ := exists_dart (lad_ne_u h hne.symm) (by rw [b1']; exact Nat.one_pos)
    obtain ⟨y1, hy1, hy1'⟩ := exists_dart (lad_ne_v h hne.symm) (by rw [b2']; exact Nat.one_pos)
    obtain ⟨j, r0, hr0, hn0⟩ := hstd x1 y1 hx1 hx1' hy1 hy1'
    refine ⟨j, r0, hr0, ?_⟩
    rw [← hn0]
    have hq12 : W a' ≠ q' := by
      intro e
      subst e
      have hb' : M.bondsBetween (W a') p' = 2 := by rw [Mole.bondsBetween_symm M]; exact hb
      have := LadderDisjoint.sourceLadder_double_partner_eq M hM (LadderDisjoint.sourceLadder_swap M h) a'
        (fun e => hpq e.symm) hb'
      exact hp this
    refine (pair_gap_norm_eq hMol hdec hc (h.2.2.1 a).1 (h.2.2.1 a).2 (h.2.2.2.1 a) b1' b1 b2' b2
      (lad_ne_uv h a' a).symm (fun e => by have := h.2.2.2.1 a; rw [← e] at b1; omega) (Ne.symm hp) (lad_ne_uv h a a')
      (fun e => by rw [← e] at b2; omega) hq12 (lad_ne_uv h a a) (lad_ne_u h hne.symm) hpp
      (lad_ne_v h hne.symm) hqq hd' hd hx1 hx1' hy1 hy1' ax bx ay by').symm
  
end Std

section Main
variable {M : Molecule V D} {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}

/-- Wrapper: the first rail of a ladder `(u, v)` whose first rung is the rung `(U a, W a)` of `(U, V)`. -/
theorem lad_first_rail (hMol : M.IsMolecule) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) {m n : ℕ} {U W : Fin (m + 1) → V} {u v : Fin (n + 1) → V}
    (hB : M.IsLadder U W) (hs : M.IsLadder u v) (a : Fin (m + 1)) (hu : u 0 = U a) (hv : v 0 = W a)
    {r : Mom d} (hr : M.IsLadderGap L w κ u v hs.1 r) :
    ∃ (j : Fin m) (r0 : Mom d), IsRailGap M L w κ U W j r0 ∧ ‖r‖ = ‖r0‖ := by
  have hn := hs.1
  have hne : (⟨0, hn⟩ : Fin n).castSucc ≠ (⟨0, hn⟩ : Fin n).succ := by simp [Fin.ext_iff]
  have e0 : u (⟨0, hn⟩ : Fin n).castSucc = U a := hu
  have e0' : v (⟨0, hn⟩ : Fin n).castSucc = W a := hv
  have hr' : IsRailGap M L w κ u v ⟨0, hn⟩ r := hr
  obtain ⟨X, Y, aX, bX, aY, bY, hX⟩ := railGap_dart (lad_ne_u hs hne) (lad_ne_v hs hne) hr'
  obtain ⟨b1, b2, hd⟩ := hs.2.2.2.2 ⟨0, hn⟩
  have hb := hs.2.2.2.1 (⟨0, hn⟩ : Fin n).succ
  have hpq := lad_ne_uv hs (⟨0, hn⟩ : Fin n).succ (⟨0, hn⟩ : Fin n).succ
  have hpp := lad_ne_u hs hne
  have hqq := lad_ne_v hs hne
  rw [e0] at aX b1 hd hpp
  rw [e0'] at aY b2 hd hqq
  obtain ⟨j, r0, hr0, hn0⟩ := rung_pair_gap hMol hdec hc hB a hpp hqq b1 b2 hd hb hpq aX bX aY bY
  exact ⟨j, r0, hr0, by rw [hX]; exact hn0⟩

/-- **Realisation independence of a sub-ladder's gap** (R21 (2)(a)).  If the first rung atom of a ladder `(u, v)` lies in a
ladder `(U, W)`, then the gap of `(u, v)` has the norm of the gap of `(U, W)` (decoration with `c = 0` at degree `4`). -/
theorem subLadder_gap_norm (hMol : M.IsMolecule) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) {m n : ℕ} {U W : Fin (m + 1) → V} {u v : Fin (n + 1) → V}
    (hB : M.IsLadder U W) (hs : M.IsLadder u v) (hmem : u 0 ∈ Molecule.ladderAtoms U W) {R r : Mom d}
    (hR : M.IsLadderGap L w κ U W hB.1 R) (hr : M.IsLadderGap L w κ u v hs.1 r) : ‖r‖ = ‖R‖ := by
  have hM : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => LadderDisjoint.deg_le_four M hMol hx
  have hR' : IsRailGap M L w κ U W ⟨0, hB.1⟩ R := hR
  have hb0 := hs.2.2.2.1 0
  have hne0 : u 0 ≠ v 0 := lad_ne_uv hs 0 0
  unfold Molecule.ladderAtoms at hmem
  rcases Finset.mem_union.mp hmem with h1 | h1
  · obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h1
    have hv0 : v 0 = W a := by
      rw [← ha] at hb0 hne0
      exact LadderDisjoint.sourceLadder_double_partner_eq M hM hB a hne0 hb0
    obtain ⟨j, r0, hr0, hn⟩ := lad_first_rail hMol hdec hc hB hs a ha.symm hv0 hr
    rw [hn]; exact railGap_norm_eq hMol hB hdec hc hr0 hR'
  · obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h1
    have hB' := LadderDisjoint.sourceLadder_swap M hB
    have hv0 : v 0 = U a := by
      rw [← ha] at hb0 hne0
      exact LadderDisjoint.sourceLadder_double_partner_eq M hM hB' a hne0 hb0
    obtain ⟨j, r0, hr0, hn⟩ := lad_first_rail hMol hdec hc hB' hs a ha.symm hv0 hr
    obtain ⟨r1, hr1, hn1⟩ := railGap_swap_exists hB hr0
    rw [hn, ← hn1]; exact railGap_norm_eq hMol hB hdec hc hr1 hR'

end Main


end SubLadder

end WaveTurbulence.VineCount
