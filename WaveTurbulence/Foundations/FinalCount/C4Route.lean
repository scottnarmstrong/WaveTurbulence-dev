/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Prop 9.6, case (4): complete (Y)-routes of a regular molecule without cut vertex

For a 4-regular connected molecule `N` without cut vertex (and in/out caps, no loops), every complete (Y)-reduction that
ends in `Q` or `T` uses only (Y2) steps (a (Y1) step needs a chain with `deg a_n + deg b_n ∈ {6, 7}` or two exits to one
atom, the last being a cut vertex). The number of steps is at most the number of pairs with `≥ 3` bonds.
So a route ends in `T` (`YRouteT k N`, `k ≤ #triple pairs`) or in `Q` (`YRouteQ N`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The regularity package preserved by (Y2) steps. -/
structure RegCore (N : Molecule V D) : Prop where
  cap : ∀ a ∈ N.atoms, N.outdeg a ≤ 2 ∧ N.indeg a ≤ 2
  loop : ∀ z, N.atom z ≠ N.atom (N.mate z)
  reg : ∀ a ∈ N.atoms, N.deg a = 4
  conn : ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, N.SameComponent a b
  nocut : ∀ w ∈ N.atoms, ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, a ≠ w → b ≠ w →
    (Degen.eraseAtoms N {w}).SameComponent a b

/-- **A route of complete (Y2) sequences ending in `Q`.** -/
inductive YRouteQ : {V : Type u} → {D : Type v} → [DecidableEq V] → [Fintype D] → [DecidableEq D] →
    Molecule V D → Prop where
  | done {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) :
      IsQ M → YRouteQ M
  | y2 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      YRouteQ (E.toTwoExit hcap).post → YRouteQ M

/-- The pairs of atoms with at least three bonds. -/
noncomputable def tripSet (N : Molecule V D) : Finset (Sym2 V) :=
  ((N.atoms ×ˢ N.atoms).filter fun pq => 3 ≤ N.bondsBetween pq.1 pq.2).image fun pq => s(pq.1, pq.2)

theorem mem_tripSet {N : Molecule V D} {p q : V} (hp : p ∈ N.atoms) (hq : q ∈ N.atoms)
    (h : 3 ≤ N.bondsBetween p q) : s(p, q) ∈ tripSet N :=
  mem_image.mpr ⟨(p, q), mem_filter.mpr ⟨mem_product.mpr ⟨hp, hq⟩, h⟩, rfl⟩

omit [DecidableEq D] in
theorem bb_pos_mem {N : Molecule V D} {p q : V} (h : 1 ≤ N.bondsBetween p q) : p ∈ N.atoms ∧ q ∈ N.atoms := by
  classical
  unfold Molecule.bondsBetween Molecule.bonds at h
  obtain ⟨x, hx⟩ := card_pos.mp h
  simp only [mem_filter, mem_univ, true_and] at hx
  have he : s(N.atom x, N.atom (N.mate x)) = s(p, q) := hx.2
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ N.atom_mem x, h2 ▸ N.atom_mem _⟩
  · exact ⟨h2 ▸ N.atom_mem _, h1 ▸ N.atom_mem x⟩

theorem tripSet_iff {N : Molecule V D} {e : Sym2 V} : e ∈ tripSet N ↔ ∃ p q, e = s(p, q) ∧ 3 ≤ N.bondsBetween p q := by
  constructor
  · intro h
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.mp h
    exact ⟨p, q, rfl, (mem_filter.mp hpq).2⟩
  · rintro ⟨p, q, rfl, h⟩
    have := bb_pos_mem (N := N) (p := p) (q := q) (by omega)
    exact mem_tripSet this.1 this.2 h

theorem toTwoExit_pair {N : Molecule V D} {C : YChain N} (E : Y2End C)
    (hcap : ∀ w ∈ N.atoms, N.outdeg w ≤ 2 ∧ N.indeg w ≤ 2) :
    s((E.toTwoExit hcap).d, (E.toTwoExit hcap).c) = s(N.atom (N.mate E.x), N.atom (N.mate E.y)) := by
  unfold Y2End.toTwoExit
  split_ifs
  · simp [TwoExit.c, TwoExit.d, Sym2.eq_swap]
  · simp [TwoExit.c, TwoExit.d]

/-- The post molecule of a (Y2) sequence loses its first triple pair and creates no new triple pair. -/
theorem tripSet_post_card {N : Molecule V D} {C : YChain N} (E : Y2End C)
    (hcap : ∀ w ∈ N.atoms, N.outdeg w ≤ 2 ∧ N.indeg w ≤ 2)
    (hcomp : N.bondsBetween (N.atom (N.mate E.x)) (N.atom (N.mate E.y)) ≠ 2) :
    (tripSet (E.toTwoExit hcap).post).card + 1 ≤ (tripSet N).card := by
  classical
  set T := E.toTwoExit hcap with hT
  have hY : T.Y = C.set := E.toTwoExit_Y hcap
  have hpair : s(T.d, T.c) = s(N.atom (N.mate E.x), N.atom (N.mate E.y)) := toTwoExit_pair E hcap
  have ha0 : C.a 0 ∈ C.set := C.a_mem (Nat.zero_le _)
  have hb0 : C.b 0 ∈ C.set := C.b_mem (Nat.zero_le _)
  have hmem : s(C.a 0, C.b 0) ∈ tripSet N :=
    mem_tripSet (C.mem 0 (Nat.zero_le _)).1 (C.mem 0 (Nat.zero_le _)).2 (by rw [C.triple])
  have hsub : tripSet T.post ⊆ (tripSet N).erase s(C.a 0, C.b 0) := by
    intro e he
    obtain ⟨p, q, rfl, h3⟩ := tripSet_iff.mp he
    have hpq := bb_pos_mem (N := T.post) (p := p) (q := q) (by omega)
    have hpA := hpq.1; have hqA := hpq.2
    rw [T.post_atoms] at hpA hqA
    obtain ⟨hpN, hpY⟩ := mem_sdiff.mp hpA
    obtain ⟨hqN, hqY⟩ := mem_sdiff.mp hqA
    have hbb : T.post.bondsBetween p q =
        N.bondsBetween p q + (if s(T.d, T.c) = s(p, q) then 1 else 0) := by
      change (Mole.addBond (Degen.eraseAtoms N T.Y) T.d T.c).bondsBetween p q = _
      rw [addBond_bondsBetween, Degen.bondsBetween_erase_eq N T.Y hpY hqY]
    refine mem_erase.mpr ⟨?_, ?_⟩
    · intro hEq
      rcases Sym2.eq_iff.mp hEq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hpY (by rw [hY, h1]; exact ha0)
      · exact hpY (by rw [hY, h1]; exact hb0)
    · by_cases hdc : s(T.d, T.c) = s(p, q)
      · rw [hbb, if_pos hdc] at h3
        have hne : N.bondsBetween p q ≠ 2 := by
          intro h2
          apply hcomp
          rw [hpair] at hdc
          rcases Sym2.eq_iff.mp hdc with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
          · rw [h1, h2']; exact h2
          · rw [h1, h2', Degen.bondsBetween_comm]; exact h2
        exact tripSet_iff.mpr ⟨p, q, rfl, by omega⟩
      · rw [hbb, if_neg hdc] at h3
        exact tripSet_iff.mpr ⟨p, q, rfl, h3⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hmem] at this
  have hpos : 0 < (tripSet N).card := card_pos.mpr ⟨_, hmem⟩
  omega

/-- The post molecule of a (Y2) sequence of a regular molecule is regular without cut vertex. -/
theorem RegCore.post {N : Molecule V D} (hR : RegCore N) {C : YChain N} (E : Y2End C) :
    RegCore (E.toTwoExit hR.cap).post := by
  obtain ⟨h1, h2, h3, h4⟩ := E.post_props hR.cap hR.loop hR.reg hR.conn
  exact ⟨h1, h2, h3, h4, (E.toTwoExit hR.cap).post_noCut hR.nocut⟩

/-- A (Y1) case 3 ending is impossible in a regular molecule without cut vertex. -/
theorem RegCore.not_y1_end3 {N : Molecule V D} (hR : RegCore N) {C : YChain N} (E : Y1End3 C) : False := by
  classical
  set S := C.set with hS
  set w := N.atom (N.mate E.x) with hw
  have hwS : w ∉ S := E.hxo
  have hwA : w ∈ N.atoms := N.atom_mem _
  have hcross := E.cross_eq
  have hcr : ∀ z, N.atom z ∈ S → N.atom (N.mate z) ∉ S → N.atom (N.mate z) = w := by
    intro z h1 h2
    have hz : z ∈ crossDarts N S := mem_crossDarts.mpr ⟨h1, h2⟩
    rw [hcross] at hz
    rcases mem_insert.mp hz with rfl | hz
    · rfl
    · rw [mem_singleton.mp hz]; exact E.same.symm
  have hb : ∃ b ∈ N.atoms, b ∉ S ∧ b ≠ w := by
    by_contra hno
    push Not at hno
    have hcard : (N.dartsAt w).card ≤ ({E.x, E.y} : Finset D).card := by
      refine card_le_card_of_injOn N.mate (fun z hz => ?_) (fun a _ b _ h => Mole.mate_injective N h)
      have hza : N.atom z = w := by simpa [Molecule.dartsAt] using hz
      have hne : N.atom (N.mate z) ≠ w := fun h => hR.loop z (hza.trans h.symm)
      have hmS : N.atom (N.mate z) ∈ S := by
        by_contra hn; exact hne (hno _ (N.atom_mem _) hn)
      have hz2 : N.mate z ∈ crossDarts N S :=
        mem_crossDarts.mpr ⟨hmS, by rw [N.mate_mate, hza]; exact hwS⟩
      rwa [hcross] at hz2
    have h4 := hR.reg w hwA
    have h2 : ({E.x, E.y} : Finset D).card ≤ 2 := card_le_two
    unfold Molecule.deg at h4
    omega
  obtain ⟨b, hbA, hbS, hbw⟩ := hb
  have ha0 : C.a 0 ∈ S := C.a_mem (Nat.zero_le _)
  have haA : C.a 0 ∈ N.atoms := (C.mem 0 (Nat.zero_le _)).1
  have hconn := hR.nocut w hwA (C.a 0) haA b hbA (fun h => hwS (h ▸ ha0)) hbw
  have key : ∀ u v, (Degen.eraseAtoms N {w}).SameComponent u v → (u ∈ S ↔ v ∈ S) := by
    intro u v h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      have p1 : N.atom z.val ≠ w := fun h => z.property.1 (by rw [h]; exact mem_singleton_self w)
      have p2 : N.atom (N.mate z.val) ≠ w := fun h => z.property.2 (by rw [h]; exact mem_singleton_self w)
      change N.atom z.val ∈ S ↔ N.atom (N.mate z.val) ∈ S
      constructor
      · intro h1
        by_contra h2
        exact p2 (hcr z.val h1 h2)
      · intro h2
        by_contra h1
        have := hcr (N.mate z.val) h2 (by rwa [N.mate_mate])
        rw [N.mate_mate] at this
        exact p1 this
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact hbS ((key _ _ hconn).mp ha0)

/-- **No (Y1) step in a regular molecule without cut vertex.** -/
theorem RegCore.not_y1 {N : Molecule V D} (hR : RegCore N) (C : YChain N) :
    ¬ (N.deg (C.a C.n) + N.deg (C.b C.n) = 6 ∨ Nonempty (Y1End2 C) ∨ Nonempty (Y1End3 C)) := by
  have da := hR.reg _ (C.mem C.n le_rfl).1
  have db := hR.reg _ (C.mem C.n le_rfl).2
  rintro (h | h | h)
  · omega
  · obtain ⟨E⟩ := h
    have := E.hdeg; omega
  · obtain ⟨E⟩ := h
    exact hR.not_y1_end3 E

/-- **Route dichotomy.** A regular molecule without cut vertex that (Y)-reduces to `Q` or `T`, with at most `j` triple
pairs, either has a `T`-route of at most `j` sequences or a `Q`-route. -/
theorem reach_cases : ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D},
    YReachesQT N → ∀ (j : ℕ), RegCore N → (tripSet N).card ≤ j →
      (∃ k ≤ j, YRouteT k N) ∨ YRouteQ N := by
  intro V D _ _ _ N hN
  induction hN with
  | done M h3 hQT =>
    intro j hR _
    rcases hQT with hQ | hT
    · exact Or.inr (YRouteQ.done M hQ)
    · exact Or.inl ⟨0, Nat.zero_le _, YRouteT.done M hT⟩
  | y2 M hcap C E hcomp _ ih =>
    intro j hR hj
    have hcard := tripSet_post_card E hcap hcomp
    rcases ih (j - 1) (hR.post E) (by omega) with ⟨k, hk, hrt⟩ | hq
    · exact Or.inl ⟨k + 1, by omega, YRouteT.y2 k M hcap C E hcomp hrt⟩
    · exact Or.inr (YRouteQ.y2 M hcap C E hcomp hq)
  | y1 M C h _ _ =>
    intro j hR _
    exact absurd h (hR.not_y1 C)

end

end WaveTurbulence.FinalCountG8
