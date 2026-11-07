/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL17
public import WaveTurbulence.Foundations.FinalCount.GL1
/-! **G3-LOWDEG (R48), part 18: the loop start.**  `SubHypLoop R M` is the standing hypothesis of a garden molecule `M` that may
have self-loops (DH23's `SubHyp` minus `deg3`, minus `noloop`); `SubHypLoop.unloop` gives `SubHypL (R + k) M.unloop` with
`k = M.loopBonds.card` (`R ↦ R + k`: the index counts `2 n - E` and the loop bonds are removed), provided every atom keeps a
non-loop dart (true when `M` has `≥ 2` atoms and is connected; the one-atom molecules are Examples A, B and are handled by
`countA_dartless_le_one`).  Also the transports of the scalar hypotheses `h0` and `hκ`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The standing hypotheses on a garden molecule `M` allowing self-loops. -/
structure SubHypLoop (R : ℕ) (M : Molecule V D) : Prop where
  bounds : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2
  count : M.bonds.card + R = 2 * M.atoms.card
  conn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  one_le : 1 ≤ R
  /-- every atom keeps a non-loop dart (automatic for `≥ 2` atoms, see `SubHypLoop.nonloop_of_two_le`) -/
  nonloop : ∀ a ∈ M.atoms, ∃ x, M.atom x = a ∧ M.atom (M.mate x) ≠ a

theorem sameComponent_unloop (M : Molecule V D) {a b : V} (h : M.SameComponent a b) : M.unloop.SameComponent a b := by
  unfold Molecule.SameComponent at *
  induction h with
  | rel a b h =>
    rcases adj_unloop_or M h with e | h'
    · rw [e]; exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h'
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem unloop_outdeg_le (M : Molecule V D) (a : V) : M.unloop.outdeg a ≤ M.outdeg a := by
  unfold Molecule.outdeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun x _ y _ e => Subtype.ext e)
  have := Finset.mem_filter.1 hx
  exact Finset.mem_filter.2 ⟨(mem_dartsAt' M a x.1).2 ((mem_dartsAt' M.unloop a x).1 this.1), this.2⟩

theorem unloop_indeg_le (M : Molecule V D) (a : V) : M.unloop.indeg a ≤ M.indeg a := by
  unfold Molecule.indeg
  refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun x _ y _ e => Subtype.ext e)
  have := Finset.mem_filter.1 hx
  exact Finset.mem_filter.2 ⟨(mem_dartsAt' M a x.1).2 ((mem_dartsAt' M.unloop a x).1 this.1), this.2⟩

/-- **The loop start**: `M.unloop` satisfies `SubHypL (R + k)`. -/
theorem SubHypLoop.unloop {R : ℕ} {M : Molecule V D} (h : SubHypLoop R M) :
    SubHypL (R + M.loopBonds.card) M.unloop where
  bounds := fun a ha => ⟨(unloop_outdeg_le M a).trans (h.bounds a ha).1, (unloop_indeg_le M a).trans (h.bounds a ha).2⟩
  count := by have := unloop_bonds_card M; have := h.count; rw [unloop_atoms]; omega
  noloop := fun x => x.2
  conn := fun a ha b hb => sameComponent_unloop M (h.conn a ha b hb)
  one_le := by have := h.one_le; omega
  deg_pos := fun a ha => by
    obtain ⟨x, hx, hx'⟩ := h.nonloop a ha
    unfold Molecule.deg
    exact Finset.card_pos.2 ⟨⟨x, by rw [hx]; exact fun e => hx' e.symm⟩, (mem_dartsAt' M.unloop a _).2 hx⟩

/-- Every atom of a connected molecule with `≥ 2` atoms has a non-loop dart. -/
theorem nonloop_of_two_le {M : Molecule V D} (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (h2 : 2 ≤ M.atoms.card) : ∀ a ∈ M.atoms, ∃ x, M.atom x = a ∧ M.atom (M.mate x) ≠ a := by
  intro a ha
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ M.atoms, b ≠ a := by
    by_contra hcon; push Not at hcon
    have : M.atoms ⊆ {a} := fun b hb => by simpa using hcon b hb
    have := Finset.card_le_card this; simp at this; omega
  by_contra hno
  push Not at hno
  -- every dart at `a` is a loop, so `a` is related only to itself
  have key : ∀ u v : V, Relation.EqvGen M.Adj u v → (u = a ↔ v = a) := by
    intro u v huv
    induction huv with
    | rel u v h =>
      obtain ⟨x, hx, hx'⟩ := h
      constructor
      · intro hu; rw [← hx'] ; exact (hno x (hx.trans hu)) ▸ rfl
      · intro hv
        have := hno (M.mate x) (hx'.trans hv)
        rw [M.mate_mate] at this
        rw [← hx]; exact this
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  exact hba ((key a b (hconn a ha b hb)).1 rfl)

theorem sum_unloop_kvec (M : Molecule V D) {L : ℝ} {w : Mom d} {κ : D → Fin d → ℤ} (hκ : ∀ x, κ (M.mate x) = κ x) (v : V) :
    ∑ x ∈ M.unloop.dartsAt v, M.unloop.dartSign x • Molecule.kvec L w (fun y : NonLoop M => κ y.1) x =
      ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x := by
  symm
  rw [sum_dartsAt_unloop M v (fun x => M.dartSign x • Molecule.kvec L w κ x) ?_]
  · rfl
  · intro x _
    show M.dartSign (M.mate x) • Molecule.kvec L w κ (M.mate x) + M.dartSign x • Molecule.kvec L w κ x = 0
    simp only [Molecule.kvec, dartSign_mateL, hκ x]; simp only [neg_smul, smul_add]; abel

/-- The degree-`4` conservation `h0` transports to `M.unloop`. -/
theorem h0_unloop {R : ℕ} {M : Molecule V D} (hS : SubHypLoop R M) {L : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}
    (hκ : ∀ x, κ (M.mate x) = κ x)
    (h0 : ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 →
      ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x • Molecule.kvec L w (fun y : NonLoop M => κ y.1) x = 0 := by
  intro a ha h4
  rw [sum_unloop_kvec M hκ a]
  exact h0 a ha (le_antisymm (deg_le_four M (hS.bounds a ha)) (h4 ▸ unloop_deg_le M a))

/-- A one-atom molecule all of whose darts are loops (Examples A, B) has a dartless `unloop`. -/
theorem unloop_isEmpty_of_allLoops (M : Molecule V D) (h : ∀ x, M.atom x = M.atom (M.mate x)) : IsEmpty (NonLoop M) :=
  ⟨fun x => x.2 (h x.1)⟩

end WaveTurbulence.FinalCountG3
