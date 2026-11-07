/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseSt
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.CutComponents
/-! **FINALCOUNT-G3: components of `M - v`** (R27, erasure deviation, `Δχ = c - deg v`).

`nbr M v` are the neighbours of `v`; `cmp M v a` the component of `a` in `M - v`; `Cs M v` the set of components of `M - v`
that meet `v`.  `F(M) ≤ F(M - v) ≤ F(M) - 1 + |Cs|` (the components of `M - v` that do not meet `v` are components of `M`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (v : V)

/-- The neighbours of `v`. -/
noncomputable def nbr : Finset V := (M.atoms.erase v).filter (fun a => M.Adj v a)

/-- The component of `a` in `M - v`. -/
noncomputable def cmp (a : V) : Finset V := (M.atoms.erase v).filter (fun b => (eraseAt M v).SameComponent a b)

/-- The components of `M - v` that meet `v`. -/
noncomputable def Cs : Finset (Finset V) := (nbr M v).image (cmp M v)

variable {M v}

theorem mem_cmp {a b : V} : b ∈ cmp M v a ↔ b ∈ M.atoms.erase v ∧ (eraseAt M v).SameComponent a b := by
  unfold cmp; simp

theorem cmp_eq_of_sc {a b : V} (h : (eraseAt M v).SameComponent a b) : cmp M v a = cmp M v b := by
  ext c
  rw [mem_cmp, mem_cmp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Relation.EqvGen.trans _ _ _ h h2⟩

theorem sc_of_cmp_eq {a b : V} (hb : b ∈ M.atoms.erase v) (h : cmp M v a = cmp M v b) :
    (eraseAt M v).SameComponent a b := by
  have : b ∈ cmp M v b := mem_cmp.2 ⟨hb, Relation.EqvGen.refl _⟩
  rw [← h] at this
  exact (mem_cmp.1 this).2

theorem mem_nbr {a : V} : a ∈ nbr M v ↔ a ∈ M.atoms.erase v ∧ M.Adj v a := by
  unfold nbr; simp

theorem exists_nbr (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) (hd : 1 ≤ M.deg v) :
    ∃ a, a ∈ nbr M v := by
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hd
  have hx' : M.atom x = v := by simpa [Molecule.dartsAt] using hx
  refine ⟨M.atom (M.mate x), mem_nbr.2 ⟨Finset.mem_erase.2 ⟨?_, M.atom_mem _⟩, ⟨x, hx', rfl⟩⟩⟩
  intro e; exact hnl x (hx'.trans e.symm)

/-- The collapse of the components of `M - v` onto those of `M`. -/
noncomputable def phiE (M : Molecule V D) (v : V) :
    Quot (fun u w : (eraseAt M v).atoms => (eraseAt M v).Adj u.1 w.1) →
      Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
  Quot.map (fun a : (eraseAt M v).atoms => (⟨a.1, Finset.mem_of_mem_erase a.2⟩ : M.atoms)) (by
    intro a b h
    exact (eraseAt_adj_iff.1 h).1)

theorem numComponents_le_erase (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) (hd : 1 ≤ M.deg v) :
    M.numComponents ≤ (eraseAt M v).numComponents := by
  unfold Molecule.numComponents
  have : Finite (Quot (fun u w : (eraseAt M v).atoms => (eraseAt M v).Adj u.1 w.1)) := inferInstance
  refine Nat.card_le_card_of_surjective (phiE M v) ?_
  intro q
  induction q using Quot.ind with
  | mk a =>
    obtain ⟨a, ha⟩ := a
    by_cases hav : a = v
    · subst hav
      obtain ⟨b, hb⟩ := exists_nbr hnl hv hd
      have hb' := mem_nbr.1 hb
      refine ⟨Quot.mk _ ⟨b, hb'.1⟩, ?_⟩
      show Quot.mk _ (⟨b, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
      rw [quot_mk_eq_iff M _ _ _ ha]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hb'.2)
    · exact ⟨Quot.mk _ ⟨a, Finset.mem_erase.2 ⟨hav, ha⟩⟩, rfl⟩

theorem numComponents_erase_le (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hv : v ∈ M.atoms) :
    (eraseAt M v).numComponents + 1 ≤ M.numComponents + (Cs M v).card := by
  classical
  unfold Molecule.numComponents
  set QE := Quot (fun u w : (eraseAt M v).atoms => (eraseAt M v).Adj u.1 w.1)
  set QM := Quot (fun u w : M.atoms => M.Adj u.1 w.1)
  set p : QM := Quot.mk _ ⟨v, hv⟩
  have : Finite QE := inferInstance
  have : Finite QM := inferInstance
  -- classes mapping away from `[v]` embed into `QM \ {[v]}`
  have h1 : Nat.card {q : QE // phiE M v q ≠ p} + 1 ≤ Nat.card QM := by
    have hinj : Function.Injective (fun q : {q : QE // phiE M v q ≠ p} => phiE M v q.1) := by
      rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      induction q using Quot.ind with
      | mk a =>
      induction q' using Quot.ind with
      | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have hav : a ≠ v := Finset.ne_of_mem_erase ha
      have haM := Finset.mem_of_mem_erase ha
      have hbM := Finset.mem_of_mem_erase hb
      have hq1 : ¬ M.SameComponent a v := fun h' => hq ((quot_mk_eq_iff M _ _ haM hv).2 h')
      have h2 : M.SameComponent a b := (quot_mk_eq_iff M _ _ haM hbM).1 h
      exact Subtype.ext ((quot_mk_eq_iff _ _ _ ha hb).2 (sc_avoid h2 hq1))
    have hle : Nat.card {q : QE // phiE M v q ≠ p} ≤ Nat.card {q : QM // q ≠ p} := by
      refine Nat.card_le_card_of_injective (fun q => ⟨phiE M v q.1, q.2⟩) ?_
      intro q q' h
      exact hinj (congrArg Subtype.val h)
    have e : Nat.card (Option {q : QM // q ≠ p}) = Nat.card QM := Nat.card_congr (Equiv.optionSubtypeNe p)
    have : Finite {q : QM // q ≠ p} := inferInstance
    have h2 : Nat.card (Option {q : QM // q ≠ p}) = Nat.card {q : QM // q ≠ p} + 1 := by simp
    omega
  -- the classes over `[v]` embed into `Cs M v`
  have h2 : Nat.card {q : QE // ¬ (phiE M v q ≠ p)} ≤ (Cs M v).card := by
    let g : {q : QE // ¬ (phiE M v q ≠ p)} → Cs M v := fun q =>
      ⟨Quot.lift (fun a : (eraseAt M v).atoms => cmp M v a.1) (by
        intro a b h
        exact cmp_eq_of_sc (Relation.EqvGen.rel _ _ h)) q.1, by
        obtain ⟨q, hq⟩ := q
        induction q using Quot.ind with
        | mk a =>
          obtain ⟨a, ha⟩ := a
          have hq' : phiE M v (Quot.mk _ ⟨a, ha⟩) = p := not_not.1 hq
          have h3 : M.SameComponent a v :=
            (quot_mk_eq_iff M _ _ (Finset.mem_of_mem_erase ha) hv).1 hq'
          obtain ⟨w, hw, haw⟩ := comp_to_v hnl (Finset.ne_of_mem_erase ha) h3
          have hwM : w ∈ nbr M v := by
            refine mem_nbr.2 ⟨Finset.mem_erase.2 ⟨?_, ?_⟩, hw⟩
            · intro e; subst e
              obtain ⟨z, h1, h2⟩ := hw; exact hnl z (h1.trans h2.symm)
            · obtain ⟨z, h1, h2⟩ := hw; exact h2 ▸ M.atom_mem _
          unfold Cs
          exact Finset.mem_image.2 ⟨w, hwM, cmp_eq_of_sc haw |>.symm⟩⟩
    have hg : Function.Injective g := by
      rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      induction q using Quot.ind with
      | mk a =>
      induction q' using Quot.ind with
      | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have h' : cmp M v a = cmp M v b := congrArg Subtype.val h
      exact Subtype.ext ((quot_mk_eq_iff _ _ _ ha hb).2 (sc_of_cmp_eq hb h'))
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have h3 : Nat.card QE = Nat.card {q : QE // phiE M v q ≠ p} + Nat.card {q : QE // ¬ (phiE M v q ≠ p)} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun q : QE => phiE M v q ≠ p)).symm
  omega

end WaveTurbulence.FinalCountG3
