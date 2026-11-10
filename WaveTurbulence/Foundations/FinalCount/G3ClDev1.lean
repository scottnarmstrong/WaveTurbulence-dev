/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5a
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
/-! **FINALCOUNT-G3 (R29 item 4, step 4): components of `M - K`** for a cluster `K` (set version of `G3EraseDev1`).

`nbrS M K` are the atoms outside `K` adjacent to `K`; `cmpS M K a` the component of `a` in `M - K`; `CsS M K` the set of components of
`M - K` that meet `nbrS` (equivalently, are adjacent to `K`).  For nonempty `K` inside one component of `M`:
`F(M - K) + 1 ≤ F(M) + |CsS|`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Finset V)

/-- The atoms outside `K` adjacent to `K`. -/
noncomputable def nbrS : Finset V := (M.atoms \ K).filter (fun a => ∃ k ∈ K, M.Adj k a)

/-- The component of `a` in `M - K`. -/
noncomputable def cmpS (a : V) : Finset V := (M.atoms \ K).filter (fun b => (eraseSet M K).SameComponent a b)

/-- The components of `M - K` adjacent to `K`. -/
noncomputable def CsS : Finset (Finset V) := (nbrS M K).image (cmpS M K)

variable {M K}

theorem mem_cmpS {a b : V} : b ∈ cmpS M K a ↔ b ∈ M.atoms \ K ∧ (eraseSet M K).SameComponent a b := by
  unfold cmpS; simp

theorem cmpS_eq_of_sc {a b : V} (h : (eraseSet M K).SameComponent a b) : cmpS M K a = cmpS M K b := by
  ext c
  rw [mem_cmpS, mem_cmpS]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Relation.EqvGen.trans _ _ _ h h2⟩

theorem sc_of_cmpS_eq {a b : V} (hb : b ∈ M.atoms \ K) (h : cmpS M K a = cmpS M K b) :
    (eraseSet M K).SameComponent a b := by
  have : b ∈ cmpS M K b := mem_cmpS.2 ⟨hb, Relation.EqvGen.refl _⟩
  rw [← h] at this
  exact (mem_cmpS.1 this).2

theorem mem_nbrS {a : V} : a ∈ nbrS M K ↔ a ∈ M.atoms \ K ∧ ∃ k ∈ K, M.Adj k a := by
  unfold nbrS; simp

theorem eraseSet_adj_iff {a b : V} : (eraseSet M K).Adj a b ↔ M.Adj a b ∧ a ∉ K ∧ b ∉ K := by
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x.1, h1, h2⟩, h1 ▸ x.2.1, h2 ▸ x.2.2⟩
  · rintro ⟨⟨z, h1, h2⟩, ha, hb⟩
    exact ⟨⟨z, h1 ▸ ha, h2 ▸ hb⟩, h1, h2⟩

theorem adjS_symm {a b : V} (h : M.Adj a b) : M.Adj b a := by
  obtain ⟨z, h1, h2⟩ := h
  exact ⟨M.mate z, h2, by rw [M.mate_mate]; exact h1⟩

theorem scS_avoid {a b : V} (h : M.SameComponent a b) :
    (¬ ∃ k ∈ K, M.SameComponent a k) → (eraseSet M K).SameComponent a b := by
  induction h with
  | rel x y hr =>
    intro hx
    have hxv : x ∉ K := fun e => hx ⟨x, e, Relation.EqvGen.refl _⟩
    have hyv : y ∉ K := fun e => hx ⟨y, e, Relation.EqvGen.rel _ _ hr⟩
    exact Relation.EqvGen.rel _ _ (eraseSet_adj_iff.2 ⟨hr, hxv, hyv⟩)
  | refl x => exact fun _ => Relation.EqvGen.refl _
  | symm x y hxy ih =>
    intro hy
    have hx : ¬ ∃ k ∈ K, M.SameComponent x k := by
      rintro ⟨k, hk, h'⟩
      exact hy ⟨k, hk, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) h'⟩
    exact Relation.EqvGen.symm _ _ (ih hx)
  | trans x y z hxy hyz ih1 ih2 =>
    intro hx
    have hy : ¬ ∃ k ∈ K, M.SameComponent y k := by
      rintro ⟨k, hk, h'⟩
      exact hx ⟨k, hk, Relation.EqvGen.trans _ _ _ hxy h'⟩
    exact Relation.EqvGen.trans _ _ _ (ih1 hx) (ih2 hy)

/-- An atom outside `K` in the component of an atom of `K` reaches a neighbour of `K` in `M - K`. -/
theorem comp_to_K {a k : V} (ha : a ∉ K) (hk : k ∈ K) (h : M.SameComponent a k) :
    ∃ w, w ∉ K ∧ (∃ k' ∈ K, M.Adj k' w) ∧ (eraseSet M K).SameComponent a w := by
  let S : V → Prop := fun x => ∃ w, w ∉ K ∧ (∃ k' ∈ K, M.Adj k' w) ∧ (eraseSet M K).SameComponent x w
  let Rr : V → Prop := fun x => x ∈ K ∨ S x
  have dir : ∀ x y, M.Adj x y → Rr x → Rr y := by
    intro x y hxy hx
    by_cases hxv : x ∈ K
    · by_cases hyv : y ∈ K
      · exact Or.inl hyv
      · exact Or.inr ⟨y, hyv, ⟨x, hxv, hxy⟩, Relation.EqvGen.refl _⟩
    · by_cases hyv : y ∈ K
      · exact Or.inl hyv
      · rcases hx with hx | ⟨w, hwK, hw, hxw⟩
        · exact absurd hx hxv
        · exact Or.inr ⟨w, hwK, hw, Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (eraseSet_adj_iff.2 ⟨hxy, hxv, hyv⟩))) hxw⟩
  have iff' : ∀ x y, M.SameComponent x y → (Rr x ↔ Rr y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact ⟨dir x y hr, dir y x (adjS_symm hr)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  have := (iff' a k h).2 (Or.inl hk)
  rcases this with h1 | h1
  · exact absurd h1 ha
  · exact h1

/-- `F(M - K) + 1 ≤ F(M) + |CsS|` for nonempty `K` inside one component of `M`. -/
theorem numComponents_eraseSet_le (hK : K ⊆ M.atoms) {k₀ : V} (hk₀ : k₀ ∈ K)
    (hKc : ∀ k ∈ K, M.SameComponent k k₀) :
    (eraseSet M K).numComponents + 1 ≤ M.numComponents + (CsS M K).card := by
  classical
  unfold Molecule.numComponents
  set QE := Quot (fun u w : (eraseSet M K).atoms => (eraseSet M K).Adj u.1 w.1)
  set QM := Quot (fun u w : M.atoms => M.Adj u.1 w.1)
  have hv : k₀ ∈ M.atoms := hK hk₀
  set p : QM := Quot.mk _ ⟨k₀, hv⟩
  have hsub : ∀ {a : V}, a ∈ (eraseSet M K).atoms → a ∈ M.atoms := fun {a} ha => (Finset.mem_sdiff.1 ha).1
  let phi : QE → QM := Quot.map (fun a : (eraseSet M K).atoms => (⟨a.1, hsub a.2⟩ : M.atoms)) (by
    intro a b h
    exact (eraseSet_adj_iff.1 h).1)
  have : Finite QE := inferInstance
  have : Finite QM := inferInstance
  have h1 : Nat.card {q : QE // phi q ≠ p} + 1 ≤ Nat.card QM := by
    have hinj : Function.Injective (fun q : {q : QE // phi q ≠ p} => phi q.1) := by
      rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      induction q using Quot.ind with
      | mk a =>
      induction q' using Quot.ind with
      | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have haM := hsub ha
      have hbM := hsub hb
      have hq1 : ¬ ∃ k ∈ K, M.SameComponent a k := by
        rintro ⟨k, hk, hs⟩
        exact hq ((quot_mk_eq_iff M _ _ haM hv).2
          (Relation.EqvGen.trans _ _ _ hs (hKc k hk)))
      have h2 : M.SameComponent a b := (quot_mk_eq_iff M _ _ haM hbM).1 h
      exact Subtype.ext ((quot_mk_eq_iff _ _ _ ha hb).2 (scS_avoid h2 hq1))
    have hle : Nat.card {q : QE // phi q ≠ p} ≤ Nat.card {q : QM // q ≠ p} := by
      refine Nat.card_le_card_of_injective (fun q => ⟨phi q.1, q.2⟩) ?_
      intro q q' h
      exact hinj (congrArg Subtype.val h)
    have e : Nat.card (Option {q : QM // q ≠ p}) = Nat.card QM := Nat.card_congr (Equiv.optionSubtypeNe p)
    have : Finite {q : QM // q ≠ p} := inferInstance
    have h2 : Nat.card (Option {q : QM // q ≠ p}) = Nat.card {q : QM // q ≠ p} + 1 := by simp
    omega
  have h2 : Nat.card {q : QE // ¬ (phi q ≠ p)} ≤ (CsS M K).card := by
    let g : {q : QE // ¬ (phi q ≠ p)} → CsS M K := fun q =>
      ⟨Quot.lift (fun a : (eraseSet M K).atoms => cmpS M K a.1) (by
        intro a b h
        exact cmpS_eq_of_sc (Relation.EqvGen.rel _ _ h)) q.1, by
        obtain ⟨q, hq⟩ := q
        induction q using Quot.ind with
        | mk a =>
          obtain ⟨a, ha⟩ := a
          have hq' : phi (Quot.mk _ ⟨a, ha⟩) = p := not_not.1 hq
          have h3 : M.SameComponent a k₀ :=
            (quot_mk_eq_iff M _ _ (hsub ha) hv).1 hq'
          obtain ⟨w, hwK, hw, haw⟩ := comp_to_K (Finset.mem_sdiff.1 ha).2 hk₀ h3
          have hwM : w ∈ nbrS M K := by
            refine mem_nbrS.2 ⟨Finset.mem_sdiff.2 ⟨?_, hwK⟩, hw⟩
            obtain ⟨k', _, z, h1, h2⟩ := hw
            exact h2 ▸ M.atom_mem _
          unfold CsS
          exact Finset.mem_image.2 ⟨w, hwM, (cmpS_eq_of_sc haw).symm⟩⟩
    have hg : Function.Injective g := by
      rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      induction q using Quot.ind with
      | mk a =>
      induction q' using Quot.ind with
      | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have h' : cmpS M K a = cmpS M K b := congrArg Subtype.val h
      exact Subtype.ext ((quot_mk_eq_iff _ _ _ ha hb).2 (sc_of_cmpS_eq hb h'))
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have h3 : Nat.card QE = Nat.card {q : QE // phi q ≠ p} + Nat.card {q : QE // ¬ (phi q ≠ p)} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun q : QE => phi q ≠ p)).symm
  omega

end WaveTurbulence.FinalCountG3
