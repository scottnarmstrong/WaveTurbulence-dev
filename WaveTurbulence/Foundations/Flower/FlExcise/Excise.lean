/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-!
# FL-EXCISE: supplement Lemma 7.4 (graph bookkeeping for excision)

On main's half-edge `Molecule`: deleting an atom set `S` (with all incident bonds) from a molecule
with maximum degree at most four. With `e_S` the bonds inside `S`, `q` the bonds crossing from `S` to its
complement (counted by their dart at `S`) and `D_S = ∑_{x ∈ S} (4 - deg x)`:
`2 v' - e' = R + (q - D_S)/2` (`R = 2v - e`), at most `c + q` components, at most `q` boundary atoms.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Flower.FlExcise

open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The molecule obtained by deleting the atoms `S` and all their incident bonds. -/
def delete (S : Finset V) : Molecule V {x : D // M.atom x ∉ S ∧ M.atom (M.mate x) ∉ S} where
  atoms := M.atoms \ S
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, by
    rw [M.mate_mate]; exact ⟨x.2.2, x.2.1⟩⟩
  out := fun x => M.out x.1
  atom_mem := fun x => Finset.mem_sdiff.2 ⟨M.atom_mem _, x.2.1⟩
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

/-- `q`: the bonds crossing from `S` to its complement, counted by their dart at `S`. -/
def crossCount (S : Finset V) : ℕ :=
  (Finset.univ.filter fun x : D => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S).card

/-- `e_S`: the bonds with both ends in `S`. -/
def innerBonds (S : Finset V) : ℕ :=
  (M.bonds.filter fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S).card

/-- `D_S = ∑_{x ∈ S} (4 - deg x)`. -/
def defect (S : Finset V) : ℕ := ∑ x ∈ S, (4 - M.deg x)

/-- The remaining atoms incident to a deleted bond. -/
def boundaryAtoms (S : Finset V) : Finset V :=
  (M.atoms \ S).filter fun u => ∃ x : D, M.atom x = u ∧ M.atom (M.mate x) ∈ S

private lemma card_split {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    s.card = (s.filter p).card + (s.filter fun x => ¬ p x).card :=
  (Finset.card_filter_add_card_filter_not p).symm

private lemma card_sym (P : D → Prop) [DecidablePred P] (hP : ∀ x, P (M.mate x) ↔ P x) :
    (Finset.univ.filter P).card = 2 * (Finset.univ.filter fun x => M.out x = true ∧ P x).card := by
  have h1 := card_split (Finset.univ.filter P) (fun x => M.out x = true)
  rw [Finset.filter_filter, Finset.filter_filter] at h1
  have h2 : (Finset.univ.filter fun x => P x ∧ ¬ M.out x = true).card =
      (Finset.univ.filter fun x => M.out x = true ∧ P x).card := by
    refine Finset.card_nbij' M.mate M.mate ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨?_, (hP x).2 hx.1⟩
      have := M.out_mate x
      cases h : M.out x <;> simp_all
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨?_, ?_⟩
      · exact (hP x).2 hx.2
      · have := M.out_mate x
        simp_all
    · intro x _; exact M.mate_mate x
    · intro x _; exact M.mate_mate x
  rw [h1, h2]
  have : (Finset.univ.filter fun x => P x ∧ M.out x = true).card =
      (Finset.univ.filter fun x => M.out x = true ∧ P x).card := by
    congr 1; ext x; simp [and_comm]
  rw [this]; ring


/-- The bonds of `delete M S` are the bonds of `M` with no end in `S`. -/
lemma delete_bonds_card (S : Finset V) :
    (delete M S).bonds.card =
      (Finset.univ.filter fun x : D => M.out x = true ∧ (M.atom x ∉ S ∧ M.atom (M.mate x) ∉ S)).card := by
  classical
  unfold Molecule.bonds
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

/-- Crossing darts at the complement are as many as crossing darts at `S`. -/
lemma card_cross_swap (S : Finset V) :
    (Finset.univ.filter fun x : D => M.atom x ∉ S ∧ M.atom (M.mate x) ∈ S).card = crossCount M S := by
  unfold crossCount
  refine Finset.card_nbij' M.mate M.mate ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, M.mate_mate] at hx ⊢
    exact ⟨hx.2, hx.1⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, M.mate_mate] at hx ⊢
    exact ⟨hx.2, hx.1⟩
  · intro x _; exact M.mate_mate x
  · intro x _; exact M.mate_mate x

/-- The degree identity `2 e_S + q = ∑_{x ∈ S} deg x`. -/
lemma degree_sum (S : Finset V) :
    ∑ x ∈ S, M.deg x = 2 * innerBonds M S + crossCount M S := by
  have h1 : ∑ x ∈ S, M.deg x = (Finset.univ.filter fun y : D => M.atom y ∈ S).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := M.atom) (t := S)
      (fun y hy => by simpa using hy)]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold Molecule.deg Molecule.dartsAt
    congr 1; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => ⟨h ▸ hu, h⟩
    · exact fun h => h.2
  rw [h1, card_split _ (fun y : D => M.atom (M.mate y) ∈ S), Finset.filter_filter, Finset.filter_filter]
  unfold innerBonds crossCount Molecule.bonds
  have := card_sym M (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S)
    (fun x => by simp [M.mate_mate, and_comm])
  rw [Finset.filter_filter, ← this]

/-- Bond partition: `e = e_S + q + e'`. -/
lemma bond_partition (S : Finset V) :
    M.bonds.card = innerBonds M S + crossCount M S + (delete M S).bonds.card := by
  have hall := card_sym M (fun _ => True) (fun _ => Iff.rfl)
  have hall' : Fintype.card D = 2 * M.bonds.card := by
    simpa [Molecule.bonds] using hall
  have hin := card_sym M (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S)
    (fun x => by simp [M.mate_mate, and_comm])
  have hout := card_sym M (fun x => M.atom x ∉ S ∧ M.atom (M.mate x) ∉ S)
    (fun x => by simp [M.mate_mate, and_comm])
  have hsw := card_cross_swap M S
  rw [← delete_bonds_card] at hout
  have hs1 := card_split (Finset.univ : Finset D) (fun y : D => M.atom y ∈ S)
  rw [card_split (Finset.univ.filter fun y : D => M.atom y ∈ S) (fun y : D => M.atom (M.mate y) ∈ S),
    card_split (Finset.univ.filter fun y : D => ¬ M.atom y ∈ S) (fun y : D => M.atom (M.mate y) ∈ S),
    Finset.filter_filter, Finset.filter_filter, Finset.filter_filter, Finset.filter_filter] at hs1
  rw [Finset.card_univ] at hs1
  unfold innerBonds
  unfold Molecule.bonds at *
  rw [Finset.filter_filter]
  unfold crossCount at *
  omega

/-- Crossing count bounded by the degree sum: `q ≤ ∑_{x ∈ S} deg x`. -/
lemma crossCount_le (S : Finset V) : crossCount M S ≤ ∑ x ∈ S, M.deg x := by
  rw [degree_sum]; omega

/-- **Lemma 7.4, bond identity.** `2 v' - e' = R + (q - D_S)/2`, in the form
`2 (2 v' - e') = 2 (2 v - e) + q - D_S`, together with `v' = v - |S|`. -/
theorem excise_identity {S : Finset V} (hS : S ⊆ M.atoms) (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4) :
    (delete M S).atoms.card = M.atoms.card - S.card ∧
    (delete M S).bonds.card = M.bonds.card - innerBonds M S - crossCount M S ∧
    2 * (2 * ((delete M S).atoms.card : ℤ) - (delete M S).bonds.card) =
      2 * (2 * (M.atoms.card : ℤ) - M.bonds.card) + crossCount M S - defect M S := by
  have hv : (delete M S).atoms.card = M.atoms.card - S.card := by
    change (M.atoms \ S).card = _
    exact Finset.card_sdiff_of_subset hS
  have hp := bond_partition M S
  have hd := degree_sum M S
  have hD : ∑ x ∈ S, M.deg x + defect M S = 4 * S.card := by
    unfold defect
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => 4) fun x hx => by
      have := hdeg x (hS hx); omega]
    simp [mul_comm]
  have hle : S.card ≤ M.atoms.card := Finset.card_le_card hS
  refine ⟨hv, by omega, ?_⟩
  rw [hv]
  have : ((M.atoms.card - S.card : ℕ) : ℤ) = M.atoms.card - S.card := by omega
  rw [this]
  have hp' : (M.bonds.card : ℤ) = innerBonds M S + crossCount M S + (delete M S).bonds.card := by
    exact_mod_cast hp
  have hd' : (2 * innerBonds M S + crossCount M S : ℤ) + defect M S = 4 * S.card := by
    exact_mod_cast (by omega : 2 * innerBonds M S + crossCount M S + defect M S = 4 * S.card)
  linarith

/-- The same, with the rational form `2 v' - e' = R + (q - D_S) / 2`. -/
theorem excise_identity_rat {S : Finset V} (hS : S ⊆ M.atoms) (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4) :
    2 * ((delete M S).atoms.card : ℚ) - (delete M S).bonds.card =
      (2 * (M.atoms.card : ℚ) - M.bonds.card) + ((crossCount M S : ℚ) - defect M S) / 2 := by
  have h := (excise_identity M hS hdeg).2.2
  have h' : (2 * (2 * ((delete M S).atoms.card : ℚ) - (delete M S).bonds.card)) =
      2 * (2 * (M.atoms.card : ℚ) - M.bonds.card) + crossCount M S - defect M S := by
    exact_mod_cast h
  linarith

/-- `q ≤ 4 |S|` (degrees at most four). -/
theorem crossCount_le_four {S : Finset V} (hS : S ⊆ M.atoms) (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4) :
    crossCount M S ≤ 4 * S.card := by
  calc crossCount M S ≤ ∑ x ∈ S, M.deg x := crossCount_le M S
    _ ≤ ∑ _x ∈ S, 4 := Finset.sum_le_sum fun x hx => hdeg x (hS hx)
    _ = 4 * S.card := by simp [mul_comm]

/-- At most `q` remaining atoms are incident to a deleted bond. -/
theorem boundaryAtoms_card_le (S : Finset V) : (boundaryAtoms M S).card ≤ crossCount M S := by
  classical
  unfold boundaryAtoms crossCount
  calc _ ≤ ((Finset.univ.filter fun x : D => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S).image fun y => M.atom (M.mate y)).card := by
        apply Finset.card_le_card
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_sdiff] at hu
        obtain ⟨⟨_, hu2⟩, x, rfl, hx⟩ := hu
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨M.mate x, ⟨by simpa using hx, by simpa [M.mate_mate] using hu2⟩, by simp [M.mate_mate]⟩
    _ ≤ _ := Finset.card_image_le

/-- Component relation of the deleted molecule on its atoms. -/
private lemma adj_delete {S : Finset V} {a b : V} :
    (delete M S).Adj a b ↔ ∃ x : D, M.atom x = a ∧ M.atom (M.mate x) = b ∧ a ∉ S ∧ b ∉ S := by
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨x.1, h1, h2, h1 ▸ x.2.1, h2 ▸ x.2.2⟩
  · rintro ⟨x, h1, h2, ha, hb⟩
    exact ⟨⟨x, h1 ▸ ha, h2 ▸ hb⟩, h1, h2⟩

private lemma adj_symm {a b : V} (h : M.Adj a b) : M.Adj b a := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨M.mate x, h2, by rw [M.mate_mate]; exact h1⟩

/-- Classes with no boundary atom are unions of original components. -/
private lemma key_closed (S : Finset V) (u : ↥(delete M S).atoms)
    (hnb : ∀ w : V, (∃ h : w ∈ (delete M S).atoms,
      Relation.EqvGen (fun a b : ↥(delete M S).atoms => (delete M S).Adj a.1 b.1) u ⟨w, h⟩) →
      ¬ ∃ x : D, M.atom x = w ∧ M.atom (M.mate x) ∈ S) :
    ∀ a b : ↥M.atoms, Relation.EqvGen (fun a b : ↥M.atoms => M.Adj a.1 b.1) a b →
      ((∃ h : a.1 ∈ (delete M S).atoms,
        Relation.EqvGen (fun a b : ↥(delete M S).atoms => (delete M S).Adj a.1 b.1) u ⟨a.1, h⟩) ↔
       (∃ h : b.1 ∈ (delete M S).atoms,
        Relation.EqvGen (fun a b : ↥(delete M S).atoms => (delete M S).Adj a.1 b.1) u ⟨b.1, h⟩)) := by
  have step : ∀ a b : V, M.Adj a b → b ∈ M.atoms →
      (∃ h : a ∈ (delete M S).atoms,
        Relation.EqvGen (fun a b : ↥(delete M S).atoms => (delete M S).Adj a.1 b.1) u ⟨a, h⟩) →
      ∃ h : b ∈ (delete M S).atoms,
        Relation.EqvGen (fun a b : ↥(delete M S).atoms => (delete M S).Adj a.1 b.1) u ⟨b, h⟩ := by
    rintro a b hab hb ⟨ha, hu⟩
    obtain ⟨x, h1, h2⟩ := hab
    have haS : a ∉ S := (Finset.mem_sdiff.1 ha).2
    have hbS : b ∉ S := by
      intro hbS
      exact hnb a ⟨ha, hu⟩ ⟨x, h1, h2 ▸ hbS⟩
    have hb' : b ∈ (delete M S).atoms := Finset.mem_sdiff.2 ⟨hb, hbS⟩
    refine ⟨hb', hu.trans _ _ _ (Relation.EqvGen.rel _ _ ?_)⟩
    exact (adj_delete M).2 ⟨x, h1, h2, haS, hbS⟩
  intro a b hab
  induction hab with
  | rel a b h => exact ⟨step _ _ h b.2, step _ _ (adj_symm M h) a.2⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Lemma 7.4, components.** The deleted molecule has at most `c + q` components. -/
theorem numComponents_delete_le (S : Finset V) :
    (delete M S).numComponents ≤ M.numComponents + crossCount M S := by
  classical
  unfold Molecule.numComponents
  set r' : ↥(delete M S).atoms → ↥(delete M S).atoms → Prop :=
    fun a b => (delete M S).Adj a.1 b.1 with hr'
  set r : ↥M.atoms → ↥M.atoms → Prop := fun a b => M.Adj a.1 b.1 with hr
  let f : ↥(delete M S).atoms → ↥M.atoms := fun a => ⟨a.1, (Finset.mem_sdiff.1 a.2).1⟩
  let φ : Quot r' → Quot r := Quot.map f (fun a b h => by
    obtain ⟨x, h1, h2⟩ := h
    exact ⟨x.1, h1, h2⟩)
  let Bs := {b : ↥(delete M S).atoms // ∃ x : D, M.atom x = b.1 ∧ M.atom (M.mate x) ∈ S}
  have hB : Nat.card Bs ≤ crossCount M S := by
    have : Nat.card Bs = (boundaryAtoms M S).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr
        { toFun := fun b => ⟨b.1.1, by
            simp only [boundaryAtoms, Finset.mem_filter]; exact ⟨b.1.2, b.2⟩⟩
          invFun := fun b => ⟨⟨b.1, by
            have := b.2; simp only [boundaryAtoms, Finset.mem_filter] at this; exact this.1⟩, by
            have := b.2; simp only [boundaryAtoms, Finset.mem_filter] at this; exact this.2⟩
          left_inv := fun b => rfl
          right_inv := fun b => rfl }
    rw [this]; exact boundaryAtoms_card_le M S
  let Ψ : Quot r' → Quot r ⊕ Bs := fun c =>
    if h : ∃ b : Bs, Quot.mk r' b.1 = c then Sum.inr h.choose else Sum.inl (φ c)
  have hinj : Function.Injective Ψ := by
    intro c1 c2 h
    by_cases h1 : ∃ b : Bs, Quot.mk r' b.1 = c1 <;> by_cases h2 : ∃ b : Bs, Quot.mk r' b.1 = c2
    · simp only [Ψ, dif_pos h1, dif_pos h2, Sum.inr.injEq] at h
      rw [← h1.choose_spec, ← h2.choose_spec, h]
    · simp [Ψ, dif_pos h1, dif_neg h2] at h
    · simp [Ψ, dif_pos h2, dif_neg h1] at h
    · simp only [Ψ, dif_neg h1, dif_neg h2, Sum.inl.injEq] at h
      induction c1 using Quot.ind with | _ u1 => ?_
      induction c2 using Quot.ind with | _ u2 => ?_
      have hq : Quot.mk r (f u1) = Quot.mk r (f u2) := h
      have hE := Quot.eqvGen_exact hq
      have hnb : ∀ w : V, (∃ h : w ∈ (delete M S).atoms,
          Relation.EqvGen r' u1 ⟨w, h⟩) → ¬ ∃ x : D, M.atom x = w ∧ M.atom (M.mate x) ∈ S := by
        rintro w ⟨hw, hE'⟩ hx
        exact h1 ⟨⟨⟨w, hw⟩, hx⟩, Quot.eqvGen_sound hE'.symm⟩
      have := key_closed M S u1 hnb (f u1) (f u2) hE
      obtain ⟨hh, hE2⟩ := this.1 ⟨u1.2, Relation.EqvGen.refl _⟩
      exact Quot.eqvGen_sound hE2
  have hfin : Finite (Quot r ⊕ Bs) := by
    haveI : Finite ↥M.atoms := inferInstance
    haveI : Finite Bs := inferInstance
    infer_instance
  calc Nat.card (Quot r') ≤ Nat.card (Quot r ⊕ Bs) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (Quot r) + Nat.card Bs := Nat.card_sum
    _ ≤ _ := by omega

end WaveTurbulence.Flower.FlExcise
