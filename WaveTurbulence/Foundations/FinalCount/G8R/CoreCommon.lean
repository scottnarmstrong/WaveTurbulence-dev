/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.MergeDecor
import Mathlib.Tactic

/-! # Common tools for the core case analysis of Prop 10.4(2)′

* the inputs at a fixed `L` (Prop 10.2, both statements; G6's Prop 10.3);
* monotonicity of `SplitBound` and subadditivity of the count in the admissibility;
* `𝕄 ∖ ℓ` for a core `𝕄`: degrees and crossing darts;
* Prop 10.2 applied to an induced piece.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- DH23 Prop 10.2, first statement, at a fixed `L` (the body of `Prop102Input`). -/
def Prop102At (d : ℕ) (L γ δ η C1 : ℝ) (m : ℕ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → (∀ a b, M.bondsBetween a b ≤ 2) →
    (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ))))

/-- DH23 Prop 10.2, second statement, at a fixed `L` (the body of `Prop102SecondInput`). -/
def Prop102SecondAt (d : ℕ) (L γ δ η C1 : ℝ) (m : ℕ) : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → (∀ a b, M.bondsBetween a b ≤ 2) →
    (M.bonds.card : ℤ) = 2 * M.atoms.card - 2 → 0 < M.bonds.card → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
      AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (L ^ (-(η / 3)))

theorem prop102At_of_input {d : ℕ} {γ η : ℝ} (h : Prop102Input.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      Prop102At.{u, v} d L γ δ η C1 m := h

theorem prop102SecondAt_of_input {d : ℕ} {γ η : ℝ} (h : Prop102SecondInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      Prop102SecondAt.{u, v} d L γ δ η C1 m := h

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `SplitBound` is monotone in the two bounds. -/
theorem splitBound_mono {M : Molecule V D} {e : D} {d : ℕ} {L γ δ η C1 ε₁ ε₂ ε₁' ε₂' : ℝ}
    (h : SplitBound M e d L γ δ η C1 ε₁ ε₂) (h1 : ε₁ ≤ ε₁') (h2 : ε₂ ≤ ε₂') : SplitBound M e d L γ δ η C1 ε₁' ε₂' := by
  obtain ⟨Q, hQ1, hQ2⟩ := h
  exact ⟨Q, fun P hP => (hQ1 P hP).trans (ENNReal.ofReal_le_ofReal h1),
    fun P hP => (hQ2 P hP).trans (ENNReal.ofReal_le_ofReal h2)⟩

/-- **The count is subadditive in the admissibility.** -/
theorem countAFree_or_le (M : Molecule V D) {d : ℕ} {L γ δ C1 : ℝ} {P : Finset V → ℝ}
    (A B : (D → (Fin d → ℤ)) → Prop) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) (fun κ => A κ ∨ B κ) P ≤
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) A P + MoleProp.countAFree M L γ δ C1 (0 : Mom d) B P := by
  have hE : MoleProp.countEFree M L γ δ (0 : Mom d) (fun κ => A κ ∨ B κ) ≤
      MoleProp.countEFree M L γ δ (0 : Mom d) A + MoleProp.countEFree M L γ δ (0 : Mom d) B := by
    conv_lhs => unfold MoleProp.countEFree
    refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
    refine (Set.encard_mono ?_).trans ((Set.encard_union_le _ _).trans (add_le_add
      (MoleProp.encard_le_countEFree M L γ δ 0 A c β k0 hk0) (MoleProp.encard_le_countEFree M L γ δ 0 B c β k0 hk0)))
    rintro κ ⟨h1, h2, h | h⟩
    · exact Or.inl ⟨h1, h2, h⟩
    · exact Or.inr ⟨h1, h2, h⟩
  rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization,
    MoleProp.countAFree_eq_normalization, ← add_mul, ← ENat.toENNReal_add]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono hE) bot_le

/-- **Crossing darts after removing a bond**: the bond is lost from `∂S` iff it crosses `S`. -/
theorem card_cross_eraseBond (M : Molecule V D) (e : D) (S : Finset V) :
    (crossDarts (MoleProp.eraseBond M e) S).card +
      ((if M.atom e ∈ S ∧ M.atom (M.mate e) ∉ S then 1 else 0) +
        (if M.atom (M.mate e) ∈ S ∧ M.atom e ∉ S then 1 else 0)) = (crossDarts M S).card := by
  classical
  have h1 : (crossDarts (MoleProp.eraseBond M e) S).card =
      ((crossDarts M S).filter fun x => x ≠ e ∧ x ≠ M.mate e).card := by
    refine card_bij (fun x _ => x.val) ?_ (fun x _ y _ h => Subtype.ext h) ?_
    · intro x hx
      have h := mem_crossDarts.mp hx
      exact mem_filter.mpr ⟨(mem_crossDarts (N := M)).mpr h, x.property⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
      have h := (mem_crossDarts (N := M)).mp hx1
      exact ⟨⟨x, hx2⟩, (mem_crossDarts (N := MoleProp.eraseBond M e)).mpr h, rfl⟩
  have hne : e ≠ M.mate e := fun h => M.mate_ne e h.symm
  have h2 : ((crossDarts M S).filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)).card =
      (if M.atom e ∈ S ∧ M.atom (M.mate e) ∉ S then 1 else 0) +
        (if M.atom (M.mate e) ∈ S ∧ M.atom e ∉ S then 1 else 0) := by
    have hset : ((crossDarts M S).filter fun x => ¬(x ≠ e ∧ x ≠ M.mate e)) =
        ({e, M.mate e} : Finset D).filter fun x => x ∈ crossDarts M S := by
      ext x
      simp only [mem_filter, mem_insert, mem_singleton, not_and_or, not_not]
      tauto
    have hc1 : e ∈ crossDarts M S ↔ M.atom e ∈ S ∧ M.atom (M.mate e) ∉ S := mem_crossDarts
    have hc2 : M.mate e ∈ crossDarts M S ↔ M.atom (M.mate e) ∈ S ∧ M.atom e ∉ S := by
      rw [mem_crossDarts, M.mate_mate]
    rw [hset, card_filter, sum_pair hne]
    simp only [hc1, hc2]
  rw [h1, ← h2, card_filter_add_card_filter_not]

namespace IsCore
variable {M : Molecule V D} (hM : IsCore M) (e : D)
include hM

omit [DecidableEq D] in
/-- The ends of `ℓ` are distinct. -/
theorem ends_ne : M.atom e ≠ M.atom (M.mate e) := hM.loop e

theorem eraseBond_deg_p : (MoleProp.eraseBond M e).deg (M.atom e) = 3 := by
  have h := deg_eraseBond_add M e (M.atom e)
  rw [ite_of_pos rfl, ite_of_not (Ne.symm (hM.loop e)), hM.reg _ (M.atom_mem e)] at h
  omega

theorem eraseBond_deg_q : (MoleProp.eraseBond M e).deg (M.atom (M.mate e)) = 3 := by
  have h := deg_eraseBond_add M e (M.atom (M.mate e))
  rw [ite_of_pos rfl, ite_of_not (hM.loop e), hM.reg _ (M.atom_mem _)] at h
  omega

theorem eraseBond_deg_le {v : V} (hv : v ∈ M.atoms) : (MoleProp.eraseBond M e).deg v ≤ 4 := by
  have h := deg_eraseBond_add M e v
  rw [hM.reg v hv] at h
  omega

omit [DecidableEq D] in
theorem eraseBond_conn : ∀ a ∈ (MoleProp.eraseBond M e).atoms, ∀ b ∈ (MoleProp.eraseBond M e).atoms,
    (MoleProp.eraseBond M e).SameComponent a b :=
  eraseBond_connected_of_even M (fun a ha => by rw [hM.reg a ha]; exact ⟨2, rfl⟩) hM.conn e

omit [DecidableEq D] in
theorem eraseBond_loop : ∀ z, (MoleProp.eraseBond M e).atom z ≠
    (MoleProp.eraseBond M e).atom ((MoleProp.eraseBond M e).mate z) := fun z => hM.loop z.val

theorem eraseBond_isMolecule : (MoleProp.eraseBond M e).IsMolecule :=
  isMolecule_of_connected _ (caps_eraseBond M e hM.cap) (hM.eraseBond_conn e) (M.atom_mem e)
    (by rw [hM.eraseBond_deg_p e]; norm_num)

/-- **Degree sum of `𝕄 ∖ ℓ` over `S`.** -/
theorem eraseBond_sum_deg {S : Finset V} (hS : S ⊆ M.atoms) :
    ∑ v ∈ S, (MoleProp.eraseBond M e).deg v + ((if M.atom e ∈ S then 1 else 0) +
      (if M.atom (M.mate e) ∈ S then 1 else 0)) = 4 * S.card := by
  have h : ∀ v ∈ S, (MoleProp.eraseBond M e).deg v + (if M.atom e = v then 1 else 0) +
      (if M.atom (M.mate e) = v then 1 else 0) = 4 := fun v hv => by
    rw [deg_eraseBond_add, hM.reg v (hS hv)]
  have hs := sum_congr rfl h
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq, sum_ite_eq, sum_const, smul_eq_mul] at hs
  omega

end IsCore

/-- **Prop 10.2 on an induced piece.** -/
theorem afreeSup_piece_le {d : ℕ} {L γ δ η C1 : ℝ} {m : ℕ} {V : Type u} {D : Type v} [DecidableEq V] [Fintype D]
    [DecidableEq D] (h102 : Prop102At.{u, v} d L γ δ η C1 m) (K : Molecule V D)
    (hsz : (K.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m) {S : Finset V} (hS : S ⊆ K.atoms)
    (hcap : ∀ a ∈ K.atoms, K.outdeg a ≤ 2 ∧ K.indeg a ≤ 2) (hle2 : ∀ a b, K.bondsBetween a b ≤ 2)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (piece K S).SameComponent a b) {z : V} (hz : z ∈ S) (hz4 : (piece K S).deg z ≠ 4)
    (hE : ((piece K S).bonds.card : ℤ) = 2 * S.card - 1) :
    AFreeSup (piece K S) d L γ δ η C1 ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
  have hmol := piece_isMolecule hS hcap hconn hz hz4
  have hconn' : ∀ a ∈ (piece K S).atoms, ∀ b ∈ (piece K S).atoms, (piece K S).SameComponent a b := by
    rw [piece_atoms hS]; exact hconn
  have hE' : ((piece K S).bonds.card : ℤ) = 2 * (piece K S).atoms.card - 1 := by rw [piece_atoms hS]; exact hE
  refine iSup₂_le fun P hP => h102 _ hmol hconn' (fun a b => (erase_bonds_le K _ a b).trans (hle2 a b)) hE'
    (hsz.trans' ?_) P hP
  rw [piece_atoms hS]; exact_mod_cast card_le_card hS

end WaveTurbulence.MoleProp4
