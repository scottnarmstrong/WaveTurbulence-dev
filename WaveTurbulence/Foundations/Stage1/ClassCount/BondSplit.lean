/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Lab
public import WaveTurbulence.Foundations.Stage1.ClassCount.Irregular
public import WaveTurbulence.Foundations.LayerCnt.BondExp
import Mathlib.Tactic

/-!
# CLASSCOUNT: partition of the bond exponent of the skeleton

For the skeleton molecule `M` and its spliced molecule `M'` (a `SpliceData`), the bond exponent of a layering `f ≤ p`
of `M` is at most the sum of the bond exponents of the units (internal bonds), of the ladders of `M'` (for the
layering `f ∘ ob`), plus `4 p ρ̄` for the remaining bonds (irregular bonds of `M'` and darts at hinges).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.LayerCnt

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Summing over a union of sets is at most the sum of the sums. -/
theorem sum_biUnion_le_nat {α ι : Type*} [DecidableEq α] (t : Finset ι) (T : ι → Finset α) (g : α → ℕ) :
    ∑ x ∈ t.biUnion T, g x ≤ ∑ i ∈ t, ∑ x ∈ T i, g x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := T a) (s₂ := t.biUnion T) (f := g)
    omega

theorem sum_sub_biUnion_le {α ι : Type*} [DecidableEq α] (s : Finset α) (t : Finset ι) (T : ι → Finset α)
    (hs : s ⊆ t.biUnion T) (g : α → ℕ) : ∑ x ∈ s, g x ≤ ∑ i ∈ t, ∑ x ∈ T i, g x :=
  (Finset.sum_le_sum_of_subset hs).trans (sum_biUnion_le_nat t T g)

/-- Each bond is counted once by its outgoing dart: `Σ_{bonds} (h x + h (mate x)) = Σ_{darts} h`. -/
theorem sum_bonds_add_mate (M : Molecule V D) (h : D → ℕ) :
    ∑ x ∈ M.bonds, (h x + h (M.mate x)) = ∑ x, h x := by
  classical
  rw [Finset.sum_add_distrib]
  have h2 : ∑ x ∈ M.bonds, h (M.mate x) = ∑ x ∈ univ.filter (fun x => ¬ M.out x = true), h x := by
    apply Finset.sum_nbij' (fun x => M.mate x) (fun x => M.mate x)
    · intro x hx
      simp only [Molecule.bonds, mem_filter, mem_univ, true_and] at hx ⊢
      rw [M.out_mate, hx]; simp
    · intro x hx
      simp only [Molecule.bonds, mem_filter, mem_univ, true_and] at hx ⊢
      rw [M.out_mate]; simpa using hx
    · intro x _; exact M.mate_mate x
    · intro x _; exact M.mate_mate x
    · intro x _; rfl
  rw [h2]
  unfold Molecule.bonds
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem LReg_mem {m : ℕ} {u v : Fin (m + 1) → V} {a b : V} (h : LReg u v a b) :
    a ∈ Molecule.ladderAtoms u v ∧ b ∈ Molecule.ladderAtoms u v := by
  classical
  unfold Molecule.ladderAtoms
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  rcases h with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩⟩
  · exact ⟨Or.inr ⟨i, rfl⟩, Or.inl ⟨i, rfl⟩⟩
  · exact ⟨Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩⟩
  · exact ⟨Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩⟩
  · exact ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩
  · exact ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩

theorem bondsIn_atoms (M : Molecule V D) : bondsIn M M.atoms = M.bonds := by
  unfold bondsIn
  apply Finset.filter_true_of_mem
  intro x _
  exact ⟨M.atom_mem x, M.atom_mem (M.mate x)⟩

/-- The bond exponent of the whole molecule is at most the ladder exponents plus `p` for each irregular bond. -/
theorem bondExp_ladders_le (M : Molecule V D) (hM : M.IsMolecule) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : LadderFam M ι) (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j))
    (p : ℕ) (f : V → ℕ) (hf : ∀ v, f v ≤ p) :
    bondExp M M.atoms f ≤ ∑ i : ι, bondExp M (F.atomsOf i) f +
      p * (4 * (M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι) := by
  classical
  set g : D → ℕ := fun x => dst (f (M.atom x)) (f (M.atom (M.mate x))) with hg
  have hgp : ∀ x, g x ≤ p := by
    intro x; have := hf (M.atom x); have := hf (M.atom (M.mate x)); simp only [hg, dst]; omega
  set Irr := M.bonds.filter (fun x => ¬ F.Reg (M.atom x) (M.atom (M.mate x))) with hIrr
  have hsub : M.bonds ⊆ Irr ∪ (Finset.univ : Finset ι).biUnion (fun i => bondsIn M (F.atomsOf i)) := by
    intro x hx
    by_cases hr : F.Reg (M.atom x) (M.atom (M.mate x))
    · obtain ⟨i, hi⟩ := hr
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      unfold bondsIn
      rw [Finset.mem_filter]
      exact ⟨hx, LReg_mem hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, hr⟩)
  have hIrrc : Irr.card ≤ 4 * (M.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι := by
    refine le_trans ?_ (F.card_irrBonds_le hM hdisj)
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_, hx.2⟩
    exact (Finset.mem_filter.1 hx.1).2
  calc bondExp M M.atoms f = ∑ x ∈ M.bonds, g x := by
        unfold bondExp; rw [bondsIn_atoms]
    _ ≤ ∑ x ∈ Irr ∪ (Finset.univ : Finset ι).biUnion (fun i => bondsIn M (F.atomsOf i)), g x :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ x ∈ Irr, g x + ∑ x ∈ (Finset.univ : Finset ι).biUnion (fun i => bondsIn M (F.atomsOf i)), g x := by
        have := Finset.sum_union_inter (s₁ := Irr) (s₂ := (Finset.univ : Finset ι).biUnion (fun i => bondsIn M (F.atomsOf i)))
          (f := g)
        omega
    _ ≤ p * Irr.card + ∑ i : ι, ∑ x ∈ bondsIn M (F.atomsOf i), g x := by
        refine add_le_add ?_ (sum_biUnion_le_nat _ _ _)
        calc ∑ x ∈ Irr, g x ≤ ∑ x ∈ Irr, p := Finset.sum_le_sum fun x _ => hgp x
          _ = p * Irr.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := by
        rw [add_comm]
        refine add_le_add le_rfl ?_
        exact Nat.mul_le_mul_left _ hIrrc

variable {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D']

/-- The darts of `M'` at hinge atoms (atoms whose image is a representative) number at most `4 q`. -/
theorem card_disc_darts_le {M : Molecule V D} {M' : Molecule V' D'} (SD : SpliceData M M')
    (hM' : M'.IsMolecule) :
    (Finset.univ.filter (fun y : D' => ∃ i, i < SD.q ∧ SD.ob (M'.atom y) = SD.rep i)).card ≤ 4 * SD.q := by
  classical
  set H := M'.atoms.filter (fun c => ∃ i, i < SD.q ∧ SD.ob c = SD.rep i) with hH
  have hHc : H.card ≤ SD.q := by
    have hsub : H ⊆ (Finset.range SD.q).biUnion (fun i => M'.atoms.filter (fun c => SD.ob c = SD.rep i)) := by
      intro c hc
      obtain ⟨hc1, i, hi, hci⟩ := Finset.mem_filter.1 hc
      exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, Finset.mem_filter.2 ⟨hc1, hci⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ i ∈ Finset.range SD.q, (M'.atoms.filter (fun c => SD.ob c = SD.rep i)).card
        ≤ ∑ i ∈ Finset.range SD.q, 1 := by
          refine Finset.sum_le_sum fun i _ => Finset.card_le_one.2 ?_
          intro a ha b hb
          exact SD.ob_inj ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
      _ = SD.q := by simp
  have hsub : (Finset.univ.filter (fun y : D' => ∃ i, i < SD.q ∧ SD.ob (M'.atom y) = SD.rep i)) ⊆
      H.biUnion (fun c => M'.dartsAt c) := by
    intro y hy
    obtain ⟨-, hy2⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_biUnion.2 ⟨M'.atom y, Finset.mem_filter.2 ⟨M'.atom_mem y, hy2⟩, ?_⟩
    simp [Molecule.dartsAt]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ c ∈ H, (M'.dartsAt c).card ≤ ∑ c ∈ H, 4 := by
        refine Finset.sum_le_sum fun c hc => ?_
        exact Mole.deg_le_four M' hM' (Finset.mem_filter.1 hc).1
    _ = 4 * H.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 * SD.q := Nat.mul_le_mul_left _ hHc

/-- **The bond partition.**  The bond exponent of a layering `f ≤ p` of the skeleton molecule is at most the unit
exponents (internal bonds), the ladder exponents of the spliced molecule for `f ∘ ob`, and `p` for each of at most
`4 ρ̄ = 4 (q + ρ_sb)` remaining bonds. -/
theorem bondExp_splice_le {M : Molecule V D} {M' : Molecule V' D'} (SD : SpliceData M M')
    (hM' : M'.IsMolecule) {ι : Type} [Fintype ι] [DecidableEq ι] (F : LadderFam M' ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F.atomsOf i) (F.atomsOf j)) (p : ℕ) (f : V → ℕ) (hf : ∀ v, f v ≤ p) :
    bondExp M M.atoms f ≤ ∑ i ∈ Finset.range SD.q, bondExp M (SD.U i) f +
      ∑ i : ι, bondExp M' (F.atomsOf i) (f ∘ SD.ob) +
      p * (4 * SD.q + (4 * (M'.atoms.filter (fun a => ∀ i, a ∉ F.atomsOf i)).card + 4 * Fintype.card ι)) := by
  classical
  set g : D → ℕ := fun x => dst (f (M.atom x)) (f (M.atom (M.mate x))) with hg
  set g' : D' → ℕ := fun y => dst (f (SD.ob (M'.atom y))) (f (SD.ob (M'.atom (M'.mate y)))) with hg'
  set δ : D' → ℕ := fun y => if SD.cl (M.atom (SD.od y)) = M.atom (SD.od y) then 0 else 1 with hδ
  set I := M.bonds.filter (fun x => ∃ i, i < SD.q ∧ M.atom x ∈ SD.U i ∧ M.atom (M.mate x) ∈ SD.U i) with hI
  set E := M.bonds.filter (fun x => ¬ ∃ i, i < SD.q ∧ M.atom x ∈ SD.U i ∧ M.atom (M.mate x) ∈ SD.U i) with hE
  have h1 : bondExp M M.atoms f = ∑ x ∈ I, g x + ∑ x ∈ E, g x := by
    unfold bondExp; rw [bondsIn_atoms]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- internal bonds
  have h2 : ∑ x ∈ I, g x ≤ ∑ i ∈ Finset.range SD.q, bondExp M (SD.U i) f := by
    refine sum_sub_biUnion_le I (Finset.range SD.q) (fun i => bondsIn M (SD.U i)) ?_ g
    intro x hx
    obtain ⟨hx1, i, hi, h3, h4⟩ := Finset.mem_filter.1 hx
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_range.2 hi, Finset.mem_filter.2 ⟨hx1, h3, h4⟩⟩
  -- external bonds come from bonds of `M'`
  have h3 : ∑ x ∈ E, g x ≤ ∑ y ∈ M'.bonds, g (SD.od y) := by
    have hsub : E ⊆ M'.bonds.image SD.od := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨y, hy⟩ := (SD.od_range x).2 hx2
      rw [Finset.mem_image]
      refine ⟨y, ?_, hy⟩
      have : M.out x = true := (Finset.mem_filter.1 hx1).2
      rw [← hy, SD.od_out] at this
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    calc ∑ x ∈ E, g x ≤ ∑ x ∈ M'.bonds.image SD.od, g x := Finset.sum_le_sum_of_subset hsub
      _ = ∑ y ∈ M'.bonds, g (SD.od y) := Finset.sum_image (fun a _ b _ h => SD.od_inj h)
  -- comparison of each bond with its image
  have h4 : ∀ y, g (SD.od y) ≤ g' y + p * (δ y + δ (M'.mate y)) := by
    intro y
    have ha : SD.ob (M'.atom y) = SD.cl (M.atom (SD.od y)) := SD.ob_atom y
    have hb : SD.ob (M'.atom (M'.mate y)) = SD.cl (M.atom (SD.od (M'.mate y))) := SD.ob_atom _
    have hm : M.atom (SD.od (M'.mate y)) = M.atom (M.mate (SD.od y)) := by rw [SD.od_mate]
    simp only [hg, hg', hδ]
    rw [ha, hb, hm]
    set a := M.atom (SD.od y)
    set b := M.atom (M.mate (SD.od y))
    have hfa := hf a
    have hfb := hf b
    have hfca := hf (SD.cl a)
    have hfcb := hf (SD.cl b)
    unfold dst
    by_cases h5 : SD.cl a = a <;> by_cases h6 : SD.cl b = b
    · simp only [h5, h6, if_true, ha, hb]; omega
    · simp only [h5, h6, if_true, if_false]; omega
    · simp only [h5, h6, if_true, if_false]; omega
    · simp only [h5, h6, if_false]; omega
  have h5 : ∑ y ∈ M'.bonds, g (SD.od y) ≤ ∑ y ∈ M'.bonds, g' y + p * ∑ y, δ y := by
    calc ∑ y ∈ M'.bonds, g (SD.od y) ≤ ∑ y ∈ M'.bonds, (g' y + p * (δ y + δ (M'.mate y))) :=
          Finset.sum_le_sum fun y _ => h4 y
      _ = ∑ y ∈ M'.bonds, g' y + p * ∑ y ∈ M'.bonds, (δ y + δ (M'.mate y)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [sum_bonds_add_mate]
  have h6 : ∑ y, δ y ≤ 4 * SD.q := by
    refine le_trans ?_ (card_disc_darts_le SD hM')
    calc ∑ y, δ y ≤ ∑ y ∈ Finset.univ.filter (fun y : D' => ∃ i, i < SD.q ∧ SD.ob (M'.atom y) = SD.rep i), 1 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : D' => ∃ i, i < SD.q ∧ SD.ob (M'.atom y) = SD.rep i)]
          have hz : ∑ y ∈ Finset.univ.filter (fun y : D' => ¬ ∃ i, i < SD.q ∧ SD.ob (M'.atom y) = SD.rep i), δ y = 0 := by
            refine Finset.sum_eq_zero fun y hy => ?_
            have hy' := (Finset.mem_filter.1 hy).2
            simp only [hδ]
            by_contra hne
            have hcl : SD.cl (M.atom (SD.od y)) ≠ M.atom (SD.od y) := by
              intro h; simp [h] at hne
            have hfree : ∃ i, i < SD.q ∧ M.atom (SD.od y) ∈ SD.U i := by
              by_contra hno
              push_neg at hno
              exact hcl (SD.cl_free _ hno)
            obtain ⟨i, hi, hmem⟩ := hfree
            apply hy'
            refine ⟨i, hi, ?_⟩
            rw [SD.ob_atom, SD.cl_unit i hi _ hmem]
          rw [hz, add_zero]
          refine Finset.sum_le_sum fun y _ => ?_
          simp only [hδ]; split_ifs <;> simp
      _ = _ := by simp
  have h7 : ∑ y ∈ M'.bonds, g' y = bondExp M' M'.atoms (f ∘ SD.ob) := by
    unfold bondExp; rw [bondsIn_atoms]; rfl
  have h8 := bondExp_ladders_le M' hM' F hdisj p (f ∘ SD.ob) (fun v => hf _)
  rw [h1]
  calc ∑ x ∈ I, g x + ∑ x ∈ E, g x
      ≤ ∑ i ∈ Finset.range SD.q, bondExp M (SD.U i) f + (bondExp M' M'.atoms (f ∘ SD.ob) + p * (4 * SD.q)) := by
        refine add_le_add h2 (h3.trans (h5.trans ?_))
        rw [h7]
        exact add_le_add le_rfl (Nat.mul_le_mul_left _ h6)
    _ ≤ _ := by nlinarith [h8]

end WaveTurbulence.ClassCount
