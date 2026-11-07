/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingCutSums
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
import Mathlib.Tactic

/-! # Two-bond cut coordinates and exact label reconstruction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbCutSign (M : Molecule V D) (S : Finset V) (x : D) : ℤˣ :=
  if M.atom x ∈ S then 1 else -1

theorem appb_cut_sign_eq (M : Molecule V D) (S : Finset V) (x : D)
    (hx : (M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) ∨
      (M.atom x ∉ S ∧ M.atom (M.mate x) ∈ S)) {E : Type*} [AddCommGroup E] (a : E) :
    ((if M.atom x ∈ S then a else 0)-(if M.atom (M.mate x) ∈ S then a else 0)) =
      (appbCutSign M S x : ℤ) • a := by
  rcases hx with h | h
  · simp [appbCutSign,h.1,h.2]
  · simp [appbCutSign,h.1,h.2]

/-- Two actual crossing bonds of a concrete old cut, with every other
local bond staying on one side. All fields are input graph facts. -/
structure AppbCutPair {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (S : Finset V) where
  subset_atoms : S ⊆ M.atoms
  crossing : appbCrossingBonds M S ⊆ appbRemovedBonds M r.removedAtoms
  first : Fin P.edges.length
  second : Fin P.edges.length
  distinct : first ≠ second
  first_cross : (M.atom (r.edge first).val ∈ S ∧ M.atom (M.mate (r.edge first).val) ∉ S) ∨
    (M.atom (r.edge first).val ∉ S ∧ M.atom (M.mate (r.edge first).val) ∈ S)
  second_cross : (M.atom (r.edge second).val ∈ S ∧ M.atom (M.mate (r.edge second).val) ∉ S) ∨
    (M.atom (r.edge second).val ∉ S ∧ M.atom (M.mate (r.edge second).val) ∈ S)
  other : ∀ i,i ≠ first → i ≠ second →
    (M.atom (r.edge i).val ∈ S ↔ M.atom (M.mate (r.edge i).val) ∈ S)

namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (p : AppbCutPair r S)

theorem momentum {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    (appbCutSign M S (r.edge p.first).val : ℤ) • Molecule.kvec L w (r.localLabels κ) p.first+
      (appbCutSign M S (r.edge p.second).val : ℤ) • Molecule.kvec L w (r.localLabels κ) p.second =
        ∑ v ∈ S,c v := by
  have hm := r.cut_momentum S p.subset_atoms p.crossing L w c κ hκ
  rw [sum_eq_add_of_mem p.first p.second (mem_univ _) (mem_univ _) p.distinct] at hm
  · simpa only [appb_cut_sign_eq M S _ p.first_cross,appb_cut_sign_eq M S _ p.second_cross] using hm
  · intro i hi hne
    have hh := p.other i hne.1 hne.2
    by_cases ha : M.atom (r.edge i).val ∈ S
    · simp only [ha,hh.mp ha,ite_true,sub_self]
    · have hb : M.atom (M.mate (r.edge i).val) ∉ S := fun hb => ha (hh.mpr hb)
      simp only [ha,hb,ite_false,sub_zero]

/-- Fixed source momentum across an actual two-bond cut fixes one local
integer label once the other is known. -/
theorem second_label_eq {d : ℕ} {L : ℝ} (hL : L ≠ 0) (w : Mom d) (c : V → Mom d)
    (κ κ' : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ')
    (hfirst : r.localLabels κ p.first = r.localLabels κ' p.first) :
    r.localLabels κ p.second = r.localLabels κ' p.second := by
  have hm := p.momentum L w c κ hκ
  have hm' := p.momentum L w c κ' hκ'
  have he : Molecule.kvec L w (r.localLabels κ) p.first = Molecule.kvec L w (r.localLabels κ') p.first :=
    congrArg (fun z => w+latticePoint L z) hfirst
  rw [he] at hm
  have hs := add_left_cancel (hm.trans hm'.symm)
  have hvec : Molecule.kvec L w (r.localLabels κ) p.second = Molecule.kvec L w (r.localLabels κ') p.second := by
    rcases Int.units_eq_one_or (appbCutSign M S (r.edge p.second).val) with h | h
    · simpa only [h,Units.val_one,one_smul] using hs
    · simpa only [h,Units.val_neg,Units.val_one,neg_smul,one_smul,neg_inj] using hs
  exact appb_latticePoint_injective hL (add_left_cancel hvec)

end AppbCutPair
end WaveTurbulence.Mole
