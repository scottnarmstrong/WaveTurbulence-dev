/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PartitionBlocks

/-! # Enclosure of legal partitions and even cardinality -/

public section
namespace WaveTurbulence.Reg.PairPartition
open Finset
variable {n : ℕ} (P : PairPartition n)
include P

/-- A finite fixed-point-free partner involution has even cardinality. -/
theorem even_card : Even n := by
  let L := Finset.univ.filter (fun x : Fin n => x < P.pair x)
  let U := Finset.univ.filter (fun x : Fin n => P.pair x < x)
  have himg : L.image P.pair = U := by
    ext x
    simp only [L,U,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [P.involutive]
      exact hy
    · intro hx
      exact ⟨P.pair x,by rw [P.involutive]; exact hx,P.involutive x⟩
  have hc : U.card = L.card := by
    rw [← himg]
    exact Finset.card_image_of_injective _ P.pair_injective
  have hd : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx := (Finset.mem_filter.mp hx).2
    have hy := (Finset.mem_filter.mp hy).2
    exact (not_lt_of_ge (le_of_lt hx)) hy
  have hu : L ∪ U = Finset.univ := by
    ext x
    simp only [L,U,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact lt_or_gt_of_ne (P.no_fixed x).symm
  have he := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd,hc,Finset.card_univ,Fintype.card_fin] at he
  exact ⟨L.card,he.symm⟩

/-- Removing both partners leaves a pairing-closed set. -/
theorem remaining_partner_mem {a b : Fin n} (hab : P.pair a = b) :
    ∀ x ∈ remaining a b, P.pair x ∈ remaining a b := by
  intro x hx
  simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true] at hx ⊢
  constructor
  · intro he
    exact hx.2 (P.pair_injective (he.trans hab.symm))
  · intro he
    have hh := congrArg P.pair he
    rw [P.involutive,hab] at hh
    exact hx.1 hh

/-- Removing the outermost pair preserves legality in both directions.
Together with concatenation, this is DH21 Proposition 4.5(2). -/
theorem legal_iff_enclosure {a b : Fin n} (hab : P.pair a = b)
    (ha : ∀ x, a ≤ x) (hb : ∀ x, x ≤ b) :
    P.Legal ↔ (P.onBlock (remaining a b) (P.remaining_partner_mem hab)).Legal := by
  constructor
  · intro h
    exact P.onBlock_legal h _ _
  · intro h x y z t hxy hyz hzt hxz hyt
    have hxa : x ≠ a := by
      rintro rfl
      rw [hab] at hxz
      subst z
      exact (not_lt_of_ge (hb t)) hzt
    have hta : t ≠ a := ne_of_gt ((ha x).trans_lt (hxy.trans (hyz.trans hzt)))
    have hya : y ≠ a := ne_of_gt ((ha x).trans_lt hxy)
    have hza : z ≠ a := ne_of_gt ((ha y).trans_lt hyz)
    have hxb : x ≠ b := ne_of_lt (hxy.trans_le (hb y))
    have hyb : y ≠ b := ne_of_lt (hyz.trans_le (hb z))
    have hzb : z ≠ b := ne_of_lt (hzt.trans_le (hb t))
    have htb : t ≠ b := by
      intro he
      have hpy : P.pair y = b := hyt.trans he
      have hya' : y = a := P.pair_injective (hpy.trans hab.symm)
      exact hya hya'
    apply P.no_crossing_of_onBlock_legal _ (P.remaining_partner_mem hab) h
      (by simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true]; exact ⟨hxb,hxa⟩)
      (by simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true]; exact ⟨hyb,hya⟩)
      (by simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true]; exact ⟨hzb,hza⟩)
      (by simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true]; exact ⟨htb,hta⟩)
      hxy hyz hzt hxz hyt

end WaveTurbulence.Reg.PairPartition
