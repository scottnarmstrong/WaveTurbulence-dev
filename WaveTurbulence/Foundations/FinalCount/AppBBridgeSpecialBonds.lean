/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondErasure
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # Exact special-bond effects of bridge removal from old graph data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbErasedPairCount (M : Molecule V D) (e : D) (a b : V) : ℕ := by
  classical
  exact (M.bonds.filter fun x => x ≠ e ∧ x ≠ M.mate e ∧ M.ends x = s(a,b)).card

theorem appb_eraseBond_pair_count (M : Molecule V D) (e : D) (a b : V) :
    (eraseBond M e).bondsBetween a b = appbErasedPairCount M e a b := by
  classical
  apply card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨hx,hend⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,x.property.1,x.property.2,hend⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hx,hne,hnm,hend⟩ := mem_filter.mp hx
    exact ⟨⟨x,hne,hnm⟩,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,hend⟩,rfl⟩

def AppbErasedBondSpecial (M : Molecule V D) (e x : D) : Prop :=
  M.out x = true ∧
  M.deg (M.atom x) = 3+(if M.atom e = M.atom x then 1 else 0)+(if M.atom (M.mate e) = M.atom x then 1 else 0) ∧
  M.deg (M.atom (M.mate x)) = 3+(if M.atom e = M.atom (M.mate x) then 1 else 0)+
    (if M.atom (M.mate e) = M.atom (M.mate x) then 1 else 0) ∧
  ∃ a ∈ M.atoms,∃ b ∈ M.atoms,a ≠ b ∧ a ≠ M.atom x ∧ a ≠ M.atom (M.mate x) ∧
    b ≠ M.atom x ∧ b ≠ M.atom (M.mate x) ∧
    appbErasedPairCount M e (M.atom x) (M.atom (M.mate x)) = 1 ∧
    appbErasedPairCount M e (M.atom x) a = 2 ∧ appbErasedPairCount M e (M.atom (M.mate x)) b = 2

theorem appb_eraseBond_special_iff (M : Molecule V D) (e : D)
    (x : {x : D // x ≠ e ∧ x ≠ M.mate e}) :
    AppbSpecial (eraseBond M e) x ↔ AppbErasedBondSpecial M e x.val := by
  have h1 := appb_eraseBond_degree M e (M.atom x.val)
  have h2 := appb_eraseBond_degree M e (M.atom (M.mate x.val))
  have hd1 : (eraseBond M e).deg (M.atom x.val) = 3 ↔
      M.deg (M.atom x.val) = 3+(if M.atom e = M.atom x.val then 1 else 0)+
        (if M.atom (M.mate e) = M.atom x.val then 1 else 0) := by omega
  have hd2 : (eraseBond M e).deg (M.atom (M.mate x.val)) = 3 ↔
      M.deg (M.atom (M.mate x.val)) = 3+(if M.atom e = M.atom (M.mate x.val) then 1 else 0)+
        (if M.atom (M.mate e) = M.atom (M.mate x.val) then 1 else 0) := by omega
  unfold AppbSpecial AppbErasedBondSpecial
  change M.out x.val = true ∧ _ ↔ _
  have hax : (eraseBond M e).atom x = M.atom x.val := rfl
  have hay : (eraseBond M e).atom ((eraseBond M e).mate x) = M.atom (M.mate x.val) := rfl
  have hatoms : (eraseBond M e).atoms = M.atoms := rfl
  simp only [hax,hay,hatoms,hd1,hd2,appb_eraseBond_pair_count]

noncomputable def appbErasedSpecialBonds (M : Molecule V D) (e : D) : Finset D := by
  classical
  exact M.bonds.filter fun x => x ≠ e ∧ x ≠ M.mate e ∧ AppbErasedBondSpecial M e x

theorem appb_eraseBond_special_count (M : Molecule V D) (e : D) :
    (appbSpecialBonds (eraseBond M e)).card = (appbErasedSpecialBonds M e).card := by
  classical
  apply card_bij (fun x _ => x.val)
  · intro x hx
    have hs := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hs.1⟩,x.property.1,x.property.2,
      (appb_eraseBond_special_iff M e x).mp hs⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hx,hne,hnm,hs⟩ := mem_filter.mp hx
    exact ⟨⟨x,hne,hnm⟩,mem_filter.mpr ⟨mem_univ _,
      (appb_eraseBond_special_iff M e ⟨x,hne,hnm⟩).mpr hs⟩,rfl⟩

end WaveTurbulence.Mole
