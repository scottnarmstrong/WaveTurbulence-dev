/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
import Mathlib.Tactic

/-! # Exact ladders and physical gaps away from the reinserted endpoints -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_sourceLadder_addBond_iff (M : Molecule V D) (a b : V)
    {m : ℕ} (u v : Fin (m+1) → V)
    (havoid : ∀ j,u j ≠ a ∧ u j ≠ b ∧ v j ≠ a ∧ v j ≠ b) :
    Degen.SourceLadder (addBond M a b) u v ↔ Degen.SourceLadder M u v := by
  have hne {p q : V} (hp : p ≠ a ∧ p ≠ b) : s(a,b) ≠ s(p,q) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hp.1 h.1.symm
    · exact hp.2 h.2.symm
  have hatoms (p : V) (hp : p ≠ a ∧ p ≠ b) : p ∈ (addBond M a b).atoms ↔ p ∈ M.atoms := by
    change p ∈ insert a (insert b M.atoms) ↔ _
    simp only [mem_insert,hp.1,hp.2,false_or]
  unfold Degen.SourceLadder
  simp_rw [hatoms _ ⟨(havoid _).1,(havoid _).2.1⟩,
    hatoms _ ⟨(havoid _).2.2.1,(havoid _).2.2.2⟩,
    appb_addBond_bondsBetween,if_neg (hne ⟨(havoid _).1,(havoid _).2.1⟩),
    if_neg (hne ⟨(havoid _).2.2.1,(havoid _).2.2.2⟩),add_zero,
    appb_addBond_directed_iff M a b _ _ (hne ⟨(havoid _).1,(havoid _).2.1⟩),
    appb_addBond_directed_iff M a b _ _ (hne ⟨(havoid _).2.2.1,(havoid _).2.2.2⟩)]

theorem appb_isLadderGap_addBond_iff (M : Molecule V D) (a b : V)
    {d m : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (z : Fin d → ℤ)
    (u v : Fin (m+1) → V) (hm : 1 ≤ m) (g : Mom d)
    (havoid : u 0 ≠ a ∧ u 0 ≠ b ∧ v 0 ≠ a ∧ v 0 ≠ b) :
    (addBond M a b).IsLadderGap L w (Sum.elim κ (fun _ : Bool => z)) u v hm g ↔
      M.IsLadderGap L w κ u v hm g := by
  constructor
  · rintro ⟨x,y,hx,hy,hax,hay,hg⟩
    have hxold : ∃ x0 : D,x = Sum.inl x0 := by
      rcases x with x | t
      · exact ⟨x,rfl⟩
      · cases t
        · exact (havoid.2.1 hax.symm).elim
        · exact (havoid.1 hax.symm).elim
    have hyold : ∃ y0 : D,y = Sum.inl y0 := by
      rcases y with y | t
      · exact ⟨y,rfl⟩
      · cases t
        · exact (havoid.2.2.2 hay.symm).elim
        · exact (havoid.2.2.1 hay.symm).elim
    obtain ⟨x0,rfl⟩ := hxold
    obtain ⟨y0,rfl⟩ := hyold
    exact ⟨x0,y0,hx,hy,hax,hay,hg⟩
  · rintro ⟨x,y,hx,hy,hax,hay,hg⟩
    exact ⟨Sum.inl x,Sum.inl y,hx,hy,hax,hay,hg⟩

end WaveTurbulence.Mole
