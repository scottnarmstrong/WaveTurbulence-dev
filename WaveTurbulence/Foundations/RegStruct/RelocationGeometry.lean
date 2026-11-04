/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality
public import WaveTurbulence.Foundations.RegStruct.RootAddressMaps

/-! # Local geometry of the source operation-B relocation map

Relocation respects path extension below a descendant root or below a root
incomparable with the insertion node. It is not claimed to respect extension
at a strict ancestor of that node.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The second raw address lies below the first, in the same original tree. -/
def Below {w : ℕ} (a b : Fin w × Path) : Prop := b.1 = a.1 ∧ a.2 <+: b.2

instance {w : ℕ} (a b : Fin w × Path) : Decidable (Below a b) := by unfold Below; infer_instance

/-- Every path extension stays below its own root. -/
theorem below_extend {w : ℕ} (a : Fin w × Path) (p : Path) : Below a (addrExt a p) :=
  ⟨rfl,List.prefix_append _ _⟩

theorem below_trans {w : ℕ} {a b c : Fin w × Path} (hab : Below a b) (hbc : Below b c) :
    Below a c := ⟨hbc.1.trans hab.1,hab.2.trans hbc.2⟩

/-- Two ancestors of one address are comparable. -/
theorem below_comparable {w : ℕ} {a b z : Fin w × Path} (ha : Below a z) (hb : Below b z) :
    Below a b ∨ Below b a := by
  rcases List.prefix_or_prefix_of_prefix ha.2 hb.2 with hab | hba
  · exact Or.inl ⟨hb.1.symm.trans ha.1,hab⟩
  · exact Or.inr ⟨ha.1.symm.trans hb.1,hba⟩

/-- An incomparable root and every one of its descendants are untouched. -/
theorem not_below_extension {w : ℕ} {a b : Fin w × Path}
    (hab : ¬ Below a b) (hba : ¬ Below b a) (p : Path) : ¬ Below a (addrExt b p) := by
  intro h
  exact (below_comparable h (below_extend b p)).elim hab hba

/-- Source relocation leaves every address outside the inserted subtree unchanged. -/
theorem relocate_eq_of_not_below (a : Fin 2 × Path) (c l : Fin 3) (z : Fin 2 × Path)
    (h : ¬ Below a z) : RawCpl.relocate a c l z = z := by
  dsimp only [Below] at h
  rw [RawCpl.relocate,ite_eq_right h]

/-- Below a descendant root, relocation is a fixed prefix change. -/
theorem relocate_respects_desc (a b : Fin 2 × Path) (c l : Fin 3) (h : Below a b) :
    RespectsAt (RawCpl.relocate a c l) b := by
  intro p
  have he : Below a (addrExt b p) := below_trans h (below_extend b p)
  dsimp only [Below] at h he
  rw [RawCpl.relocate,ite_eq_left he,RawCpl.relocate,ite_eq_left h]
  obtain ⟨r,hr⟩ := h.2
  simp only [addrExt]
  rw [← hr]
  simp only [List.append_assoc,List.drop_left]

/-- Below an incomparable root, relocation is the identity on its full represented subtree. -/
theorem relocate_respects_incomparable (a b : Fin 2 × Path) (c l : Fin 3)
    (hab : ¬ Below a b) (hba : ¬ Below b a) : RespectsAt (RawCpl.relocate a c l) b := by
  intro p
  rw [relocate_eq_of_not_below _ _ _ _ (not_below_extension hab hba p),
    relocate_eq_of_not_below _ _ _ _ hab]

/-- Every moved address remains below the insertion node. -/
theorem relocate_below (a z : Fin 2 × Path) (c l : Fin 3) (h : Below a z) :
    Below a (RawCpl.relocate a c l z) := by
  dsimp only [Below] at h
  rw [RawCpl.relocate,ite_eq_left h]
  refine ⟨h.1,?_⟩
  change a.2 <+: (a.2 ++ [c,l]) ++ z.2.drop a.2.length
  rw [List.append_assoc]
  exact List.prefix_append _ _

/-- Inserting two path slots is injective on the entire raw address space. -/
theorem relocate_injective (a : Fin 2 × Path) (c l : Fin 3) :
    Function.Injective (RawCpl.relocate a c l) := by
  intro x y hxy
  by_cases hx : Below a x
  · by_cases hy : Below a y
    · dsimp only [Below] at hx hy
      have hp := congrArg Prod.snd hxy
      rw [RawCpl.relocate,ite_eq_left hx,RawCpl.relocate,ite_eq_left hy] at hp
      obtain ⟨r,hr⟩ := hx.2
      obtain ⟨s,hs⟩ := hy.2
      change (a.2 ++ [c,l]) ++ x.2.drop a.2.length =
        (a.2 ++ [c,l]) ++ y.2.drop a.2.length at hp
      rw [← hr,← hs] at hp
      simp only [List.drop_left] at hp
      have hrs := List.append_cancel_left hp
      apply Prod.ext (hx.1.trans hy.1.symm)
      rw [← hr,← hs,hrs]
    · have hb := relocate_below a x c l hx
      rw [hxy,relocate_eq_of_not_below a c l y hy] at hb
      exact (hy hb).elim
  · by_cases hy : Below a y
    · have hb := relocate_below a y c l hy
      rw [← hxy,relocate_eq_of_not_below a c l x hx] at hb
      exact (hx hb).elim
    · rw [relocate_eq_of_not_below a c l x hx,relocate_eq_of_not_below a c l y hy] at hxy
      exact hxy

end WaveTurbulence.Reg
