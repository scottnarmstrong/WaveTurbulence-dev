/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Exact prefix insertion for subtree and paired-tree surgery

All source widths and all finite inserted paths are allowed. This includes the
two-slot B relocation and the longer lone paths of regular trees.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Insert the path p immediately below a, retaining every original descendant suffix. -/
def stretch {w : ℕ} (a : Address w) (p : Path) (z : Address w) : Address w :=
  if z.1 = a.1 ∧ a.2 <+: z.2 then (z.1,a.2 ++ p ++ z.2.drop a.2.length) else z

theorem stretch_outside {w : ℕ} (a : Address w) (p : Path) (z : Address w) (hz : ¬ Below a z) :
    stretch a p z = z := by
  dsimp only [Below] at hz
  rw [stretch,ite_eq_right hz]

theorem stretch_below {w : ℕ} (a z : Address w) (p : Path) (hz : Below a z) : Below a (stretch a p z) := by
  dsimp only [Below] at hz
  rw [stretch,ite_eq_left hz]
  refine ⟨hz.1,?_⟩
  change a.2 <+: (a.2 ++ p) ++ z.2.drop a.2.length
  rw [List.append_assoc]
  exact List.prefix_append _ _

/-- Prefix insertion is injective on every raw address, not only leaves. -/
theorem stretch_injective {w : ℕ} (a : Address w) (p : Path) : Function.Injective (stretch a p) := by
  intro x y hxy
  by_cases hx : Below a x
  · by_cases hy : Below a y
    · dsimp only [Below] at hx hy
      have hp := congrArg (fun z : Address w => z.2) hxy
      rw [stretch,ite_eq_left hx,stretch,ite_eq_left hy] at hp
      obtain ⟨r,hr⟩ := hx.2
      obtain ⟨s,hs⟩ := hy.2
      change (a.2 ++ p) ++ x.2.drop a.2.length = (a.2 ++ p) ++ y.2.drop a.2.length at hp
      rw [← hr,← hs] at hp
      simp only [List.drop_left] at hp
      have hrs := List.append_cancel_left hp
      apply Prod.ext (hx.1.trans hy.1.symm)
      rw [← hr,← hs,hrs]
    · have hb := stretch_below a x p hx
      rw [hxy,stretch_outside a p y hy] at hb
      exact (hy hb).elim
  · by_cases hy : Below a y
    · have hb := stretch_below a y p hy
      rw [← hxy,stretch_outside a p x hx] at hb
      exact (hx hb).elim
    · rw [stretch_outside a p x hx,stretch_outside a p y hy] at hxy
      exact hxy

/-- Explicit descendant suffixes are transported by literal concatenation. -/
theorem stretch_frame {w : ℕ} (a : Address w) (p r : Path) :
    stretch a p (addrExt a r) = addrExt a (p++r) := by
  have h : (addrExt a r).1 = a.1 ∧ a.2 <+: (addrExt a r).2 := ⟨rfl,List.prefix_append _ _⟩
  rw [stretch,ite_eq_left h]
  simp only [addrExt,List.drop_left,List.append_assoc]

/-- Every descendant raw address has its actual suffix relative to the upper root. -/
theorem below_exists_frame {w : ℕ} (a x : Address w) (hx : Below a x) : ∃ r : Path, x = addrExt a r := by
  obtain ⟨r,hr⟩ := hx.2
  exact ⟨r,Prod.ext hx.1 hr.symm⟩

/-- If the inserted path preserves the upper sign, every transported node keeps its sign. -/
theorem stretch_sign {w : ℕ} (σ : Fin w → ℤˣ) (a : Address w) (p : Path)
    (hp : pathSign (nodeSign σ a) p = nodeSign σ a) (x : Address w) :
    nodeSign σ (stretch a p x) = nodeSign σ x := by
  by_cases hx : Below a x
  · obtain ⟨r,rfl⟩ := below_exists_frame a x hx
    rw [stretch_frame,nodeSign_addrExt,nodeSign_addrExt,Comb.pathSign_append,hp]
  · rw [stretch_outside a p x hx]

/-- The pinned B relocation is exactly insertion of its continuing and lone slots. -/
theorem relocate_eq_stretch {w : ℕ} (a z : Address w) (c l : Fin 3) :
    relocate a c l z = stretch a [c,l] z := rfl

end WaveTurbulence.Reg.Skeleton
