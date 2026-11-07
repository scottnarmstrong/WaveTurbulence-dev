/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceIP
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), B: the degree of a crown joint of the residual vine

For the skipped vine `A` with joints `x, y` of a decomposed group (`S = L0 ∪ A ∪ R0`, runs collapsed), the
residual joint `π x` has degree at most that of the end joint `a` of the group in the original molecule
(`π y` at most `b`): the external bonds of the collapsed run are the `deg a - 2` external bonds of `a` and the
two bonds of `x` in `A`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V0 V1 D0 D1 : Type*} [DecidableEq V0] [Fintype D0] [DecidableEq D0]
  [DecidableEq V1] [Fintype D1] [DecidableEq D1]
  {N0 : Molecule V0 D0} {N1 : Molecule V1 D1} {cls : V0 → Option V0} {S A L0 R0 : Finset V0}
  {a b x y : V0}

theorem SDecomp.deg_x_le (H : SDecomp N0 cls S A L0 R0 a b x y) (M : SpMol N0 N1 cls) :
    N1.deg (M.pi x) ≤ N0.deg a := by
  classical
  -- every dart at `π x` is sent by `od` to a dart at an atom of the class of `x`
  have hcl : ∀ d : D1, N1.atom d = M.pi x → ((cls (N0.atom (M.od d))).getD (N0.atom (M.od d)) =
      (cls x).getD x) := by
    intro d hd
    rw [← M.ob_atom, hd, M.ob_pi]
  have hnc : ∀ d : D1, ¬ ∃ r, cls (N0.atom (M.od d)) = some r ∧ cls (N0.atom (N0.mate (M.od d))) = some r :=
    fun d => (M.od_range (M.od d)).mp ⟨d, rfl⟩
  by_cases hL : L0 = ∅
  · -- `x = a`, unmerged
    have hxa : x = a := by
      rcases H.hL with ⟨_, h⟩ | ⟨_, _, hi⟩
      · exact h
      · exfalso
        have : x ∈ L0 ∩ A := by rw [hi]; exact mem_singleton_self _
        rw [hL] at this; simp at this
    unfold Molecule.deg
    rw [← hxa]
    apply Finset.card_le_card_of_injOn M.od
    · intro d hd
      simp only [Molecule.dartsAt, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd ⊢
      rcases H.classx (hcl d hd) with ⟨hxL, _⟩ | ⟨_, h⟩
      · rw [hL] at hxL; simp at hxL
      · exact h
    · exact fun d _ d' _ h => M.od_inj h
  · obtain ⟨hxa, hLB, hi⟩ : x ≠ a ∧ N0.IsBlock L0 a x ∧ L0 ∩ A = {x} := by
      rcases H.hL with ⟨h, _⟩ | h
      · exact absurd h hL
      · exact h
    have hxL := H.xL hL
    have haL : a ∈ L0 := hLB.2.1
    -- external darts of the run
    let Tset : Finset D0 := (N0.dartsAt a).filter (fun d => ¬ N0.InGroup L0 d) ∪
      (N0.dartsAt x).filter (fun d => ¬ N0.InGroup L0 d)
    have hinj : N1.deg (M.pi x) ≤ Tset.card := by
      unfold Molecule.deg
      apply Finset.card_le_card_of_injOn M.od
      · intro d hd
        simp only [Molecule.dartsAt, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd
        have hpL : N0.atom (M.od d) ∈ L0 := by
          rcases H.classx (hcl d hd) with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd hxL h
        have hext : ¬ N0.InGroup L0 (M.od d) := by
          intro hg
          exact hnc d (H.classInt_L hg)
        by_cases hpa : N0.atom (M.od d) = a
        · rw [Finset.mem_coe]
          simp only [Tset, Finset.mem_union, Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and]
          exact Or.inl ⟨hpa, hext⟩
        · by_cases hpx : N0.atom (M.od d) = x
          · rw [Finset.mem_coe]
            simp only [Tset, Finset.mem_union, Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and]
            exact Or.inr ⟨hpx, hext⟩
          · exact absurd (allInt H.mol hLB hpL hpa hpx rfl) hext
      · exact fun d _ d' _ h => M.od_inj h
    refine hinj.trans ?_
    -- count
    have hda : ((N0.dartsAt a).filter (fun d => ¬ N0.InGroup L0 d)).card + 2 = N0.deg a := by
      have h1 := Finset.card_filter_add_card_filter_not (s := N0.dartsAt a) (fun d => N0.InGroup L0 d)
      have h2 : N0.degIn L0 a = 2 := (block_joint_degrees N0 hLB).1
      unfold Molecule.degIn at h2
      unfold Molecule.deg
      omega
    have hdx : ((N0.dartsAt x).filter (fun d => ¬ N0.InGroup L0 d)).card ≤ 2 := by
      have h1 := Finset.card_filter_add_card_filter_not (s := N0.dartsAt x) (fun d => N0.InGroup L0 d)
      have h2 : N0.degIn L0 x = 2 := (block_joint_degrees N0 hLB).2
      have h3 : N0.deg x ≤ 4 := deg_le_four N0 H.mol (H.hLsub hxL |> fun h => H.hSB.1 h)
      unfold Molecule.degIn at h2
      unfold Molecule.deg at h3
      omega
    calc Tset.card ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ N0.deg a := by omega

theorem SDecomp.deg_y_le (H : SDecomp N0 cls S A L0 R0 a b x y) (M : SpMol N0 N1 cls) :
    N1.deg (M.pi y) ≤ N0.deg b :=
  H.symm.deg_x_le M

end WaveTurbulence.RedSplice
