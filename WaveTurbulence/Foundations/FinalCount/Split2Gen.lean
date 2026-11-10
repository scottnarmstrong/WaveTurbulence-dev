/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Iso
import Mathlib.Tactic

/-! # General facts for the decoration-level split (finalcount-g8, F6-1)

* `countAFree_or_le`: counts are subadditive in the admissibility;
* `postGoodOff_largeGap`, `largeGap_relabel`: from the goodness of a multiplier to `LargeGap` of the relabelled post
  decoration.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem countEFree_or_le (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm A B : (D → (Fin d → ℤ)) → Prop) (h : ∀ κ, Adm κ → A κ ∨ B κ) :
    MoleProp.countEFree M L γ δ w Adm ≤ MoleProp.countEFree M L γ δ w A + MoleProp.countEFree M L γ δ w B := by
  unfold MoleProp.countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  refine (Set.encard_mono ?_).trans ((Set.encard_union_le _ _).trans (add_le_add
    (MoleProp.encard_le_countEFree M L γ δ w A c β k0 hk0) (MoleProp.encard_le_countEFree M L γ δ w B c β k0 hk0)))
  intro κ hκ
  rcases h κ hκ.2.2 with h1 | h1
  · exact Or.inl ⟨hκ.1, hκ.2.1, h1⟩
  · exact Or.inr ⟨hκ.1, hκ.2.1, h1⟩

theorem countAFree_or_le (M : Molecule V D) {d : ℕ} (L γ δ C1 : ℝ) (P : Finset V → ℝ)
    (Adm A B : (D → (Fin d → ℤ)) → Prop) (h : ∀ κ, Adm κ → A κ ∨ B κ) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) A P + MoleProp.countAFree M L γ δ C1 (0 : Mom d) B P := by
  rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization,
    MoleProp.countAFree_eq_normalization, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  have := ENat.toENNReal_mono (countEFree_or_le M L γ δ 0 Adm A B h)
  rwa [ENat.toENNReal_add] at this

/-- Goodness of a multiplier, with nothing exempt, is `LargeGap` of the post decoration. -/
theorem postGoodOff_largeGap {N : Molecule V D} (T : TwoExit N) {d : ℕ} {Bs : Finset V} (hBs : Bs \ T.Y = ∅)
    {L γ η' : ℝ} {κ : D → (Fin d → ℤ)} {g : ℤ} (h : T.PostGoodOff Bs L γ η' κ g) :
    MoleProp.LargeGap T.post L γ η' (0 : Mom d) (T.postLabels κ g) := by
  intro x y hxy hdir
  exact h x y hxy (by rw [hBs]; exact notMem_empty _) hdir

end WaveTurbulence.FinalCountG8
