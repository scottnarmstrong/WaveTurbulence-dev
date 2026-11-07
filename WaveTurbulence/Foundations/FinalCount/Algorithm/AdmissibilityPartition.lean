/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinks
import Mathlib.Tactic

/-! # Counting both branches of an actual decoration test

The conservation centers are maximized independently in each branch.
Neither finite cardinality nor positivity of a normalizing factor is
required. This is the partition used for source 3S3 and 3D3 label tests.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem countE_le_admissibility_cover (M : Molecule V D) {d : ℕ}
    (L γ δ : ℝ) (w : Mom d) (Adm A B : (D → (Fin d → ℤ)) → Prop)
    (hcover : ∀ κ,Adm κ → A κ ∨ B κ) :
    appbCountE M L γ δ w Adm ≤ appbCountE M L γ δ w A+appbCountE M L γ δ w B := by
  unfold appbCountE
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let S := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ A κ}
  let T := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ B κ}
  have hsub : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} ⊆ S ∪ T := by
    intro κ hκ
    rcases hcover κ hκ.2.2 with h | h
    · exact Or.inl ⟨hκ.1,hκ.2.1,h⟩
    · exact Or.inr ⟨hκ.1,hκ.2.1,h⟩
  refine (Set.encard_mono hsub).trans ((Set.encard_union_le S T).trans (add_le_add ?_ ?_))
  · exact le_iSup_of_le c (le_iSup_of_le β (le_iSup_of_le k0 (le_iSup_of_le hk0 le_rfl)))
  · exact le_iSup_of_le c (le_iSup_of_le β (le_iSup_of_le k0 (le_iSup_of_le hk0 le_rfl)))

theorem linkCountA_le_admissibility_cover (M : Molecule V D) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm A B : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hcover : ∀ κ,Adm κ → A κ ∨ B κ) :
    appbLinkCountA M L γ δ C1 w Adm P ≤
      appbLinkCountA M L γ δ C1 w A P+appbLinkCountA M L γ δ C1 w B P := by
  have hh := ENat.toENNReal_mono (countE_le_admissibility_cover M L γ δ w Adm A B hcover)
  rw [ENat.toENNReal_add] at hh
  unfold appbLinkCountA
  exact (mul_le_mul_left hh _).trans_eq (add_mul _ _ _)

/-- The exact binary partition into passing and failing label tests.
Both branches retain every previous admissibility constraint. -/
theorem linkCountA_le_test_partition (M : Molecule V D) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm Test : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) :
    appbLinkCountA M L γ δ C1 w Adm P ≤
      appbLinkCountA M L γ δ C1 w (fun κ => Adm κ ∧ Test κ) P+
      appbLinkCountA M L γ δ C1 w (fun κ => Adm κ ∧ ¬Test κ) P := by
  classical
  apply linkCountA_le_admissibility_cover
  intro κ hκ
  by_cases ht : Test κ
  · exact Or.inl ⟨hκ,ht⟩
  · exact Or.inr ⟨hκ,ht⟩

end WaveTurbulence.Mole.AppbAlgorithm
