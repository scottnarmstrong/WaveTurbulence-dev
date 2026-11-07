/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairTables
public import WaveTurbulence.Foundations.FinalCount.AppBPairReconstruction
import Mathlib.Tactic

/-! # Exact central-pair reconstruction in every 2R-3F layout -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset Set
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbR23_open_central {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r23.pattern) :
    AppbLocalPair r (r.vertex 1) :=
  r.pairFromTable 1 (by decide) ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide) (by decide)

def appbR23_open_left {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r23.pattern) :
    AppbLocalPair r (r.vertex 2) :=
  r.pairFromTable 2 (by decide) ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide) (by decide)

def appbR23_open_right {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r23.pattern) :
    AppbLocalPair r (r.vertex 3) :=
  r.pairFromTable 3 (by decide) ⟨1,by decide⟩ ⟨3,by decide⟩ (by decide) (by decide)

/-- Actual label reconstruction for the open 2R-3F layout. -/
theorem appb_r23_open_projection_injective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r23.pattern)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbR23_open_central r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  let leaves : Fin 2 → Σ a : V,AppbLocalPair r a :=
    ![⟨r.vertex 2,appbR23_open_left r⟩,⟨r.vertex 3,appbR23_open_right r⟩]
  apply r.pair_projection_injOn_localChoices (appbR23_open_central r) leaves ?_ ?_ ?_ p hL γ δ w Adm
  · intro j
    fin_cases j
    · exact mem_image_of_mem r.vertex (show 2 ∈ (AppbPatternKind.r23.pattern).removed by decide)
    · exact mem_image_of_mem r.vertex (show 3 ∈ (AppbPatternKind.r23.pattern).removed by decide)
  · intro j
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0,rfl⟩)
    · exact Or.inr (Or.inr ⟨1,rfl⟩)

def appbR23_triangle_central {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r23triangle.pattern) :
    AppbLocalPair r (r.vertex 1) :=
  r.pairFromTable 1 (by decide) ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide) (by decide)

def appbR23_triangle_left {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r23triangle.pattern) :
    AppbLocalPair r (r.vertex 2) :=
  r.pairFromTable 2 (by decide) ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide) (by decide)

/-- Actual label reconstruction for the triangle 2R-3F layout. -/
theorem appb_r23_triangle_projection_injective {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r23triangle.pattern)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbR23_triangle_central r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  let leaves : Fin 1 → Σ a : V,AppbLocalPair r a :=
    fun _ => ⟨r.vertex 2,appbR23_triangle_left r⟩
  apply r.pair_projection_injOn_localChoices (appbR23_triangle_central r) leaves ?_ ?_ ?_ p hL γ δ w Adm
  · intro j
    fin_cases j
    · exact mem_image_of_mem r.vertex (show 2 ∈ (AppbPatternKind.r23triangle.pattern).removed by decide)
  · intro j
    fin_cases j
    · exact Or.inl rfl
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0,rfl⟩)

def appbR23_common_central {M : Molecule V D} (r : AppbRealization M appbR23Common) :
    AppbLocalPair r (r.vertex 1) :=
  r.pairFromTable 1 (by decide) ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide) (by decide)

def appbR23_common_left {M : Molecule V D} (r : AppbRealization M appbR23Common) :
    AppbLocalPair r (r.vertex 2) :=
  r.pairFromTable 2 (by decide) ⟨0,by decide⟩ ⟨2,by decide⟩ (by decide) (by decide)

def appbR23_common_right {M : Molecule V D} (r : AppbRealization M appbR23Common) :
    AppbLocalPair r (r.vertex 3) :=
  r.pairFromTable 3 (by decide) ⟨1,by decide⟩ ⟨3,by decide⟩ (by decide) (by decide)

/-- Actual label reconstruction for the common 2R-3F layout. -/
theorem appb_r23_common_projection_injective {M : Molecule V D}
    (r : AppbRealization M appbR23Common)
    {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbR23_common_central r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  let leaves : Fin 2 → Σ a : V,AppbLocalPair r a :=
    ![⟨r.vertex 2,appbR23_common_left r⟩,⟨r.vertex 3,appbR23_common_right r⟩]
  apply r.pair_projection_injOn_localChoices (appbR23_common_central r) leaves ?_ ?_ ?_ p hL γ δ w Adm
  · intro j
    fin_cases j
    · exact mem_image_of_mem r.vertex (show 2 ∈ (appbR23Common).removed by decide)
    · exact mem_image_of_mem r.vertex (show 3 ∈ (appbR23Common).removed by decide)
  · intro j
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0,rfl⟩)
    · exact Or.inr (Or.inr ⟨1,rfl⟩)

end WaveTurbulence.Mole
