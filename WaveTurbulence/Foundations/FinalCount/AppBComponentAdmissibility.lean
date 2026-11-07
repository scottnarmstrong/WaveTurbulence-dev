/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentProduct
import Mathlib.Tactic

/-! # Explicit component projection hull of an admissibility predicate

The hull records precisely the weakening to independent component tests.
It is not identified with an arbitrary cross-component predicate.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbSideAdmissibility (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) (ζ : AppbSideDart M S → (Fin d → ℤ)) : Prop :=
  ∃ κ, A κ ∧ appbSideLabels M S κ = ζ

def appbComponentHull (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) : (D → (Fin d → ℤ)) → Prop :=
  appbSeparatedAdmissibility M S (appbSideAdmissibility M S A)
    (appbSideAdmissibility M (M.atoms \ S) A)

theorem appb_mem_componentHull (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) {κ : D → (Fin d → ℤ)} (hκ : A κ) :
    appbComponentHull M S A κ := ⟨⟨κ,hκ,rfl⟩,⟨κ,hκ,rfl⟩⟩

/-- Every test depending only on one side survives the hull. -/
theorem appb_componentHull_preserves_left (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop)
    (T : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (hT : ∀ κ,A κ → T (appbSideLabels M S κ))
    {κ : D → (Fin d → ℤ)} (hκ : appbComponentHull M S A κ) :
    T (appbSideLabels M S κ) := by
  obtain ⟨κ',hA,he⟩ := hκ.1
  rw [← he]
  exact hT κ' hA

theorem appb_componentHull_preserves_right (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop)
    (T : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop)
    (hT : ∀ κ,A κ → T (appbSideLabels M (M.atoms \ S) κ))
    {κ : D → (Fin d → ℤ)} (hκ : appbComponentHull M S A κ) :
    T (appbSideLabels M (M.atoms \ S) κ) := by
  obtain ⟨κ',hA,he⟩ := hκ.2
  rw [← he]
  exact hT κ' hA

/-- Already separated component tests are unchanged by projection and
recombination. No cross-component compatibility is silently discarded. -/
theorem appb_componentHull_separated_iff (M : Molecule V D) (S : Finset V) {d : ℕ}
    (A1 : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (A2 : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop)
    (κ : D → (Fin d → ℤ)) :
    appbComponentHull M S (appbSeparatedAdmissibility M S A1 A2) κ ↔
      appbSeparatedAdmissibility M S A1 A2 κ := by
  constructor
  · intro hκ
    obtain ⟨κ1,h1,he1⟩ := hκ.1
    obtain ⟨κ2,h2,he2⟩ := hκ.2
    exact ⟨he1 ▸ h1.1,he2 ▸ h2.2⟩
  · exact appb_mem_componentHull M S _

/-- Product realization uses the explicitly named hull, not the possibly
stronger original admissibility predicate. -/
theorem appb_component_projection_product_le (M : Molecule V D) (S : Finset V)
    (h : AppbClosedSide M S) {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) :
    appbCountE (appbSideMolecule M S h) L γ δ w (appbSideAdmissibility M S A)*
      appbCountE (appbSideMolecule M (M.atoms \ S) h.complement) L γ δ w
        (appbSideAdmissibility M (M.atoms \ S) A) ≤
      appbCountE M L γ δ w (appbComponentHull M S A) :=
  appb_component_product_le M S h hL γ δ w _ _

end WaveTurbulence.Mole
