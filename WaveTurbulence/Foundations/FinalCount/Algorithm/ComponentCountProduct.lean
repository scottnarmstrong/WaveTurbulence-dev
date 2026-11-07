/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ComponentCountUpper
import Mathlib.Tactic

/-! # Exact multiplicativity for independent component restrictions -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem component_countE_product (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (A1 : (AppbSideDart M S → (Fin d → ℤ)) → Prop)
    (A2 : (AppbSideDart M (M.atoms \ S) → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w (appbSeparatedAdmissibility M S A1 A2) =
      appbCountE (appbSideMolecule M S hS) L γ δ w A1*
        appbCountE (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w A2 := by
  apply le_antisymm
  · have hupper := component_countE_upper M S hS L γ δ w (appbSeparatedAdmissibility M S A1 A2)
    have h1 : appbCountE (appbSideMolecule M S hS) L γ δ w
        (appbSideAdmissibility M S (appbSeparatedAdmissibility M S A1 A2)) ≤
        appbCountE (appbSideMolecule M S hS) L γ δ w A1 := by
      apply appbCountE_mono
      intro ζ hζ
      obtain ⟨κ,hκ,he⟩ := hζ
      exact he ▸ hκ.1
    have h2 : appbCountE (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w
        (appbSideAdmissibility M (M.atoms \ S) (appbSeparatedAdmissibility M S A1 A2)) ≤
        appbCountE (appbSideMolecule M (M.atoms \ S) hS.complement) L γ δ w A2 := by
      apply appbCountE_mono
      intro ζ hζ
      obtain ⟨κ,hκ,he⟩ := hζ
      exact he ▸ hκ.2
    exact hupper.trans (mul_le_mul h1 h2 (by exact bot_le) (by exact bot_le))
  · exact appb_component_product_le M S hS hL γ δ w A1 A2

end WaveTurbulence.Mole.AppbAlgorithm
