/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCounting
public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
import Mathlib.Tactic

/-! # Uniform finiteness and actual parameter fibers in Appendix B -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- All fixed counting parameters; arbitrary degree-four sources are allowed. -/
structure AppbCountParameters (M : Molecule V D) (d : ℕ) where
  momentum : V → Mom d
  energy : V → ℝ
  center : D → Mom d
  center_mate : ∀ x, center (M.mate x) = center x

noncomputable instance appbCountParameters_inhabited (M : Molecule V D) (d : ℕ) :
    Inhabited (AppbCountParameters M d) :=
  ⟨⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => rfl⟩⟩

/-- The actual restricted decorations for one parameter fiber. -/
def AppbCountParameters.decorations {M : Molecule V D} {d : ℕ} (p : AppbCountParameters M d)
    (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) : Set (D → (Fin d → ℤ)) :=
  {κ | M.IsDecoration L w p.momentum κ ∧ M.IsRestricted L γ δ w p.energy p.center κ ∧ Adm κ}

/-- Every fiber is bounded by the accepted coordinate-box estimate. -/
theorem appbCountE_le_box (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w Adm ≤ (⌈2*L+1⌉₊ : ℕ∞)^(d*Fintype.card D) := by
  unfold appbCountE
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  exact (Set.encard_mono (fun _κ h => h.2.1)).trans (restricted_encard_le M hL γ δ w β k0)

theorem appbCountE_ne_top (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w Adm ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (appbCountE_le_box M hL γ δ w Adm)

/-- The bundled parameter API is definitionally faithful to the supremum. -/
theorem appbCountE_eq_iSup (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    appbCountE M L γ δ w Adm = ⨆ p : AppbCountParameters M d, (p.decorations L γ δ w Adm).encard := by
  unfold appbCountE AppbCountParameters.decorations
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
    exact le_iSup_of_le ⟨c,β,k0,hk0⟩ le_rfl
  · apply iSup_le
    intro p
    exact le_iSup_of_le p.momentum <| le_iSup_of_le p.energy <|
      le_iSup_of_le p.center <| le_iSup_of_le p.center_mate le_rfl

/-- A worst counting fiber exists at an actual choice of parameters.
This uses the proved uniform finite bound, not a compactness assumption. -/
theorem appbCountE_attained (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ p : AppbCountParameters M d, (p.decorations L γ δ w Adm).encard = appbCountE M L γ δ w Adm := by
  rw [appbCountE_eq_iSup]
  apply ENat.exists_eq_iSup_of_lt_top
  rw [← appbCountE_eq_iSup]
  exact lt_top_iff_ne_top.mpr (appbCountE_ne_top M hL γ δ w Adm)

end WaveTurbulence.Mole
