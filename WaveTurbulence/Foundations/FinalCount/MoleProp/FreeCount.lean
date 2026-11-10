/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
import Mathlib.Tactic

/-! # DH23 section 10.1 counting with unrestricted conservation charges

Unlike TARGET's countE, the conservation parameters at degree-four atoms
are unrestricted in DH23 Propositions 10.1–10.4 (TeX L1829). This literal
supremum retains the same decorations, energy restrictions and bond centers.
-/

@[expose] public section
set_option autoImplicit false
open Set Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 L1829: maximize over every c, without a zero-charge restriction. -/
noncomputable def countEFree (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) : ℕ∞ :=
  ⨆ c : V → Mom d, ⨆ β : V → ℝ, ⨆ k0 : D → Mom d,
    ⨆ (_hk0 : ∀ x, k0 (M.mate x) = k0 x),
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard

/-- The uniform localization bound survives the relaxed conservation law. -/
theorem countEFree_le (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    countEFree M L γ δ w Adm ≤ (⌈2*L+1⌉₊ : ℕ∞)^(d*Fintype.card D) := by
  unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
  exact (Set.encard_mono (fun _ h => h.2.1)).trans (Mole.restricted_encard_le M hL γ δ w β k0)

theorem countEFree_ne_top (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    countEFree M L γ δ w Adm ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (countEFree_le M hL γ δ w Adm)

theorem encard_le_countEFree (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (hk0 : ∀ x, k0 (M.mate x) = k0 x) :
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard ≤
      countEFree M L γ δ w Adm :=
  le_iSup_of_le c (le_iSup_of_le β (le_iSup_of_le k0 (le_iSup_of_le hk0 le_rfl)))

theorem countEFree_mono (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    {Adm Adm' : (D → (Fin d → ℤ)) → Prop} (h : ∀ κ, Adm κ → Adm' κ) :
    countEFree M L γ δ w Adm ≤ countEFree M L γ δ w Adm' := by
  unfold countEFree
  refine iSup_mono fun c => iSup_mono fun β => iSup_mono fun k0 => iSup_mono fun _ => ?_
  exact Set.encard_mono (fun _ hk => ⟨hk.1,hk.2.1,h _ hk.2.2⟩)

/-- Actual large-gap condition at every opposite pair of incident darts. -/
def LargeGap (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ x y : D, M.atom x = M.atom y → M.out x ≠ M.out y →
    L ^ (-γ + η) ≤ ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖

/-- The actual LG constraint is preserved by literal induced erasure. -/
theorem largeGap_erase (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (w : Mom d)
    (Y : Finset V) {κ : D → (Fin d → ℤ)} (h : LargeGap M L γ η w κ) :
    LargeGap (Degen.eraseAtoms M Y) L γ η w (fun x => κ x.val) := by
  intro x y hxy hdir
  exact h x.val y.val hxy hdir

end WaveTurbulence.MoleProp
