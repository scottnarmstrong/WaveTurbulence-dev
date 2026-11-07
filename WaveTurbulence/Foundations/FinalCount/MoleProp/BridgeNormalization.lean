/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeComponents
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleNormalization
import Mathlib.Tactic

/-! # Full neutral normalized bridge removal in DH23 Proposition 10.3 -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_eraseBond_le (M : Molecule V D) (e : D)
    {a b : V} (hab : a ≠ b) :
    (eraseBond M e).bondsBetween a b ≤ M.bondsBetween a b := by
  classical
  have hsub : ((Degen.neighborDarts (eraseBond M e) a b).image
      (fun x => x.val)) ⊆ Degen.neighborDarts M a b := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨hya,hyb⟩ := mem_filter.mp hy
    apply mem_filter.mpr
    exact ⟨(Mole.mem_dartsAt M a y.val).mpr ((Mole.mem_dartsAt _ a y).mp hya),hyb⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ Subtype.val_injective,
    Degen.card_neighborDarts _ hab,Degen.card_neighborDarts _ hab] at hh
  exact hh

theorem simple_eraseBond (M : Molecule V D) (e : D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ∀ a b, a ≠ b → (eraseBond M e).bondsBetween a b ≤ 1 := by
  intro a b hab
  exact (bondsBetween_eraseBond_le M e hab).trans (hsimple a b hab)

theorem largeGap_eraseBond (M : Molecule V D) (e : D) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)}
    (h : LargeGap M L γ η w κ) :
    LargeGap (eraseBond M e) L γ η w (fun x => κ x.val) := by
  intro x y hxy hdir
  exact h x.val y.val hxy hdir

theorem erasedBondAdmissibility_largeGap (M : Molecule V D) (e : D) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ) :
    ∀ κ, erasedBondAdmissibility M e Adm κ → LargeGap (eraseBond M e) L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact largeGap_eraseBond M e L γ η w (hAdm κ0 h0)

theorem countAFree_le_erase_bridge (M : Molecule V D) (e : D) (he : Degen.IsBridge M e)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤
      countAFree (eraseBond M e) L γ δ C1 w (erasedBondAdmissibility M e Adm) P := by
  rw [countAFree_eq_of_simple M hsimple,countAFree_eq_of_simple _ (simple_eraseBond M e hsimple),
    circuitRank_eraseBond_eq M e he]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono
    (countEFree_le_erase_bridge M e he hL γ δ w Adm)) bot_le

end WaveTurbulence.MoleProp
