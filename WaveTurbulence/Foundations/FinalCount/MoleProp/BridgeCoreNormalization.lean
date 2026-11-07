/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeCoreCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeCore
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleNormalization
import Mathlib.Tactic

/-! # Full neutral normalized bridge removal in DH23 Proposition 10.3 -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_bridgeCore_le (M : Molecule V D)
    {a b : V} (hab : a ≠ b) :
    (bridgeCore M).bondsBetween a b ≤ M.bondsBetween a b := by
  classical
  have hsub : ((Degen.neighborDarts (bridgeCore M) a b).image
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

theorem simple_bridgeCore (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ∀ a b, a ≠ b → (bridgeCore M).bondsBetween a b ≤ 1 := by
  intro a b hab
  exact (bondsBetween_bridgeCore_le M hab).trans (hsimple a b hab)

theorem largeGap_bridgeCore (M : Molecule V D) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)}
    (h : LargeGap M L γ η w κ) :
    LargeGap (bridgeCore M) L γ η w (fun x => κ x.val) := by
  intro x y hxy hdir
  exact h x.val y.val hxy hdir

theorem bridgeCoreAdmissibility_largeGap (M : Molecule V D) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → LargeGap M L γ η w κ) :
    ∀ κ, bridgeCoreAdmissibility M Adm κ → LargeGap (bridgeCore M) L γ η w κ := by
  intro κ hκ
  obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
  exact largeGap_bridgeCore M L γ η w (hAdm κ0 h0)

theorem countAFree_le_bridgeCore (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤
      countAFree (bridgeCore M) L γ δ C1 w (bridgeCoreAdmissibility M Adm) P := by
  rw [countAFree_eq_of_simple M hsimple,countAFree_eq_of_simple _ (simple_bridgeCore M hsimple),
    (bridgeCore_bridgefree_and_circuitRank M).2]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono
    (countEFree_le_bridgeCore M hL γ δ w Adm)) bot_le

end WaveTurbulence.MoleProp
