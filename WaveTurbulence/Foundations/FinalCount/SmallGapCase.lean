/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.SixTuple
public import WaveTurbulence.Foundations.FinalCount.SmallStars
import Mathlib.Tactic

/-! # One case of the small-gap count: the extra dart `ex` at `v₁` and `ey` at `v₂` with `‖k_ex − σ k_ey‖ ≤ λ` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem doubleSign_pm (b : Bool) : doubleSign b = 1 ∨ doubleSign b = -1 := by
  cases b <;> simp [doubleSign]

theorem doubleSign_eq_iff (a b : Bool) : doubleSign a = doubleSign b ↔ a = b := by
  cases a <;> cases b <;> simp [doubleSign]

theorem quad_not_three (M : Molecule V D) (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {v : V}
    (hv : v ∈ M.atoms) {p q r s : D} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hs : s ∉ ({p, q, r} : Finset D))
    (hstar : M.dartsAt v = {p, q, r, s}) : ¬ (M.out p = M.out q ∧ M.out q = M.out s) := by
  have ho := (hcap v hv).1
  have hi := (hcap v hv).2
  rw [outdeg_quad' M v hpq hpr hqr hs hstar] at ho
  rw [indeg_quad' M v hpq hpr hqr hs hstar] at hi
  cases hp : M.out p <;> cases hq : M.out q <;> cases hr : M.out r <;> cases hs' : M.out s <;> simp_all

theorem smallgap_case_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ lam : ℝ, 0 ≤ lam →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms)
      {x y ex ex' ey ey' : D} (hxy : x ≠ y) (hxe : x ≠ ex) (hxe' : x ≠ ex') (hye : y ≠ ex) (hye' : y ≠ ex')
      (hee : ex ≠ ex') (hmxy : M.mate x ≠ M.mate y) (hmxf : M.mate x ≠ ey) (hmxf' : M.mate x ≠ ey')
      (hmyf : M.mate y ≠ ey) (hmyf' : M.mate y ≠ ey') (hff : ey ≠ ey')
      (hA : M.dartsAt v₁ = {x, y, ex, ex'}) (hB : M.dartsAt v₂ = {M.mate x, M.mate y, ey, ey'})
      (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
      (S : Finset (D → Fin d → ℤ))
      (hS : ∀ κ ∈ S, M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧
        ‖latticePoint L (κ ex) - (σ : ℝ) • latticePoint L (κ ey)‖ ≤ lam),
      ((S.image (localLabels M ![x, y, ex, ex', ey, ey'])).card : ℝ) ≤
        (2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by
  classical
  obtain ⟨C, L₀, hC, h⟩ := sixTuple_card_le d hd γ hγ
  refine ⟨C, max L₀ 1, hC, fun L hL δ hδ lam hlam V D _ _ _ M hcap v₁ v₂ hv₁ hv₂ x y ex ex' ey ey' hxy hxe hxe' hye hye'
    hee hmxy hmxf hmxf' hmyf hmyf' hff hA hB σ hσ c β k0 S hS => ?_⟩
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  by_cases hSe : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hSe]
    simp only [image_empty, card_empty, Nat.cast_zero]
    have := hδ.1
    positivity
  obtain ⟨κ0, hκ0⟩ := hSe
  have htA : ex' ∉ ({x, y, ex} : Finset D) := by simp [hxe'.symm, hye'.symm, hee.symm]
  have htB : ey' ∉ ({M.mate x, M.mate y, ey} : Finset D) := by simp [hmxf'.symm, hmyf'.symm, hff.symm]
  have hcapA := quad_not_three M hcap hv₁ hxy hxe hye htA hA
  have hcapB := hcap v₂ hv₂
  have hne : ¬ (doubleSign (M.out x) = doubleSign (M.out y) ∧ doubleSign (M.out y) = doubleSign (M.out ex')) := by
    intro ⟨h1, h2⟩
    exact hcapA ⟨(doubleSign_eq_iff _ _).mp h1, (doubleSign_eq_iff _ _).mp h2⟩
  let n1 : Fin d → ℤ := doubleSign (M.out x) • κ0 x + doubleSign (M.out y) • κ0 y + doubleSign (M.out ex) • κ0 ex +
    doubleSign (M.out ex') • κ0 ex'
  let n2 : Fin d → ℤ := -(doubleSign (M.out x) • κ0 x) - doubleSign (M.out y) • κ0 y +
    doubleSign (M.out ey) • κ0 ey + doubleSign (M.out ey') • κ0 ey'
  let cen : Fin 6 → Mom d := ![k0 x, k0 y, k0 ex, k0 ex', k0 ey, k0 ey']
  have hmain := h L hLL δ hδ lam hlam (doubleSign (M.out x)) (doubleSign (M.out y)) (doubleSign (M.out ex))
    (doubleSign (M.out ex')) (doubleSign (M.out ey)) (doubleSign (M.out ey')) σ (doubleSign_pm _) (doubleSign_pm _)
    (doubleSign_pm _) (doubleSign_pm _) hne hσ cen n1 n2 (β v₁) (S.image (localLabels M ![x, y, ex, ex', ey, ey'])) (by
    intro q hq
    obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hq
    obtain ⟨hdec, hres, hgap⟩ := hS κ hκ
    obtain ⟨hdec0, _, _⟩ := hS κ0 hκ0
    have hmA := momentum_of_dartsAt_quadruple M L hv₁ hxy hxe hye htA hA hdec
    have hm0A := momentum_of_dartsAt_quadruple M L hv₁ hxy hxe hye htA hA hdec0
    have hmB := momentum_of_dartsAt_quadruple M L hv₂ hmxy hmxf hmyf htB hB hdec
    have hm0B := momentum_of_dartsAt_quadruple M L hv₂ hmxy hmxf hmyf htB hB hdec0
    have hEA := energy_of_dartsAt_quadruple M L γ δ hv₁ hxy hxe hye htA hA hres
    refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
    · have hnl : ∀ j : D, NearLattice L (k0 j) (κ j) := fun j =>
        (by simpa only [Molecule.kvec, zero_add] using hres.2 j : ‖latticePoint L (κ j) - k0 j‖ ≤ 1)
      fin_cases i <;> exact hnl _
    · apply latticePointHom_injective hLp.ne'
      simp only [n1, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul, localLabels,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
      exact hmA.trans hm0A.symm
    · simpa [localLabels, doubleSign_out_cast] using hEA
    · apply latticePointHom_injective hLp.ne'
      rw [hdec.1 x, hdec.1 y] at hmB
      rw [hdec0.1 x, hdec0.1 y] at hm0B
      simp only [Degen.dartSign_mate] at hmB hm0B
      simp only [n2, map_add, map_sub, map_neg, map_zsmul, latticePointHom_apply, doubleSign_out_smul, localLabels]
      have e0 : (![x, y, ex, ex', ey, ey'] : Fin 6 → D) 0 = x := rfl
      have e1 : (![x, y, ex, ex', ey, ey'] : Fin 6 → D) 1 = y := rfl
      have e4 : (![x, y, ex, ex', ey, ey'] : Fin 6 → D) 4 = ey := rfl
      have e5 : (![x, y, ex, ex', ey, ey'] : Fin 6 → D) 5 = ey' := rfl
      rw [e0, e1, e4, e5]
      linear_combination (norm := module) hmB - hm0B
    · simpa [localLabels, cen] using hgap)
  exact hmain

end WaveTurbulence.FinalCountG8
