/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeCount
public import WaveTurbulence.Foundations.FinalCount.SmallStars
public import WaveTurbulence.Foundations.FinalCount.Pair33Count
import Mathlib.Tactic

/-! # The fibres of the restriction to the merged molecule (DH23 Lemma A.3(1))

Two decorations of `M` with the same restriction to `merge M` differ only on the double bond `v₁ = v₂`; its labels
`(p₁, p₂)` solve the conservation law and the energy window at `v₁` with the other labels of `v₁` fixed: a point of
`atomPairSet`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V}

/-- **The fibre injects into an `atomPairSet`.** -/
theorem fiber_subset_pairSet {d : ℕ} {L γ δ : ℝ} (hLp : 0 < L) (hv₁ : v₁ ∈ M.atoms)
    {x y r₁ r₂ : D} (hxy : x ≠ y) (hxr₁ : x ≠ r₁) (hxr₂ : x ≠ r₂) (hyr₁ : y ≠ r₁) (hyr₂ : y ≠ r₂) (hrr : r₁ ≠ r₂)
    (hA : M.dartsAt v₁ = {x, y, r₁, r₂})
    (hpair : ∀ z, M.ends z = s(v₁, v₂) → z = x ∨ z = y ∨ z = M.mate x ∨ z = M.mate y)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ₀ : D → (Fin d → ℤ))
    (hdec₀ : M.IsDecoration L (0 : Mom d) c κ₀) :
    let ε : ℤˣ := sgn M x * sgn M y
    let nk : Fin d → ℤ := (sgn M x : ℤ) • (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y)
    let β₂ : ℝ := (doubleSign (M.out x) : ℝ) * (β v₁ - (M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 +
      M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2))
    ∀ κ, (M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ) →
      (κ r₁ = κ₀ r₁ ∧ κ r₂ = κ₀ r₂) →
      (κ x, κ y) ∈ atomPairSet L (k0 x) (k0 y) nk β₂ (δ⁻¹ * L ^ (-2 * γ)) ε := by
  intro ε nk β₂ κ ⟨hdec, hres⟩ ⟨e1, e2⟩
  have htA : r₂ ∉ ({x, y, r₁} : Finset D) := by simp [hxr₂.symm, hyr₂.symm, hrr.symm]
  have hm := momentum_of_dartsAt_quadruple M L hv₁ hxy hxr₁ hyr₁ htA hA hdec
  have hm0 := momentum_of_dartsAt_quadruple M L hv₁ hxy hxr₁ hyr₁ htA hA hdec₀
  have hE := energy_of_dartsAt_quadruple M L γ δ hv₁ hxy hxr₁ hyr₁ htA hA hres
  rw [e1, e2] at hm hE
  have hmain : doubleSign (M.out x) • κ x + doubleSign (M.out y) • κ y =
      doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y := by
    apply latticePointHom_injective hLp.ne'
    simp only [map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
    have := hm.trans hm0.symm
    linear_combination (norm := module) this
  have hsq : ∀ z : D, M.dartSign z * M.dartSign z = 1 := fun z => by
    unfold Molecule.dartSign; cases M.out z <;> norm_num
  have hsx : (sgn M x : ℤ) * (sgn M x : ℤ) = 1 := by
    rw [sgn_cast]; unfold doubleSign; cases M.out x <;> norm_num
  have hnl : ∀ j : D, NearLattice L (k0 j) (κ j) := fun j =>
    (by simpa only [Molecule.kvec, zero_add] using hres.2 j : ‖latticePoint L (κ j) - k0 j‖ ≤ 1)
  refine ⟨hnl x, hnl y, ?_, ?_⟩
  · show κ x + (((sgn M x * sgn M y : ℤˣ) : ℤ)) • κ y = (sgn M x : ℤ) • (doubleSign (M.out x) • κ₀ x + doubleSign (M.out y) • κ₀ y)
    rw [← hmain, smul_add, smul_smul, smul_smul, ← sgn_cast, ← sgn_cast, hsx, Units.val_mul, one_smul]
  · show |‖latticePoint L (κ x)‖ ^ 2 + (((sgn M x * sgn M y : ℤˣ) : ℤ) : ℝ) * ‖latticePoint L (κ y)‖ ^ 2 -
      (doubleSign (M.out x) : ℝ) * (β v₁ - (M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 +
        M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2))| ≤ _
    have hx := doubleSign_out_cast M x
    have hy := doubleSign_out_cast M y
    have key : ‖latticePoint L (κ x)‖ ^ 2 + (((sgn M x * sgn M y : ℤˣ) : ℤ) : ℝ) * ‖latticePoint L (κ y)‖ ^ 2 -
        (doubleSign (M.out x) : ℝ) * (β v₁ - (M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 +
          M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2)) =
        (M.dartSign x) * (M.dartSign x * ‖latticePoint L (κ x)‖ ^ 2 + M.dartSign y * ‖latticePoint L (κ y)‖ ^ 2 +
          M.dartSign r₁ * ‖latticePoint L (κ₀ r₁)‖ ^ 2 + M.dartSign r₂ * ‖latticePoint L (κ₀ r₂)‖ ^ 2 - β v₁) := by
      rw [Units.val_mul, Int.cast_mul, sgn_cast_real, sgn_cast_real, ← hx]
      have := hsq x
      rw [← hx] at this
      linear_combination (-(‖latticePoint L (κ x)‖ ^ 2)) * this
    rw [key, abs_mul]
    have habs : |M.dartSign x| = 1 := by unfold Molecule.dartSign; cases M.out x <;> norm_num
    rw [habs, one_mul]
    exact hE

end MergeSum
end WaveTurbulence.FinalCountG8
