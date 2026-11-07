/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitDecor
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Scales
import Mathlib.Tactic

/-! # The transported decoration is restricted, with split energy windows

With `K = 1 + 4|Y|` and `0 ≤ g ≤ 4`, the post energies at `c` and `d` lie within `K τ` of explicit centers; splitting
these two windows into `K` windows of radius `τ` each (`exists_window`) makes the transported labels a restricted
decoration of the post molecule for one of `K²` explicit energy parameters. The new bond's unit-ball center is
`k⁰_y + g R`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- The window factor `K = 1 + 4|Y|`. -/
def windowK : ℕ := 1 + 4 * T.Y.card

/-- The energy center at `c` before splitting. -/
noncomputable def centerC {d : ℕ} (β : V → ℝ) (c : V → Mom d) (g : ℤ) : ℝ :=
  β T.c + (1 - g) * ∑ v ∈ T.Y, β v + g * (1 - g) * ‖T.exitCharge c‖ ^ 2

/-- The energy center at `d` before splitting. -/
noncomputable def centerD {d : ℕ} (β : V → ℝ) (c : V → Mom d) (g : ℤ) : ℝ :=
  β T.d + g * ∑ v ∈ T.Y, β v + g * (g - 1) * ‖T.exitCharge c‖ ^ 2

/-- The split energy parameters of the post molecule. -/
noncomputable def postEnergy {d : ℕ} (β : V → ℝ) (c : V → Mom d) (g : ℤ) (τ : ℝ) (jc jd : ℕ) (v : V) : ℝ :=
  if v = T.c then T.centerC β c g - T.windowK * τ + (2 * jc + 1) * τ
  else if v = T.d then T.centerD β c g - T.windowK * τ + (2 * jd + 1) * τ else β v

/-- The post unit-ball centers. -/
def postCenters {d : ℕ} (k0 : D → Mom d) (c : V → Mom d) (g : ℤ) : Degen.RetainedDart N T.Y ⊕ Bool → Mom d :=
  Sum.elim (fun z => k0 z.val) (fun _ => k0 T.y + (g : ℝ) • T.exitCharge c)

theorem gamma_c_window {d : ℕ} {L γ δ : ℝ} {w : Mom d} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : N.IsDecoration L w c κ) (hres : N.IsRestricted L γ δ w β k0 κ) {g : ℤ}
    (hg : g ∈ Icc (0 : ℤ) 4) :
    |T.post.Gamma L w (T.postLabels κ g) T.c - T.centerC β c g| ≤ T.windowK * (δ⁻¹ * L ^ (-2 * γ)) := by
  rw [T.post_gamma L w hκ.1 g T.c_notMem]
  simp only [ite_true, T.c_ne_d, ite_false, add_zero]
  set kx := Molecule.kvec L w κ T.x
  set ky := Molecule.kvec L w κ T.y
  have hsh := norm_sq_shift_c ky (kx - ky) (g : ℝ)
  rw [show ky + (kx - ky) = kx by abel] at hsh
  rw [hsh, T.norm_sq_x_sub_y L w hκ.1, T.kvec_x_sub_y hκ]
  have hS := T.sum_gamma_window hres
  have hc := hres.1 T.c (mem_sdiff.mp T.c_mem).1
  obtain ⟨hg0, hg4⟩ := mem_Icc.mp hg
  have hg0' : (0 : ℝ) ≤ g := by exact_mod_cast hg0
  have hg4' : (g : ℝ) ≤ 4 := by exact_mod_cast hg4
  have hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := (abs_nonneg _).trans hc
  have h1g : |1 - (g : ℝ)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hkey : N.Gamma L w κ T.c + ((1 - g) * ∑ v ∈ T.Y, N.Gamma L w κ v + g * (1 - g) * ‖T.exitCharge c‖ ^ 2) -
      T.centerC β c g = (N.Gamma L w κ T.c - β T.c) + (1 - g) * (∑ v ∈ T.Y, N.Gamma L w κ v - ∑ v ∈ T.Y, β v) := by
    unfold centerC; ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hm : |1 - (g : ℝ)| * |∑ v ∈ T.Y, N.Gamma L w κ v - ∑ v ∈ T.Y, β v| ≤ 4 * (T.Y.card * (δ⁻¹ * L ^ (-2 * γ))) :=
    mul_le_mul h1g hS (abs_nonneg _) (by norm_num)
  unfold windowK
  push_cast
  linarith

theorem gamma_d_window {d : ℕ} {L γ δ : ℝ} {w : Mom d} {c : V → Mom d} {β : V → ℝ} {k0 : D → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : N.IsDecoration L w c κ) (hres : N.IsRestricted L γ δ w β k0 κ) {g : ℤ}
    (hg : g ∈ Icc (0 : ℤ) 4) :
    |T.post.Gamma L w (T.postLabels κ g) T.d - T.centerD β c g| ≤ T.windowK * (δ⁻¹ * L ^ (-2 * γ)) := by
  rw [T.post_gamma L w hκ.1 g T.d_notMem]
  simp only [ite_true, Ne.symm T.c_ne_d, ite_false, add_zero]
  set kx := Molecule.kvec L w κ T.x
  set ky := Molecule.kvec L w κ T.y
  have hsh := norm_sq_shift_d ky (kx - ky) (g : ℝ)
  rw [show ky + (kx - ky) = kx by abel] at hsh
  rw [hsh, T.norm_sq_x_sub_y L w hκ.1, T.kvec_x_sub_y hκ]
  have hS := T.sum_gamma_window hres
  have hd := hres.1 T.d (mem_sdiff.mp T.d_mem).1
  obtain ⟨hg0, hg4⟩ := mem_Icc.mp hg
  have hg0' : (0 : ℝ) ≤ g := by exact_mod_cast hg0
  have hg4' : (g : ℝ) ≤ 4 := by exact_mod_cast hg4
  have hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := (abs_nonneg _).trans hd
  have hkey : N.Gamma L w κ T.d + (g * ∑ v ∈ T.Y, N.Gamma L w κ v + g * (g - 1) * ‖T.exitCharge c‖ ^ 2) -
      T.centerD β c g = (N.Gamma L w κ T.d - β T.d) + g * (∑ v ∈ T.Y, N.Gamma L w κ v - ∑ v ∈ T.Y, β v) := by
    unfold centerD; ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hg0']
  have hm : (g : ℝ) * |∑ v ∈ T.Y, N.Gamma L w κ v - ∑ v ∈ T.Y, β v| ≤ 4 * (T.Y.card * (δ⁻¹ * L ^ (-2 * γ))) :=
    mul_le_mul hg4' hS (abs_nonneg _) (by norm_num)
  unfold windowK
  push_cast
  linarith

end TwoExit
end WaveTurbulence.MoleProp4
