/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
/-! Every nonzero source gap is a lattice difference of norm at least L inverse. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

 theorem inv_scale_le_norm_gap {D : Type*} {d : ℕ} {L : ℝ} (hL : 0 < L)
    (base : Mom d) (κ : D → (Fin d → ℤ)) (x y : D)
    (hne : Molecule.gapAt L base κ x y ≠ 0) : L⁻¹ ≤ ‖Molecule.gapAt L base κ x y‖ := by
  classical
  have hxy : κ x ≠ κ y := by
    intro he
    apply hne
    unfold Molecule.gapAt Molecule.kvec
    rw [he, sub_self]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  have hn : (1 : ℝ) ≤ |(κ x j : ℝ) - (κ y j : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hj))
  have hcoord : (Molecule.gapAt L base κ x y) j = ((κ x j : ℝ) - (κ y j : ℝ)) / L := by
    unfold Molecule.gapAt Molecule.kvec latticePoint
    simp only [PiLp.sub_apply, PiLp.add_apply]
    ring
  have hh := PiLp.norm_apply_le (Molecule.gapAt L base κ x y) j
  rw [Real.norm_eq_abs, hcoord, abs_div, abs_of_pos hL] at hh
  have hlow : L⁻¹ ≤ |(κ x j : ℝ) - (κ y j : ℝ)| / L := by
    simpa only [one_div] using (div_le_div_of_nonneg_right hn hL.le)
  exact hlow.trans hh

end WaveTurbulence.LGSpine
