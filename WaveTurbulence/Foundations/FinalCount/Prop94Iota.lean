/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Ops
/-! The `ι_v ≠ 0` reading of DH23 Remark `remiota` / L1801 (FINALCOUNT-G2).

Source: "`ι_v = 1` if a cutting operation happened before the cutting at `v`, such that the gaps `r, r'` of
these cuttings satisfy `0 < |r ± r'| ≤ L^{-50η} R_v`" (L1782), and L1801: "the corresponding gap `r` must belong
to a fixed ball of radius `L^{-50η}R`".  After the earlier cut at `v'` (degree `2`, darts `y₁` incoming,
`y₂` outgoing) the gap `r'` of that cut is, up to sign, the charge `c_{v'} = ∑_{x ↔ v'} ζ_{v',x} k_x` of the
cut atom, a *parameter* of the molecule.  So the condition is a condition on the decoration alone,
"`|r - s · charge(v')| ≤ ρ` for the fixed atom `v'` and a sign `s = ±1`", and the fixed ball of L1801 is the one
with centre `s · c_{v'}`, determined by the parameters. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The charge `∑_{x ↔ v'} ζ_{v',x} k_x` of an atom. -/
noncomputable def chargeAt (M : Molecule V D) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (v' : V) : Mom d :=
  ∑ x ∈ M.dartsAt v', M.dartSign x • Molecule.kvec L w κ x

theorem norm_latticePoint_ge {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) (hn : n ≠ 0) : L⁻¹ ≤ ‖latticePoint L n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    exact hn (funext fun i => by simpa using (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(latticePoint L n) i| ≤ ‖latticePoint L n‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n) i
  have h3 : (latticePoint L n) i = (n i : ℝ) / L := rfl
  rw [h3, abs_div, abs_of_pos hL] at h2
  calc L⁻¹ = 1 / L := by simp
    _ ≤ |(n i : ℝ)| / L := by gcongr
    _ ≤ _ := h2

end WaveTurbulence.FinalCount
