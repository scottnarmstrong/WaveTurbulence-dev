/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount4
/-! # VINE-COUNT part 23 (session 4): the joint slab of an Operation 1 that creates a new component.

For a vine removal `K` whose gap `r = gapAt x₁ x₂` is a fixed nonzero lattice vector and whose lower-joint energy
`‖k_{y₂}‖² - ‖k_{y₁}‖²` lies in a fixed interval (DH23/TARGET excessprop1 (2): "`k_{ℓ₁} ± k_{ℓ₂}` equals a fixed constant and
`|k_{ℓ₁}|² ± |k_{ℓ₂}|²` belongs to a fixed interval"), the chart coordinate `x₀` lies in a slab
`{z : |2⟨r, z⟩ - β'| ≤ ν τ}`, whose lattice points number `≲ ν δ⁻¹ L^{d-γ+γ₀}` (TARGET Lemma `atomcountlem`, `atomcountbd`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The energy of the two bonds of the removed vine at its lower joint: `|k_{y₂}|² - |k_{y₁}|²`. -/
noncomputable def lowerG {M : Molecule V D} (K : VineCut M) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) : ℝ :=
  ‖Molecule.kvec L w κ K.y₂‖ ^ 2 - ‖Molecule.kvec L w κ K.y₁‖ ^ 2

section Slab
variable {M : Molecule V D} (K : VineCut M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower) (hMol : M.IsMolecule)
  (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)
include hB

theorem energy_lower_eq (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) :
    energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) K.C.lower = - lowerG K L w κ := by
  have hk : ∀ x, ‖Molecule.kvec L w κ (M.mate x)‖ ^ 2 = ‖Molecule.kvec L w κ x‖ ^ 2 := by
    intro x; simp [Molecule.kvec, hκ x]
  have h := sum_bond_incidence M K.C.atoms K.C.lower (fun x => ‖Molecule.kvec L w κ x‖ ^ 2) hk
  rw [group_at_b K hB, Finset.sum_pair (y₁_ne_y₂ K hB)] at h
  simp only [smul_eq_mul, Molecule.dartSign, y₁_out K, y₂_out K] at h
  unfold energy lowerG
  simp only [Bool.false_eq_true, ite_false, ite_true] at h
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [h]; ring

include hMol hM in
theorem x0_phase (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hdec : M.IsDecoration L w c κ)
    (hc : ∀ x ∈ M.atoms, M.deg x = 4 → c x = 0) :
    2 * inner ℝ (latticePoint L (rint K κ)) (latticePoint L (xint K A κ A.indexing.shape.x0)) =
      - lowerG K L w κ + ‖w‖ ^ 2 - ‖w - latticePoint L (rint K κ)‖ ^ 2 := by
  have hrl : Molecule.gapAt L w κ K.x₁ K.x₂ = latticePoint L (rint K κ) := gapAt_eq_lattice K L w κ
  have c0 := chart_coord_eq K hB hMol hM A L w c κ hdec hc A.indexing.shape.x0
  have ht := A.joint_phase d w (Molecule.gapAt L w κ K.x₁ K.x₂)
    (A.chart w (Molecule.gapAt L w κ K.x₁ K.x₂) (kfibElt K hB hMol hM L w c κ hdec hc))
  rw [Equiv.symm_apply_apply] at ht
  unfold nodeResonance at ht
  rw [if_pos rfl, A.indexing.lower] at ht
  have ktf : (kfibElt K hB hMol hM L w c κ hdec hc).1 = fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1 :=
    funext fun e => kfibElt_val K hB hMol hM L w c κ hdec hc e
  rw [ktf] at ht
  change energy M K.C.atoms (fun e : Bond M K.C.atoms => Molecule.kvec L w κ e.1) K.C.lower + _ = _ at ht
  rw [energy_lower_eq K hB L w κ hdec.1, c0, hrl] at ht
  linarith

end Slab

end WaveTurbulence.VineCount
