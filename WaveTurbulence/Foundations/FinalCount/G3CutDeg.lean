/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Inv
/-! **FINALCOUNT-G3**: degrees, out-degrees and in-degrees of a cut molecule. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]
variable {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}

theorem outdeg_eq_sum (N : Molecule V D) (a : V) :
    N.outdeg a = ∑ x ∈ N.dartsAt a, (if N.out x = true then 1 else 0) := by
  unfold Molecule.outdeg; rw [Finset.card_filter]

theorem indeg_eq_sum (N : Molecule V D) (a : V) :
    N.indeg a = ∑ x ∈ N.dartsAt a, (if N.out x = false then 1 else 0) := by
  unfold Molecule.indeg; rw [Finset.card_filter]

theorem cut_out (v v₂ : V) (x₁ x₂ : D) : (M.cut v v₂ x₁ x₂).out = M.out := rfl

theorem cut_dartsAt_v (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).dartsAt v = {x₁, x₂} := by
  ext x
  rw [cut_mem_dartsAt_v M hcd]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro (h | h)
    · exact ⟨h ▸ hcd.2.2.1, Or.inl h⟩
    · exact ⟨h ▸ hcd.2.2.2.1, Or.inr h⟩

theorem cut_x_ne (hcd : M.IsCutData v v₂ x₁ x₂) : x₁ ≠ x₂ := fun e => by
  have h1 := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2; rw [e] at h1; simp_all

theorem cut_outdeg_v (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).outdeg v = 1 := by
  rw [outdeg_eq_sum, cut_dartsAt_v hcd, Finset.sum_pair (cut_x_ne hcd)]
  have := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2
  simp [cut_out, this, h2]

theorem cut_indeg_v (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).indeg v = 1 := by
  rw [indeg_eq_sum, cut_dartsAt_v hcd, Finset.sum_pair (cut_x_ne hcd)]
  have := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2
  simp [cut_out, this, h2]

theorem cut_deg_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) : (M.cut v v₂ x₁ x₂).deg v₂ + 2 = M.deg v := by
  have := cut_sum_split M hcd (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
  have h2 := cut_deg_v M hcd
  unfold Molecule.deg at *
  omega

theorem cut_sum_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) (g : D → ℕ) :
    ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, g x + (g x₁ + g x₂) = ∑ x ∈ M.dartsAt v, g x := by
  rw [cut_sum_split M hcd g, cut_dartsAt_v hcd, Finset.sum_pair (cut_x_ne hcd)]
  ring

theorem cut_outdeg_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).outdeg v₂ + 1 = M.outdeg v := by
  have h := cut_sum_v₂ hcd (fun x => if M.out x = true then 1 else 0)
  have h1 := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2
  rw [outdeg_eq_sum, outdeg_eq_sum, cut_out]
  simp only [h1, h2] at h
  simpa using h

theorem cut_indeg_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) :
    (M.cut v v₂ x₁ x₂).indeg v₂ + 1 = M.indeg v := by
  have h := cut_sum_v₂ hcd (fun x => if M.out x = false then 1 else 0)
  have h1 := hcd.2.2.2.2.2.1; have h2 := hcd.2.2.2.2.2.2
  rw [indeg_eq_sum, indeg_eq_sum, cut_out]
  simp only [h1, h2] at h
  simpa using h

theorem cut_deg_other (hcd : M.IsCutData v v₂ x₁ x₂) {a : V} (h1 : a ≠ v) (h2 : a ≠ v₂) :
    (M.cut v v₂ x₁ x₂).deg a = M.deg a := by
  unfold Molecule.deg; rw [cut_dartsAt_other M hcd h1 h2]

theorem cut_outdeg_other (hcd : M.IsCutData v v₂ x₁ x₂) {a : V} (h1 : a ≠ v) (h2 : a ≠ v₂) :
    (M.cut v v₂ x₁ x₂).outdeg a = M.outdeg a := by
  unfold Molecule.outdeg; rw [cut_dartsAt_other M hcd h1 h2]; rfl

theorem cut_indeg_other (hcd : M.IsCutData v v₂ x₁ x₂) {a : V} (h1 : a ≠ v) (h2 : a ≠ v₂) :
    (M.cut v v₂ x₁ x₂).indeg a = M.indeg a := by
  unfold Molecule.indeg; rw [cut_dartsAt_other M hcd h1 h2]; rfl

end WaveTurbulence.FinalCountG3
