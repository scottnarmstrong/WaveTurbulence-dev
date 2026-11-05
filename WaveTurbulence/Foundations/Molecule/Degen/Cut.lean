/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-! # DH21 Lemma 9.14: cancellation of internal bonds in a cut

Scratch against B2 molecule draft cd556873. A boundary is represented by
its dart inside the chosen atom set, retaining its actual orientation.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.Degen

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Darts on the inside of the cut, counted once per crossing bond. -/
def boundaryDarts (M : Molecule V D) (S : Finset V) : Finset D :=
  univ.filter fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S

/-- Internal darts occur in mate pairs, including the two darts of a self-loop. -/
def internalDarts (M : Molecule V D) (S : Finset V) : Finset D :=
  univ.filter fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S

theorem sum_internal_eq_zero (M : Molecule V D) (S : Finset V)
    {E : Type*} [AddCommGroup E] (g : D → E)
    (hg : ∀ x, g (M.mate x) = -g x) :
    ∑ x ∈ internalDarts M S, g x = 0 := by
  apply Finset.sum_involution (fun x _ => M.mate x)
  · intro x _
    rw [hg, add_neg_cancel]
  · intro x _ _
    exact M.mate_ne x
  · intro x hx
    simpa only [internalDarts, mem_filter, mem_univ, true_and, M.mate_mate, and_comm] using hx
  · intro x _
    exact M.mate_mate x

/-- Exact discrete divergence theorem, valid in any additive commutative group. -/
theorem sum_atoms_eq_boundary (M : Molecule V D) (S : Finset V)
    {E : Type*} [AddCommGroup E] (g : D → E)
    (hg : ∀ x, g (M.mate x) = -g x) :
    (∑ v ∈ S, ∑ x ∈ M.dartsAt v, g x) = ∑ x ∈ boundaryDarts M S, g x := by
  classical
  have hflat : (∑ v ∈ S, ∑ x ∈ M.dartsAt v, g x) =
      ∑ x ∈ univ.filter (fun x => M.atom x ∈ S), g x := by
    simp only [Molecule.dartsAt, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    by_cases hx : M.atom x ∈ S
    · rw [sum_eq_single (M.atom x)]
      · simp only [hx, ite_true]
      · intro v _ hv
        simp only [show M.atom x ≠ v from Ne.symm hv, ite_false]
      · exact fun h => False.elim (h hx)
    · simp only [hx, ite_false]
      apply sum_eq_zero
      intro v hv
      have hne : M.atom x ≠ v := fun he => hx (he ▸ hv)
      simp only [hne, ite_false]
  have hsplit : (∑ x ∈ univ.filter (fun x => M.atom x ∈ S), g x) =
      (∑ x ∈ internalDarts M S, g x) + ∑ x ∈ boundaryDarts M S, g x := by
    have he := sum_filter_add_sum_filter_not (s := univ.filter (fun x => M.atom x ∈ S))
      (fun x => M.atom (M.mate x) ∈ S) g
    simpa only [filter_filter, internalDarts, boundaryDarts] using he.symm
  rw [hflat, hsplit, sum_internal_eq_zero M S g hg, zero_add]

omit [DecidableEq V] [Fintype D] in
/-- Mate reverses the source's actual orientation sign. -/
theorem dartSign_mate (M : Molecule V D) (x : D) :
    M.dartSign (M.mate x) = -M.dartSign x := by
  simp only [Molecule.dartSign, M.out_mate]
  cases M.out x <;> norm_num

/-- DH21 Lemma 9.14, exact momentum identity on an arbitrary atom cut.
The constant is literally the sum of the prescribed atom momenta. -/
theorem cut_momentum (M : Molecule V D) {d : ℕ} {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hκ : M.IsDecoration L w c κ)
    (S : Finset V) (hS : S ⊆ M.atoms) :
    (∑ x ∈ boundaryDarts M S, M.dartSign x • Molecule.kvec L w κ x) = ∑ v ∈ S, c v := by
  rw [← sum_atoms_eq_boundary M S]
  · apply sum_congr rfl
    intro v hv
    exact hκ.2 v (hS hv)
  · intro x
    rw [dartSign_mate, Molecule.kvec, hκ.1 x, neg_smul]
    rfl

/-- DH21 Lemma 9.14, energy inequality. The stronger `card S` error is
proved; bounding it by the full number of atoms gives the printed lemma.
The square-torus specialization uses the Euclidean norm (campaign D2). -/
theorem cut_energy (M : Molecule V D) {d : ℕ} {L γ δ : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} {β : V → ℝ} {k0 : D → Mom d}
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ)
    (S : Finset V) (hS : S ⊆ M.atoms) :
    |(∑ x ∈ boundaryDarts M S, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) -
        ∑ v ∈ S, β v| ≤ S.card * (δ⁻¹ * L ^ (-2 * γ)) := by
  have he := sum_atoms_eq_boundary M S
    (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) (fun x => by
      rw [dartSign_mate, Molecule.kvec, hκ.1 x, neg_mul]
      rfl)
  change (∑ v ∈ S, M.Gamma L w κ v) = _ at he
  rw [← he, ← sum_sub_distrib]
  calc
    _ ≤ ∑ v ∈ S, |M.Gamma L w κ v - β v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ S, δ⁻¹ * L ^ (-2 * γ) := sum_le_sum fun v hv => hres.1 v (hS hv)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

/-- A single crossing bond has its momentum uniquely fixed by the atom
parameters, independent of every other label in the decoration. -/
theorem single_boundary_momentum_unique (M : Molecule V D) {d : ℕ} {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ κ' : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ')
    (S : Finset V) (hS : S ⊆ M.atoms) {x : D}
    (hboundary : boundaryDarts M S = {x}) :
    Molecule.kvec L w κ x = Molecule.kvec L w κ' x := by
  have h1 := cut_momentum M hκ S hS
  have h2 := cut_momentum M hκ' S hS
  rw [hboundary, sum_singleton] at h1 h2
  have he := h1.trans h2.symm
  unfold Molecule.dartSign at he
  cases hout : M.out x <;> simpa only [hout, Bool.false_eq_true, ite_false, ite_true,
    one_smul, neg_smul, neg_inj] using he

end WaveTurbulence.Degen
