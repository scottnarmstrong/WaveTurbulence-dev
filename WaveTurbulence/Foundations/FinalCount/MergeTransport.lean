/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeSum
import Mathlib.Tactic

/-! # A decoration of `M` restricts to a decoration of the merged molecule (DH23 L1977)

The charge at the merged atom is `c v₁ + c v₂`; its energy is `Γ_{v₁} + Γ_{v₂}` (the two bonds between `v₁` and `v₂`
cancel in both sums); all other stars are unchanged.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

/-- The charges of the merged molecule. -/
def mcharges {d : ℕ} (v₁ v₂ : V) (c : V → Mom d) : V → Mom d := fun v => if v = v₁ then c v₁ + c v₂ else c v

theorem dartSign_N (z : OffPair M v₁ v₂) : (mergePair M v₁ v₂ hv₁ hne).dartSign z = M.dartSign z.val := rfl

theorem atom_ne_v₂ {v : V} (hv : v ∈ (mergePair M v₁ v₂ hv₁ hne).atoms) : v ≠ v₂ := (mem_erase.mp hv).1

/-- A decoration of `M` restricts to a decoration of the merged molecule. -/
theorem merge_isDecoration {d : ℕ} {L : ℝ} {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hv₂ : v₂ ∈ M.atoms)
    (hκ : M.IsDecoration L (0 : Mom d) c κ) :
    (mergePair M v₁ v₂ hv₁ hne).IsDecoration L (0 : Mom d) (mcharges v₁ v₂ c) (fun y => κ y.val) := by
  refine ⟨fun z => hκ.1 z.val, fun v hv => ?_⟩
  have hv2 := atom_ne_v₂ (hv₁ := hv₁) (hne := hne) hv
  have hvM : v ∈ M.atoms := (mem_erase.mp hv).2
  have hsum : ∀ z ∈ (mergePair M v₁ v₂ hv₁ hne).dartsAt v,
      (mergePair M v₁ v₂ hv₁ hne).dartSign z • Molecule.kvec L 0 (fun y : OffPair M v₁ v₂ => κ y.val) z =
        M.dartSign z.val • Molecule.kvec L 0 κ z.val := fun z _ => rfl
  rw [sum_congr rfl hsum]
  by_cases h1 : v = v₁
  · subst h1
    have key := star_sum_v₁ (M := M) (v₁ := v) (v₂ := v₂) (hv₁ := hv₁) (hne := hne)
      (fun x => M.dartSign x • Molecule.kvec L 0 κ x)
    have hz : ∑ x ∈ pairDarts M v v₂, M.dartSign x • Molecule.kvec L 0 κ x = 0 :=
      sum_pair_odd _ (fun x => by
        rw [Degen.dartSign_mate]
        have : Molecule.kvec L 0 κ (M.mate x) = Molecule.kvec L 0 κ x := by simp [Molecule.kvec, hκ.1]
        rw [this, neg_smul])
    rw [hz, add_zero] at key
    rw [key, hκ.2 v hvM, hκ.2 v₂ hv₂]
    simp [mcharges]
  · have hfar := star_sum_far (M := M) (v₁ := v₁) (v₂ := v₂) (hv₁ := hv₁) (hne := hne)
      (fun x => M.dartSign x • Molecule.kvec L 0 κ x) h1 hv2
    rw [hfar, hκ.2 v hvM]
    simp [mcharges, h1]

/-- Energies of the merged molecule away from the merged atom. -/
theorem merge_gamma_far {d : ℕ} {L : ℝ} {κ : D → (Fin d → ℤ)} {v : V} (hv : v ∈ (mergePair M v₁ v₂ hv₁ hne).atoms)
    (h1 : v ≠ v₁) :
    (mergePair M v₁ v₂ hv₁ hne).Gamma L (0 : Mom d) (fun y => κ y.val) v = M.Gamma L (0 : Mom d) κ v := by
  have h2 := atom_ne_v₂ (hv₁ := hv₁) (hne := hne) hv
  have := star_sum_far (M := M) (v₁ := v₁) (v₂ := v₂) (hv₁ := hv₁) (hne := hne)
    (fun x => M.dartSign x * ‖Molecule.kvec L 0 κ x‖ ^ 2) h1 h2
  exact this

/-- The energy at the merged atom is the sum of the two energies. -/
theorem merge_gamma_v₁ {d : ℕ} {L : ℝ} {κ : D → (Fin d → ℤ)} (hκ : ∀ z, κ (M.mate z) = κ z) :
    (mergePair M v₁ v₂ hv₁ hne).Gamma L (0 : Mom d) (fun y => κ y.val) v₁ =
      M.Gamma L (0 : Mom d) κ v₁ + M.Gamma L (0 : Mom d) κ v₂ := by
  have key := star_sum_v₁ (M := M) (v₁ := v₁) (v₂ := v₂) (hv₁ := hv₁) (hne := hne)
    (fun x => M.dartSign x * ‖Molecule.kvec L 0 κ x‖ ^ 2)
  have hz : ∑ x ∈ pairDarts M v₁ v₂, M.dartSign x * ‖Molecule.kvec L 0 κ x‖ ^ 2 = 0 :=
    sum_pair_odd _ (fun x => by
      rw [Degen.dartSign_mate]
      have : Molecule.kvec L 0 κ (M.mate x) = Molecule.kvec L 0 κ x := by simp [Molecule.kvec, hκ]
      rw [this]; ring)
  rw [hz, add_zero] at key
  exact key

end MergeSum
end WaveTurbulence.FinalCountG8
