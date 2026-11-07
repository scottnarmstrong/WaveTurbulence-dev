/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
import Mathlib.Tactic

/-! # The exact countE supremum and its actual restriction admissibility -/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Literal existential projection of the inherited label restrictions
onto the actual retained bonds, not an assumed counting estimate. -/
def eraseAdmissibility (M : Molecule V D) {d : ℕ} (Y : Finset V)
    (Adm : (D → (Fin d → ℤ)) → Prop) (κ' : RetainedDart M Y → (Fin d → ℤ)) : Prop :=
  ∃ κ : D → (Fin d → ℤ), Adm κ ∧ (fun x : RetainedDart M Y => κ x.val) = κ'

/-- Every fixed set of source parameters is one actual term of countE. -/
theorem encard_le_countE (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0)
    (hk0 : ∀ x, k0 (M.mate x) = k0 x) :
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}.encard ≤
      M.countE L γ δ w Adm := by
  unfold Molecule.countE
  exact le_iSup_of_le c <| le_iSup_of_le hc <| le_iSup_of_le β <|
    le_iSup_of_le k0 <| le_iSup_of_le hk0 le_rfl

/-- Conditioned on the common integer label q, every old decoration maps
into a single post-removal parameter set, whose parameters do not depend
on the rest of the old decoration. -/
theorem restriction_maps_conditioned (M : Molecule V D) {d : ℕ} {v : V} {e : D}
    (he : M.atom e = v) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    {κ : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hd : M.IsDecoration L w c κ) (hr : M.IsRestricted L γ δ w β k0 κ)
    (ha : Adm κ) (ht : ConstantAt M κ v) (hq : κ e = q) :
    (eraseAtoms M {v}).IsDecoration L w
        (momentumForCommon M {v} c (w + latticePoint L q)) (fun x => κ x.val) ∧
      (eraseAtoms M {v}).IsRestricted L γ δ w
        (energyForCommon M {v} β (w + latticePoint L q)) (fun x => k0 x.val) (fun x => κ x.val) ∧
      eraseAdmissibility M {v} Adm (fun x => κ x.val) := by
  have hm := isDecoration_eraseAtoms M {v} hd
  have hg := isRestricted_eraseAtoms M {v} hr
  rw [residualMomentum_eq_common M he hd.1 ht] at hm
  rw [residualEnergy_eq_common M he hd.1 ht] at hg
  simp only [Molecule.kvec, hq] at hm hg
  exact ⟨hm, hg, κ, ha, rfl⟩

end WaveTurbulence.Degen
