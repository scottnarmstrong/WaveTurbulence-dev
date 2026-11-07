/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CountESupremum
public import WaveTurbulence.Foundations.FinalCount.Degen.CommonChoices
import Mathlib.Tactic

/-! # Uniform countE inequality for actual degenerate-atom deletion -/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 section 10.5's unnormalized large-gain counting step, with the
actual countE supremum on both sides and no post-count hypothesis. -/
theorem countE_erase_constant_atom_le (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) {v : V} {e : D} (he : M.atom e = v)
    (hconstant : ∀ κ, Adm κ → ConstantAt M κ v) :
    M.countE L γ δ w Adm ≤ (⌈(2 * L + 1) ^ d⌉₊ : ℕ∞) *
      (eraseAtoms M {v}).countE L γ δ w (eraseAdmissibility M {v} Adm) := by
  classical
  let P := eraseAdmissibility M {v} Adm
  let E := (eraseAtoms M {v}).countE L γ δ w P
  have hE : E ≠ ⊤ := Mole.countE_ne_top (eraseAtoms M {v}) hL γ δ w P
  let N := E.toNat
  have hNE : (N : ℕ∞) = E := ENat.natCast_toNat hE
  conv_lhs => unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A : Set (D → (Fin d → ℤ)) := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  have hfA : A.Finite := (Mole.finite_restricted M hL γ δ w β k0).subset (fun κ hκ => hκ.2.1)
  let S := hfA.toFinset
  have hmem (κ : D → (Fin d → ℤ)) : κ ∈ S ↔ κ ∈ A := hfA.mem_toFinset
  let Q := S.image (fun κ => κ e)
  have hQ : Q.card ≤ ⌈(2 * L + 1) ^ d⌉₊ := by
    have hr := card_common_choices_le hL w (k0 e) e S
      (fun κ hκ => ((hmem κ).mp hκ).2.1.2 e)
    exact_mod_cast hr.trans (Nat.le_ceil _)
  have hF (q : Fin d → ℤ) : (S.filter fun κ => κ e = q).card ≤ N := by
    let F := S.filter fun κ => κ e = q
    let c' := momentumForCommon M {v} c (w + latticePoint L q)
    let β' := energyForCommon M {v} β (w + latticePoint L q)
    let T : Set (RetainedDart M {v} → (Fin d → ℤ)) :=
      {κ' | (eraseAtoms M {v}).IsDecoration L w c' κ' ∧
        (eraseAtoms M {v}).IsRestricted L γ δ w β' (fun x => k0 x.val) κ' ∧ P κ'}
    let r := fun κ : D → (Fin d → ℤ) => fun x : RetainedDart M {v} => κ x.val
    have hmap : Set.MapsTo r (F : Set (D → (Fin d → ℤ))) T := by
      intro κ hκ
      have hκ' := mem_filter.mp hκ
      have ha := (hmem κ).mp hκ'.1
      exact restriction_maps_conditioned M he L γ δ w Adm c β k0 ha.1 ha.2.1 ha.2.2
        (hconstant κ ha.2.2) hκ'.2
    have hinj : Set.InjOn r (F : Set (D → (Fin d → ℤ))) := by
      intro κ hκ κ' hκ' hrest
      have hκF := mem_filter.mp hκ
      have hκF' := mem_filter.mp hκ'
      have ha := (hmem κ).mp hκF.1
      have ha' := (hmem κ').mp hκF'.1
      apply removal_pair_injective M he ha.1.1 ha'.1.1 (hconstant κ ha.2.2) (hconstant κ' ha'.2.2)
      exact Prod.ext (hκF.2.trans hκF'.2.symm) hrest
    have hc' := momentumForCommon_zero_at_four M hM {v} c (w + latticePoint L q) hc
    have hk0' : ∀ x : RetainedDart M {v}, k0 ((eraseAtoms M {v}).mate x).val = k0 x.val := by
      intro x
      exact hk0 x.val
    have hT : T.encard ≤ E := encard_le_countE (eraseAtoms M {v}) L γ δ w P c' β' (fun x => k0 x.val) hc' hk0'
    have hh := (Set.encard_le_encard_of_injOn hmap hinj).trans hT
    rw [Set.encard_coe_eq_coe_finsetCard] at hh
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hh hE
  have hSN : S.card ≤ ⌈(2 * L + 1) ^ d⌉₊ * N := by
    calc
      _ = ∑ q ∈ Q, (S.filter fun κ => κ e = q).card := card_eq_sum_card_image _ S
      _ ≤ ∑ _q ∈ Q, N := sum_le_sum fun q _ => hF q
      _ = Q.card * N := by simp only [sum_const, nsmul_eq_mul]; rfl
      _ ≤ _ := Nat.mul_le_mul_right N hQ
  change A.encard ≤ _
  rw [hfA.encard_eq_coe_toFinset_card]
  have hSN' : (S.card : ℕ∞) ≤ (⌈(2 * L + 1) ^ d⌉₊ : ℕ∞) * (N : ℕ∞) := by exact_mod_cast hSN
  simpa only [hNE] using hSN'

end WaveTurbulence.Degen
