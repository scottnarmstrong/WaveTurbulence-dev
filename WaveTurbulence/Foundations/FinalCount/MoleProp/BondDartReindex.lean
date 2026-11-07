/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DartReindex
import Mathlib.Tactic

/-! # Relabeling the genuine counting fibers, including bond consistency -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem countEFree_le_of_bond_preserving_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (E → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → (∀ x, κ (M.mate x) = κ x) → Adm' (relabelDartLabels f κ)) :
    countEFree M L γ δ w Adm ≤ countEFree N L γ δ w Adm' := by
  classical
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let k0' := fun y => k0 (f.symm y)
  have hk0' : ∀ y, k0' (N.mate y) = k0' y := by
    intro y
    obtain ⟨x,rfl⟩ := f.surjective y
    simp only [k0',hm,f.symm_apply_apply,hk0]
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  let B := {κ' | N.IsDecoration L w c κ' ∧ N.IsRestricted L γ δ w β k0' κ' ∧ Adm' κ'}
  have hsign (x : D) : N.dartSign (f x) = M.dartSign x := by simp only [Molecule.dartSign,ho]
  have hkv (κ : D → (Fin d → ℤ)) (x : D) :
      Molecule.kvec L w (relabelDartLabels f κ) (f x) = Molecule.kvec L w κ x := by
    simp only [Molecule.kvec,relabelDartLabels,Equiv.coe_fn_mk,f.symm_apply_apply]
  have hmap : Set.MapsTo (relabelDartLabels f) A B := by
    intro κ hκ
    have hsum (v : V) : ∑ y ∈ N.dartsAt v, N.dartSign y • Molecule.kvec L w (relabelDartLabels f κ) y =
        ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x := by
      rw [← sum_dartsAt_reindex M N f ha v (fun y => N.dartSign y • Molecule.kvec L w (relabelDartLabels f κ) y)]
      simp only [hsign,hkv]
    have henergy (v : V) : N.Gamma L w (relabelDartLabels f κ) v = M.Gamma L w κ v := by
      unfold Molecule.Gamma
      rw [← sum_dartsAt_reindex M N f ha v (fun y => N.dartSign y * ‖Molecule.kvec L w (relabelDartLabels f κ) y‖ ^ 2)]
      simp only [hsign,hkv]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,hAdm κ hκ.2.2 hκ.1.1⟩
    · intro y
      obtain ⟨x,rfl⟩ := f.surjective y
      simp only [relabelDartLabels,Equiv.coe_fn_mk,hm,f.symm_apply_apply,hκ.1.1]
    · intro v hv
      rw [hsum]
      exact hκ.1.2 v (hA.symm ▸ hv)
    · intro v hv
      rw [henergy]
      exact hκ.2.1.1 v (hA.symm ▸ hv)
    · intro y
      obtain ⟨x,rfl⟩ := f.surjective y
      simpa only [hkv,k0',f.symm_apply_apply] using hκ.2.1.2 x
  exact (Set.encard_le_encard_of_injOn hmap (relabelDartLabels f).injective.injOn).trans
    (encard_le_countEFree N L γ δ w Adm' c β k0' hk0')

theorem countAFree_le_of_bond_preserving_dart_equiv (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x, N.atom (f x) = M.atom x)
    (hm : ∀ x, N.mate (f x) = f (M.mate x)) (ho : ∀ x, N.out (f x) = M.out x)
    {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (E → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → (∀ x, κ (M.mate x) = κ x) → Adm' (relabelDartLabels f κ)) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤ countAFree N L γ δ C1 w Adm' P := by
  have hχ := circuitRank_eq_of_dart_equiv M N f hA ha hm ho
  have hcells := ladderCells_eq_of_dart_equiv M N f hA ha hm ho
  unfold countAFree cellProduct
  rw [hχ,hcells]
  exact mul_le_mul_of_nonneg_right (ENat.toENNReal_mono
    (countEFree_le_of_bond_preserving_dart_equiv M N f hA ha hm ho L γ δ w Adm Adm' hAdm)) bot_le

end WaveTurbulence.MoleProp
