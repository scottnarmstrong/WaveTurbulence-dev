/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.PositiveQuarticCutGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
import Mathlib.Tactic

/-! # Actual same-direction quartic pair deletion count

The actual old stars are explicit source data. Source conservation fixes
the integer charges, and the genuine five-label count bounds the deleted
label image before the legitimate post-parameter supremum is taken.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem actual_positive_quartic_cut_deletion_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ p q x y z r s : D, x ≠ y → x ≠ z → y ≠ z → p ≠ q → p ≠ r → q ≠ r →
      s ∉ ({p,q,r} : Finset D) → M.out s=M.out r →
      M.dartsAt a={x,y,z} → M.dartsAt b={p,q,r,s} →
      FirstProfileCut M x y z p → FirstProfileCut M x y z q →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := conditional_quartic_positive_profile_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb p q x y z r s hxy hxz hyz hpq hpr hqr hs hout hA hStarB hCutp hCutq Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  let Q := F.image (doubleFiveProfile x y z r s)
  have hfixed : ∀ κ ∈ F, ∀ κ' ∈ F,
      sharedFirstProfile (doubleFiveProfile x y z r s κ)=sharedFirstProfile (doubleFiveProfile x y z r s κ') →
      κ p=κ' p ∧ κ q=κ' q := by
    intro κ hκ κ' hκ' he
    have hdκ := ((hmem κ).mp hκ).1
    have hdκ' := ((hmem κ').mp hκ').1
    exact ⟨firstProfileCut_label_unique M hLp.ne' hCutp hdκ hdκ' he,
      firstProfileCut_label_unique M hLp.ne' hCutq hdκ hdκ' he⟩
  have hQbound := hB L hLR δ hδ M hM a ha b hb p q x y z r s hxy hxz hyz hpq hpr hqr hs hout hA hStarB c β k0 F
    (fun κ hκ => ⟨((hmem κ).mp hκ).1,((hmem κ).mp hκ).2.1⟩) hfixed
  have hlocal : (F.image (deletedLabels M {a,b})).card ≤ Q.card := by
    apply card_image_le_of_kernel_inclusion F
    intro κ hκ κ' hκ' he
    exact positive_quartic_deletedLabels_eq M hLp.ne' hA hStarB hCutp hCutq
      ((hmem κ).mp hκ).1 ((hmem κ').mp hκ').1 he
  have hImage : (deletedLabels M {a,b} '' A).ncard = (F.image (deletedLabels M {a,b})).card := by
    have he : deletedLabels M {a,b} '' A = (F.image (deletedLabels M {a,b}) : Set _) := by
      rw [Finset.coe_image,hf.coe_toFinset]
    rw [he,Set.ncard_coe_finset]
  have hreal : ((deletedLabels M {a,b} '' A).ncard : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
    rw [hImage]
    have hh : ((F.image (deletedLabels M {a,b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
    exact hh.trans hQbound
  have hnat : (deletedLabels M {a,b} '' A).ncard ≤ ⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ := by
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  have hEN : ((deletedLabels M {a,b} '' A).ncard : ℕ∞) ≤ (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) := by exact_mod_cast hnat
  exact (encard_le_deletedImage_mul_post M {a,b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
    (mul_le_mul_of_nonneg_right hEN bot_le)

end WaveTurbulence.MoleProp
