/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualSharedTripleEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
import Mathlib.Tactic

/-! # Actual adjacent cubic-star deletion count

The actual old stars are explicit source data. Source conservation fixes
the integer charges, and the genuine five-label count bounds the deleted
label image before the legitimate post-parameter supremum is taken.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem actual_shared_triples_deletion_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ x y r s t : D, x ≠ y → x ≠ r → y ≠ r →
      M.mate x ≠ s → M.mate x ≠ t → s ≠ t →
      M.dartsAt a = {x,y,r} → M.dartsAt b = {M.mate x,s,t} →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := signed_shared_count_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb x y r s t hxy hxr hyr hxs hxt hst hA hStarB Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hcap : SharedMixed (actualSharedSigns M x y r s t) false :=
    not_all_out_equal_of_triple_star M hM ha hxy hxr hyr hA
  let e : Fin 5 → D := ![x,y,r,s,t]
  have hcover := deleted_shared_triples_coverage M hA hStarB
  have hprof : (localLabels M e : (D → (Fin d → ℤ)) → (Fin 5 → (Fin d → ℤ))) = doubleFiveProfile x y r s t := by
    funext κ i
    fin_cases i <;> rfl
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  by_cases hne : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let sg := actualSharedSigns M x y r s t
    let aq := ∑ i : Fin 5, sharedCoefficients sg false i • doubleFiveProfile x y r s t κ0 i
    let bq := ∑ i : Fin 5, sharedCoefficients sg true i • doubleFiveProfile x y r s t κ0 i
    let centers := ![k0 x,k0 y,k0 r,k0 s,k0 t]
    let Q := F.image (doubleFiveProfile x y r s t)
    have hQS : ∀ k ∈ Q, SignedSharedSource L sg aq bq
        (β a) (β b) (1*(δ⁻¹*L^(-2*γ))) centers k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκA := (hmem κ).mp hκ
      refine ⟨?_,?_⟩
      · intro i
        fin_cases i
        · change ‖latticePoint L (κ x)-k0 x‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 x
        · change ‖latticePoint L (κ y)-k0 y‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 y
        · change ‖latticePoint L (κ r)-k0 r‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 r
        · change ‖latticePoint L (κ s)-k0 s‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 s
        · change ‖latticePoint L (κ t)-k0 t‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 t
      · intro second
        have hm := actual_shared_integer_momentum_eq M hLp.ne' ha hb hxy hxr hyr hxs hxt hst hA hStarB hκA.1 hκ0.1 second
        have he := actual_shared_energy M L γ δ ha hb hxy hxr hyr hxs hxt hst hA hStarB hκA.1 hκA.2.1 second
        constructor
        · cases second <;> exact hm
        · simpa only [one_mul] using he
    have hQbound' := hB L hLR δ hδ 1 le_rfl sg hcap aq bq (β a) (β b) centers Q hQS
    have hQbound : (Q.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
      simpa only [one_pow,mul_one] using hQbound'
    have hlocal := card_deletedLabels_image_le_localLabels_image M {a,b} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    rw [hprof] at hlocal
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
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
