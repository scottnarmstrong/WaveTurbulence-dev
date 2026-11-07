/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualThreeCutEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
import Mathlib.Tactic

/-! # Actual hard three-cut deletion count

The actual old stars are explicit source data. Source conservation fixes
the integer charges, and the genuine five-label count bounds the deleted
label image before the legitimate post-parameter supremum is taken.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem actual_three_cut_deletion_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ e₁ e₂ x y z r s : D, x ≠ y → x ≠ z → y ≠ z →
      e₁ ≠ e₂ → e₁ ≠ r → e₂ ≠ r → s ∉ ({e₁,e₂,r} : Finset D) →
      e₁ ≠ M.mate x → e₂ ≠ M.mate x →
      M.dartsAt a = {x,y,z} → M.dartsAt b = {e₁,e₂,r,s} →
    ∀ U₀ U₁ U₂ : Finset V, U₀ ⊆ M.atoms → U₁ ⊆ M.atoms → U₂ ⊆ M.atoms →
      Degen.boundaryDarts M U₀ = {e₁,e₂,M.mate x} →
      Degen.boundaryDarts M U₁ = {M.mate e₁,M.mate y} →
      Degen.boundaryDarts M U₂ = {M.mate e₂,M.mate z} →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*((U₀.card : ℝ)+1)^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := signed_shared_count_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb e₁ e₂ x y z r s hxy hxz hyz h12 h1r h2r hs h1x h2x hA hStarB U₀ U₁ U₂ hU₀ hU₁ hU₂ hcut₀ hcut₁ hcut₂ Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hcap : SharedMixed (actualThreeCutSigns M x y z r s) false :=
    not_all_out_equal_of_triple_star M hM ha hxy hxz hyz hA
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  have hN : (1 : ℝ) ≤ (U₀.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  by_cases hne : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let sg := actualThreeCutSigns M x y z r s
    let aq := ∑ i : Fin 5, sharedCoefficients sg false i • doubleFiveProfile x y z r s κ0 i
    let bq := ∑ i : Fin 5, sharedCoefficients sg true i • doubleFiveProfile x y z r s κ0 i
    let centers := ![k0 x,k0 y,k0 z,k0 r,k0 s]
    let Q := F.image (doubleFiveProfile x y z r s)
    have hQS : ∀ k ∈ Q, SignedSharedSource L sg aq bq
        (β a) ((∑ v ∈ U₀, β v)-β b) (((U₀.card : ℝ)+1)*(δ⁻¹*L^(-2*γ))) centers k := by
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
        · change ‖latticePoint L (κ z)-k0 z‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 z
        · change ‖latticePoint L (κ r)-k0 r‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 r
        · change ‖latticePoint L (κ s)-k0 s‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 s
      · intro second
        have hm := three_cut_shared_integer_eq M hLp.ne' ha hb hxy hxz hyz h12 h1r h2r hs h1x h2x hA hStarB U₀ hU₀ hcut₀ hκA.1 hκ0.1 second
        have he := three_cut_shared_energy M L γ δ hτ ha hb hxy hxz hyz h12 h1r h2r hs h1x h2x hA hStarB U₀ hU₀ hcut₀ hκA.1 hκA.2.1 second
        constructor
        · cases second <;> exact hm
        · exact he
    have hQbound := hB L hLR δ hδ ((U₀.card : ℝ)+1) hN sg hcap aq bq (β a) ((∑ v ∈ U₀, β v)-β b) centers Q hQS
    have hlocal : (F.image (deletedLabels M {a,b})).card ≤ Q.card := by
      apply card_image_le_of_kernel_inclusion F
      intro κ hκ κ' hκ' hp
      exact three_cut_deletedLabels_eq M hLp.ne' hA hStarB U₁ U₂ hU₁ hU₂ hcut₁ hcut₂
        ((hmem κ).mp hκ).1 ((hmem κ').mp hκ').1 hp
    have hImage : (deletedLabels M {a,b} '' A).ncard = (F.image (deletedLabels M {a,b})).card := by
      have he : deletedLabels M {a,b} '' A = (F.image (deletedLabels M {a,b}) : Set _) := by
        rw [Finset.coe_image,hf.coe_toFinset]
      rw [he,Set.ncard_coe_finset]
    have hreal : ((deletedLabels M {a,b} '' A).ncard : ℝ) ≤ C*((U₀.card : ℝ)+1)^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {a,b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      exact hh.trans hQbound
    have hnat : (deletedLabels M {a,b} '' A).ncard ≤ ⌈C*((U₀.card : ℝ)+1)^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {a,b} '' A).ncard : ℕ∞) ≤ (⌈C*((U₀.card : ℝ)+1)^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {a,b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
