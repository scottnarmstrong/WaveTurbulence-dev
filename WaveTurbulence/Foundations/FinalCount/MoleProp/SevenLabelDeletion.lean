/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SevenLabelEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
import Mathlib.Tactic

/-! # Actual seven-label deletion in DH23 Proposition 10.3 case (2) -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem seven_label_deletion_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ x y z r s t u : D, x ≠ y → x ≠ z → y ≠ z → x ≠ r → x ≠ s →
      r ≠ s → r ≠ t → s ≠ t → u ∉ ({r,s,t} : Finset D) →
      M.dartsAt a = {x,y,z} → M.dartsAt b = {r,s,t,u} →
      M.out r = false → M.out s = true → M.out t = false → M.out u = true →
    ∀ U : Finset V, U ⊆ M.atoms →
      Degen.boundaryDarts M U = {M.mate x,M.mate r,M.mate s} →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(4*((d : ℝ)-γ)-min γ (1-γ)-η)⌉₊ : ℕ∞)*
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := seven_label_local_count_bound d hd γ hγ η hη hηmax
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb x y z r s t u hxy hxz hyz hxr hxs hrs hrt hst hu hA hStarB hro hso hto huo U hU hcut Adm hAdm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  have hcap : SharedMixed (actualThreeCutSigns M x y z r s) false :=
    not_all_out_equal_of_triple_star M hM ha hxy hxz hyz hA
  let e : Fin 7 → D := ![x,y,z,r,s,t,u]
  have hcover : ∀ w : DeletedDart M {a,b}, ∃ i : Fin 7, w.val=e i ∨ w.val=M.mate (e i) := by
    apply deleted_cover_of_incident_cover
    intro w hw
    rcases mem_insert.mp hw with hwa | hwb
    · have hh := (Mole.mem_dartsAt M a w).mpr hwa
      rw [hA] at hh
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h
      · exact ⟨0,Or.inl h⟩
      · exact ⟨1,Or.inl h⟩
      · exact ⟨2,Or.inl h⟩
    · have hh := (Mole.mem_dartsAt M b w).mpr (mem_singleton.mp hwb)
      rw [hStarB] at hh
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h
      · exact ⟨3,Or.inl h⟩
      · exact ⟨4,Or.inl h⟩
      · exact ⟨5,Or.inl h⟩
      · exact ⟨6,Or.inl h⟩
  have hprof : (localLabels M e : (D → (Fin d → ℤ)) → (Fin 7 → (Fin d → ℤ))) = actualSevenProfile x y z r s t u := by
    funext κ i
    fin_cases i <;> rfl
  have hat : M.atom t=b := (Mole.mem_dartsAt M b t).mp (by rw [hStarB]; simp)
  have hau : M.atom u=b := (Mole.mem_dartsAt M b u).mp (by rw [hStarB]; simp)
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
    let cq := ∑ i : Fin 5, sharedCoefficients sg true i • doubleFiveProfile x y z r s κ0 i
    let bq := -κ0 r+κ0 s-κ0 t+κ0 u
    let centers := actualSevenProfile x y z r s t u k0
    let Q := F.image (actualSevenProfile x y z r s t u)
    have hbphysical (κ) (hκ : M.IsDecoration L (0 : Mom d) c κ) :
        latticePoint L (-κ r+κ s-κ t+κ u)=c b := by
      have hh := momentum_of_dartsAt_quadruple M L hb hrs hrt hst hu hStarB hκ
      change latticePointHom L (-κ r+κ s-κ t+κ u)=c b
      simp only [map_add,map_sub,map_neg,latticePointHom_apply]
      simpa [Molecule.dartSign,hro,hso,hto,huo,sub_eq_add_neg,add_assoc] using hh
    have hQS : ∀ k ∈ Q, SevenLabelSource L sg aq cq bq
        (β a) (∑ v ∈ U, β v) (β b) (δ⁻¹*L^(-2*γ)) ((U.card : ℝ)+1)
        (L^(-γ+η)) centers k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκA := (hmem κ).mp hκ
      refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_⟩
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
        have hm := virtual_cut_shared_integer_eq M hLp.ne' ha hxy hxz hyz hxr hxs hrs hA U hU hcut hκA.1 hκ0.1 second
        have he := virtual_cut_shared_energy M L γ δ hτ ha hxy hxz hyz hxr hxs hrs hA U hU hcut hκA.1 hκA.2.1 second
        constructor
        · cases second <;> exact hm
        · exact he
      · change -κ r+κ s-κ t+κ u=bq
        apply latticePointHom_injective hLp.ne'
        exact (hbphysical κ hκA.1).trans (hbphysical κ0 hκ0.1).symm
      · have hh := energy_of_dartsAt_quadruple M L γ δ hb hrs hrt hst hu hStarB hκA.2.1
        simpa [Molecule.dartSign,hro,hso,hto,huo,actualSevenProfile,sub_eq_add_neg] using hh
      · change ‖latticePoint L (κ t)-k0 t‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 t
      · change ‖latticePoint L (κ u)-k0 u‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 u
      · have hh := hAdm κ hκA.2.2 t u (hat.trans hau.symm) (by rw [hto,huo]; decide)
        change L^(-γ+η) ≤ ‖latticePoint L (κ t-κ u)‖
        simpa only [WeylSums.latticePoint_sub_eq,Molecule.kvec,zero_add] using hh
    have hQbound := hB L hLR δ hδ ((U.card : ℝ)+1)
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) sg hcap aq cq bq
      (β a) (∑ v ∈ U, β v) (β b) centers Q hQS
    have hlocal := card_deletedLabels_image_le_localLabels_image M {a,b} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    rw [hprof] at hlocal
    have hImage : (deletedLabels M {a,b} '' A).ncard = (F.image (deletedLabels M {a,b})).card := by
      have he : deletedLabels M {a,b} '' A = (F.image (deletedLabels M {a,b}) : Set _) := by
        rw [Finset.coe_image,hf.coe_toFinset]
      rw [he,Set.ncard_coe_finset]
    have hreal : ((deletedLabels M {a,b} '' A).ncard : ℝ) ≤ C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(4*((d : ℝ)-γ)-min γ (1-γ)-η) := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {a,b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      exact hh.trans hQbound
    have hnat : (deletedLabels M {a,b} '' A).ncard ≤ ⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(4*((d : ℝ)-γ)-min γ (1-γ)-η)⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {a,b} '' A).ncard : ℕ∞) ≤ (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^3*L^(4*((d : ℝ)-γ)-min γ (1-γ)-η)⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {a,b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
