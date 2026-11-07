/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairStars
import Mathlib.Tactic

/-! # The five-label count for any `(3,4)` double pair (DH23 basiccount(4)), no cell needed

Copy of G6's `double_pair_three_four_five_count_bound` with the stars from `stars34` (degrees and caps only).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem pair34_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
      a ≠ b → M.deg a = 3 → M.deg b = 4 → M.bondsBetween a b = 2 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := signed_double_five_local_count_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb hab ha3 hb4 hdouble Adm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  obtain ⟨x,y,r,s,t,hxy,hxr,hyr,hmxy,hmxs,hmys,ht,hA,hStarB,hout⟩ := stars34 M hM.1 ha hb hab ha3 hb4 hdouble
  have hcap := not_all_out_equal_of_triple_star M hM ha hxy hxr hyr hA
  have hto : M.out t = doubleExtraSign (M.out x) (M.out y) (M.out r) :=
    extra_out_of_paired_star M hM hb hmxy hmxs hmys ht hStarB hout
  let e : Fin 5 → D := ![x,y,r,s,t]
  have hcover := deleted_pair_coverage_three_four M hA hStarB
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
    let aq := doubleSign (M.out x) • κ0 x+doubleSign (M.out y) • κ0 y+doubleSign (M.out r) • κ0 r
    let bq := -(doubleSign (M.out x) • κ0 x)-doubleSign (M.out y) • κ0 y-doubleSign (M.out r) • κ0 s+
      doubleSign (doubleExtraSign (M.out x) (M.out y) (M.out r)) • κ0 t
    let centers := ![k0 x,k0 y,k0 r,k0 s,k0 t]
    let Q := F.image (doubleFiveProfile x y r s t)
    have hQS : ∀ k ∈ Q, SignedDoubleFiveSource L (M.out x) (M.out y) (M.out r) aq bq
        (β a) (β b) (δ⁻¹*L^(-2*γ)) centers k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκA := (hmem κ).mp hκ
      have hMom := source_double_five_integer_momentum_eq M hLp.ne' ha hb hxy hxr hyr hmxy hmxs hmys ht hA hStarB hout hto hκA.1 hκ0.1
      have hEnergy := source_double_five_energy M L γ δ ha hb hxy hxr hyr hmxy hmxs hmys ht hA hStarB hout hto hκA.1 hκA.2.1
      refine ⟨hMom,?_,hEnergy⟩
      intro i
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
    have hQbound := hB L hLR δ hδ (M.out x) (M.out y) (M.out r) hcap aq bq (β a) (β b) centers Q hQS
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


end WaveTurbulence.FinalCountG8
