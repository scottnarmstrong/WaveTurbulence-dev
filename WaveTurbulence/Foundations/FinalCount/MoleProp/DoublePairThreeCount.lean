/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSourceEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairCoverage
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ScaleConditions
import Mathlib.Tactic

/-! # Actual paired degree-three deletion with its own ladder-position gain -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem double_pair_three_three_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
      a ≠ b → M.deg a = 3 → M.deg b = 3 → M.bondsBetween a b = 2 →
    ∀ S ∈ ladderCells M, a ∈ S →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
  classical
  obtain ⟨C,hC,hB⟩ := signed_double_pair_local_count_bound d hd γ hγ 2 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨R,hR⟩ := hB δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL V D _ _ _ M hM a ha b hb hab ha3 hb3 hdouble S hS haS Adm P hGap
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hSCell : IsLadderCell M S := (mem_filter.mp hS).2
  have hmeet : ¬ Disjoint S {a,b} := fun h => disjoint_left.mp h haS (by simp)
  obtain ⟨u,v,x,y,r,s,hCell,hUV,hu,hv,hxy,hx,hy,hr,hs,hout,hxr,hyr,hmxy,hmxs,hmys,hA,hB3,_hB4⟩ :=
    exists_double_pair_stars M hM hab ha3 hdouble hSCell hmeet
  have hStarB := hB3 hb3
  have hcap := not_all_out_equal_of_triple_star M hM ha hxy hxr hyr hA
  let e : Fin 4 → D := ![x,y,r,s]
  have hcover := deleted_pair_coverage_three_three M hA hStarB
  have hprof : (localLabels M e : (D → (Fin d → ℤ)) → (Fin 4 → (Fin d → ℤ))) = doublePairProfile x y r s := by
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
    let aq := doubleSign (M.out x) • κ0 x + doubleSign (M.out y) • κ0 y + doubleSign (M.out r) • κ0 r
    let bq := -(doubleSign (M.out x) • κ0 x)-doubleSign (M.out y) • κ0 y-doubleSign (M.out r) • κ0 s
    let centers := ![k0 x,k0 y,k0 r,k0 s]
    have href : SignedDoublePairMomentum (M.out x) (M.out y) (M.out r) aq bq (doublePairProfile x y r s κ0) := by
      constructor <;> rfl
    have hN : ‖latticePoint L (aq+bq)‖ = ‖latticePoint L (κ0 r)-latticePoint L (κ0 s)‖ := by
      simpa only [doublePairProfile_two,doublePairProfile_three] using signed_double_pair_charge_norm L _ _ _ aq bq _ href
    have hrg : M.IsLadderGap L (0 : Mom d) κ0 u v hCell.1
        (latticePoint L (κ0 r)-latticePoint L (κ0 s)) := by
      refine ⟨r,s,?_,?_,hr.1.trans hu.symm,hs.1.trans hv.symm,?_⟩
      · simp only [Molecule.ends,hr.1,hr.2,hu]
        congr 2 <;> apply Fin.ext <;> rfl
      · simp only [Molecule.ends,hs.1,hs.2,hv]
        congr 2 <;> apply Fin.ext <;> rfl
      · simp only [Molecule.gapAt,Molecule.kvec,zero_add]
    have hg := hGap κ0 hκ0.2.2 u v hCell _ hrg
    rw [hUV,← hN] at hg
    have hP : P S = 0 ∨ P S ∈ Set.Icc L⁻¹ 1 := by
      rcases hg with hz | hm | ho
      · exact Or.inl hz.1
      · exact Or.inr ⟨hm.1,hm.2.1.le⟩
      · refine Or.inr ⟨?_,?_⟩
        · rw [ho.1]
          exact (inv_le_one₀ hLp).mpr hL1
        · rw [ho.1]
    have hnorm : 0 < P S → (2 : ℝ)⁻¹*P S ≤ ‖latticePoint L (aq+bq)‖ := by
      intro hp
      rcases hg with hz | hm | ho
      · exact False.elim (hp.ne' hz.1)
      · convert hm.2.2.1 using 1 <;> ring
      · rw [ho.1]
        convert ho.2 using 1 <;> norm_num
    let Q := F.image (doublePairProfile x y r s)
    have hQS : ∀ k ∈ Q, SignedDoublePairSource L (M.out x) (M.out y) (M.out r) aq bq
        (β a) (β b) (δ⁻¹*L^(-2*γ)) centers k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκA := (hmem κ).mp hκ
      have hMom := source_double_pair_integer_momentum_eq M hLp.ne' ha hb hxy hxr hyr hmxy hmxs hmys hA hStarB hout hκA.1 hκ0.1
      have hEnergy := source_double_pair_energy M L γ δ ha hb hxy hxr hyr hmxy hmxs hmys hA hStarB hout hκA.1 hκA.2.1
      refine ⟨hMom,?_,hEnergy⟩
      intro i
      fin_cases i
      · change ‖latticePoint L (κ x) - k0 x‖ ≤ 1
        simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 x
      · change ‖latticePoint L (κ y) - k0 y‖ ≤ 1
        simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 y
      · change ‖latticePoint L (κ r) - k0 r‖ ≤ 1
        simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 r
      · change ‖latticePoint L (κ s) - k0 s‖ ≤ 1
        simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 s
    have hQbound := hR L hLR (M.out x) (M.out y) (M.out r) hcap aq bq (β a) (β b) centers (P S) hP hnorm Q hQS
    change (Q.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹ at hQbound
    have hlocal := card_deletedLabels_image_le_localLabels_image M {a,b} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    rw [hprof] at hlocal
    have hImage : (deletedLabels M {a,b} '' A).ncard = (F.image (deletedLabels M {a,b})).card := by
      have he : deletedLabels M {a,b} '' A = (F.image (deletedLabels M {a,b}) : Set _) := by
        rw [Finset.coe_image,hf.coe_toFinset]
      rw [he,Set.ncard_coe_finset]
    have hreal : ((deletedLabels M {a,b} '' A).ncard : ℝ) ≤
        C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹ := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {a,b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      exact hh.trans hQbound
    have hnat : (deletedLabels M {a,b} '' A).ncard ≤ ⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {a,b} '' A).ncard : ℕ∞) ≤ (⌈C*δ⁻¹*L^(2*((d : ℝ)-γ))*(Molecule.ladderWeight L γ δ (P S))⁻¹⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {a,b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
