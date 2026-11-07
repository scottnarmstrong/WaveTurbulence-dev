/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103GoodConfiguration
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SharedTripleNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ThreeCutNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SevenLabelNormalization
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualAffineSharedDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualAffineInsideDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualAffineDoubleDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualPositiveQuarticDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.GoodCoefficient
import Mathlib.Tactic

/-! # Actual local good-configuration counting assembly

All local counts are proved from old stars and old cuts. The geometric
selector must produce the input configuration; the source proposition
does not assume a good operation or its local counting estimate.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

private theorem star4_last_not_mem {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {b : V} {p q : D} (B : Star4Remainder M b p q) :
    B.s ∉ ({p,q,B.r} : Finset D) := by
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨Ne.symm B.xs,Ne.symm B.ys,Ne.symm B.rs⟩

private theorem cut_scale_le_size {V : Type*} (U A : Finset V) (hU : U ⊆ A) :
    (U.card : ℝ)+1 ≤ (A.card : ℝ)+1 := by
  have hh : (U.card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hU
  linarith only [hh]

theorem actual_good_configuration_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ),
    ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ a ∈ M.atoms, ActualGoodConfiguration M a →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
    ∃ b ∈ M.atoms, a ≠ b ∧
      ((M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank=3 ∧
        countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (C*((M.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ)))*
            countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P) ∨
       (M.circuitRank-(Degen.eraseAtoms M {a,b}).circuitRank=4 ∧
        countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (C*((M.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-(min γ (1-γ)+η)))*
            countAFree (Degen.eraseAtoms M {a,b}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) P)) := by
  classical
  obtain ⟨Cs,Rs,hCs,hS⟩ := actual_shared_triples_normalized_bound d hd γ hγ
  obtain ⟨Ca,Ra,hCa,hA⟩ := actual_affine_shared_deletion_count_bound d hd γ hγ
  obtain ⟨Ci,Ri,hCi,hI⟩ := actual_affine_inside_deletion_count_bound d hd γ hγ
  obtain ⟨Cd,Rd,hCd,hD⟩ := actual_affine_double_deletion_count_bound d hd γ hγ
  obtain ⟨Cp,Rp,hCp,hP⟩ := actual_positive_quartic_cut_deletion_count_bound d hd γ hγ
  obtain ⟨Ct,Rt,hCt,hT⟩ := actual_three_cut_normalized_bound d hd γ hγ
  obtain ⟨Cv,Rv,hCv,hV⟩ := seven_label_normalized_bound d hd γ hγ η hη hηmax
  let C := Cs+Ca+Ci+Cd+Cp+Ct+Cv+10
  let R := max Rs (max Ra (max Ri (max Rd (max Rp (max Rt Rv)))))
  have hsC : Cs ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have haC : Ca+1 ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have hiC : Ci+1 ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have hdC : Cd+1 ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have hpC : Cp+1 ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have htC : Ct ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  have hvC : Cv ≤ C := by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv]
  refine ⟨C,max R 1,by dsimp [C]; linarith only [hCs,hCa,hCi,hCd,hCp,hCt,hCv],?_⟩
  intro L hL hlog C1 hC1 δ hδ V D _ _ _ M hM hsimp a ha hG Adm P hAdm
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hR : Rs ≤ L ∧ Ra ≤ L ∧ Ri ≤ L ∧ Rd ≤ L ∧ Rp ≤ L ∧ Rt ≤ L ∧ Rv ≤ L := by
    simpa only [R,max_le_iff] using (le_max_left R 1).trans hL
  rcases hR with ⟨hRs,hRa,hRi,hRd,hRp,hRt,hRv⟩
  have hone : (1 : ℝ) ≤ (M.atoms.card : ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  cases hG with
  | sharedCubic b hb hab x A B loss =>
    refine ⟨b,hb,hab,Or.inl ⟨loss,?_⟩⟩
    have hh := hS L hRs hlog C1 hC1 δ hδ M hM hsimp a ha b hb x A.y A.z B.y B.z
      A.xy A.xz A.yz B.xy B.xz B.yz A.star B.star loss Adm P
    have hc := good_coefficient_le (gain := min γ (1-γ)) hCs.le hsC (show (0 : ℝ) ≤ 1 by norm_num) hone hδ.1.le hL0
    have hc' : Cs*(δ⁻¹)^3*L^(-min γ (1-γ)) ≤ C*((M.atoms.card : ℝ)+1)^2*(δ⁻¹)^3*L^(-min γ (1-γ)) := by
      simpa only [one_pow,mul_one] using hc
    exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc') bot_le)
  | affineCubic b hb hab x p A B px pmx inside U hU cut loss =>
    refine ⟨b,hb,hab,Or.inl ⟨loss,?_⟩⟩
    cases inside
    · have hc := hA L hRa δ hδ M hM a ha b hb p x A.y A.z B.y B.z
        A.xy A.xz A.yz B.xy B.xz B.yz px A.star B.star U hU cut Adm
      exact three_loss_normalization_of_count_bound M (Degen.eraseAtoms M {a,b}) hd hγ hL1 hlog hδ hC1 hCa.le haC
        (le_add_of_nonneg_left (Nat.cast_nonneg _)) (cut_scale_le_size U M.atoms hU)
        hsimp (simple_eraseAtoms M {a,b} hsimp) loss Adm (erasedFreeAdmissibility M {a,b} Adm) P hc
    · have hc := hI L hRi δ hδ M hM a ha b hb p x A.y A.z B.y B.z
        A.xy A.xz A.yz B.xy B.xz B.yz pmx A.star B.star U hU cut Adm
      exact three_loss_normalization_of_count_bound M (Degen.eraseAtoms M {a,b}) hd hγ hL1 hlog hδ hC1 hCi.le hiC
        (le_add_of_nonneg_left (Nat.cast_nonneg _)) (cut_scale_le_size U M.atoms hU)
        hsimp (simple_eraseAtoms M {a,b} hsimp) loss Adm (erasedFreeAdmissibility M {a,b} Adm) P hc
  | affineQuartic b hb hab x p A B py U hU cut loss =>
    refine ⟨b,hb,hab,Or.inl ⟨loss,?_⟩⟩
    have hc := hD L hRd δ hδ M hM a ha b hb p x A.y A.z B.r B.s
      A.xy A.xz A.yz B.xy B.xr B.yr (star4_last_not_mem B) py A.star B.star U hU cut Adm
    exact three_loss_normalization_of_count_bound M (Degen.eraseAtoms M {a,b}) hd hγ hL1 hlog hδ hC1 hCd.le hdC
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) (cut_scale_le_size U M.atoms hU)
      hsimp (simple_eraseAtoms M {a,b} hsimp) loss Adm (erasedFreeAdmissibility M {a,b} Adm) P hc
  | positiveQuartic b hb hab x p q A B same cutp cutq loss =>
    refine ⟨b,hb,hab,Or.inl ⟨loss,?_⟩⟩
    have hc := hP L hRp δ hδ M hM a ha b hb p q x A.y A.z B.r B.s
      A.xy A.xz A.yz B.xy B.xr B.yr (star4_last_not_mem B) same A.star B.star cutp cutq Adm
    have hc' : countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈Cp*1^2*(δ⁻¹)^2*L^(3*((d : ℝ)-γ)-min γ (1-γ))⌉₊ : ℕ∞)*
          countEFree (Degen.eraseAtoms M {a,b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a,b} Adm) := by
      simpa only [one_pow,mul_one] using hc
    exact three_loss_normalization_of_count_bound M (Degen.eraseAtoms M {a,b}) hd hγ hL1 hlog hδ hC1 hCp.le hpC
      (le_refl (1 : ℝ)) hone hsimp (simple_eraseAtoms M {a,b} hsimp) loss Adm (erasedFreeAdmissibility M {a,b} Adm) P hc'
  | threeCutQuartic b hb hab x p q A B pmx qmx U₀ U₁ U₂ hU₀ hU₁ hU₂ cut₀ cut₁ cut₂ loss =>
    refine ⟨b,hb,hab,Or.inl ⟨loss,?_⟩⟩
    have hh := hT L hRt hlog C1 hC1 δ hδ M hM hsimp a ha b hb p q x A.y A.z B.r B.s
      A.xy A.xz A.yz B.xy B.xr B.yr (star4_last_not_mem B) pmx qmx A.star B.star
      U₀ U₁ U₂ hU₀ hU₁ hU₂ cut₀ cut₁ cut₂ loss Adm P
    have hc := good_coefficient_le hCt.le htC
      (zero_le_one.trans (le_add_of_nonneg_left (Nat.cast_nonneg U₀.card)))
      (cut_scale_le_size U₀ M.atoms hU₀) hδ.1.le hL0 (gain := min γ (1-γ))
    exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) bot_le)
  | sevenLabelQuartic b hb hab x p q A B xp xq po qo ro so U hU cut loss =>
    refine ⟨b,hb,hab,Or.inr ⟨loss,?_⟩⟩
    have hh := hV L hRv hlog C1 hC1 δ hδ M hM hsimp a ha b hb x A.y A.z p q B.r B.s
      A.xy A.xz A.yz xp xq B.xy B.xr B.yr (star4_last_not_mem B) A.star B.star po qo ro so
      U hU cut loss Adm P hAdm
    have hc := good_coefficient_le hCv.le hvC
      (zero_le_one.trans (le_add_of_nonneg_left (Nat.cast_nonneg U.card)))
      (cut_scale_le_size U M.atoms hU) hδ.1.le hL0 (gain := min γ (1-γ)+η)
    exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) bot_le)

end WaveTurbulence.MoleProp
