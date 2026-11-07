/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SharedTripleLocal
import Mathlib.Tactic

/-! # The all-same virtual triple in DH23 Proposition 10.3

Fixing the first triple leaves a same-direction pair. Its sharp shell
bound supplies gamma-zero saving uniformly in the shared label. This is
a literal local source count, not an assumed graph good-step estimate.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def sharedFirstProfile {K : Type*} (k : Fin 5 → K) : Fin 3 → K :=
  fun i => k ⟨i.val,by omega⟩

def sharedFirstSigns (sg : Fin 6 → Bool) : Fin 3 → Bool :=
  fun i => sg ⟨i.val,by omega⟩

theorem shared_first_sum {E : Type*} [AddCommGroup E] (sg : Fin 6 → Bool) (k : Fin 5 → E) :
    (∑ i : Fin 5, sharedCoefficients sg false i • k i) =
      ∑ i : Fin 3, doubleSign (sharedFirstSigns sg i) • sharedFirstProfile k i := by
  simp [sharedCoefficients,sharedFirstSigns,sharedFirstProfile,Fin.sum_univ_succ]

theorem shared_first_fiber_pair_injOn {K : Type*} [DecidableEq K]
    (S : Finset (Fin 5 → K)) (q : Fin 3 → K) :
    Set.InjOn (fun k : Fin 5 → K => (k 3,k 4)) (S.filter fun k => sharedFirstProfile k=q) := by
  intro k hk k' hk' hp
  have he : sharedFirstProfile k=sharedFirstProfile k' := (mem_filter.mp hk).2.trans (mem_filter.mp hk').2.symm
  funext i
  fin_cases i
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 2
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

/-- After fixing the first three labels, an all-same second star is a
literal positive atom-pair counting problem. -/
theorem shared_same_sign_fiber_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ≤ 1)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (sg : Fin 6 → Bool) (hall : sg 3=sg 4 ∧ sg 4=sg 5)
    (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d)
    (S : Finset (Fin 5 → (Fin d → ℤ)))
    (hS : ∀ k ∈ S, SignedSharedSource L sg a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k)
    (q : Fin 3 → (Fin d → ℤ)) :
    ((S.filter fun k => sharedFirstProfile k=q).card : ℝ) ≤
      (3^(d-2)*(2*(6*Real.pi+1284002)))*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
  classical
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let F := S.filter fun k => sharedFirstProfile k=q
  let T := F.image (fun k => (k 3,k 4))
  let nk := doubleSign (sg 3) • b-q 0
  let β := doubleSign (sg 3) • β₂-‖latticePoint L (q 0)‖^2
  have hcard : T.card = F.card := card_image_of_injOn (shared_first_fiber_pair_injOn S q)
  have hf := finite_atomPairSet hLp (centers 3) (centers 4) nk β (δ⁻¹*L^(-2*γ)) 1
  have h34 : sg 4=sg 3 := hall.1.symm
  have h35 : sg 5=sg 3 := (hall.1.trans hall.2).symm
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      atomPairSet L (centers 3) (centers 4) nk β (δ⁻¹*L^(-2*γ)) 1 := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    obtain ⟨hk,hkq⟩ := mem_filter.mp hk
    obtain ⟨hn,hs⟩ := hS k hk
    have hq : k 0=q 0 := congrFun hkq 0
    have hm := (hs true).1
    have he := (hs true).2
    have hm' : k 3+k 4=nk := by
      cases hsign : sg 3 <;> simp [sharedCoefficients,Fin.sum_univ_succ,doubleSign,h34,h35,hsign] at hm
      · dsimp only [nk]
        simp only [hsign,doubleSign,Bool.false_eq_true,ite_false,neg_one_zsmul]
        rw [← hm,← hq]
        abel
      · dsimp only [nk]
        simp only [hsign,doubleSign,ite_true,one_smul]
        rw [← hm,← hq]
        abel
    have he' : |‖latticePoint L (k 3)‖^2+‖latticePoint L (k 4)‖^2-β| ≤ δ⁻¹*L^(-2*γ) := by
      cases hsign : sg 3 <;> simp [sharedCoefficients,Fin.sum_univ_succ,doubleSign,h34,h35,hsign] at he
      · dsimp only [β]
        simp only [hsign,doubleSign,Bool.false_eq_true,ite_false,neg_one_zsmul]
        rw [← hq]
        rw [← abs_neg] at he
        convert he using 1 <;> congr 1 <;> ring
      · dsimp only [β]
        simp only [hsign,doubleSign,ite_true,one_smul]
        rw [← hq]
        convert he using 1 <;> congr 1 <;> ring
    refine ⟨hn 3,hn 4,?_,?_⟩
    · simpa using hm'
    · simpa using he'
  have hn : T.card ≤ (atomPairSet L (centers 3) (centers 4) nk β (δ⁻¹*L^(-2*γ)) 1).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (atomPairSet L (centers 3) (centers 4) nk β (δ⁻¹*L^(-2*γ)) 1).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans (positive_pair_sharp_bound (by omega : 2 ≤ d) hL hδ hγ (centers 3) (centers 4) nk β)

/-- The easy second-star all-same branch is first-triple times positive
pair, with constants uniform in all fixed data. -/
theorem signed_shared_same_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (sg : Fin 6 → Bool), SharedMixed sg false → (sg 3=sg 4 ∧ sg 4=sg 5) →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, SignedSharedSource L sg a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨Ct,R,hCt,hB⟩ := literal_signed_triple_count_bound d hd γ hγ
  let Cp : ℝ := 3^(d-2)*(2*(6*Real.pi+1284002))
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  refine ⟨Ct*Cp,max R 1,mul_nonneg hCt hCp,?_⟩
  intro L hL δ hδ sg hmix hall a b β₁ β₂ centers S hS
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  let F := S.image sharedFirstProfile
  have hsg : ¬(sharedFirstSigns sg 0=sharedFirstSigns sg 1 ∧ sharedFirstSigns sg 1=sharedFirstSigns sg 2) := hmix
  have hFirst : ∀ k ∈ F, (∀ i, NearLattice L (sharedFirstProfile centers i) (k i)) ∧
      (∑ i : Fin 3, doubleSign (sharedFirstSigns sg i) • k i)=a ∧
      |(∑ i : Fin 3, doubleSign (sharedFirstSigns sg i) • ‖latticePoint L (k i)‖^2)-β₁| ≤ δ⁻¹*L^(-2*γ) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    obtain ⟨hn,hs⟩ := hS k hk
    refine ⟨fun i => hn _,?_,?_⟩
    · exact (shared_first_sum sg k).symm.trans (hs false).1
    · simpa only [shared_first_sum,sharedFirstProfile,Bool.false_eq_true,ite_false] using (hs false).2
  have hF := hB L ((le_max_left R 1).trans hL) δ hδ (sharedFirstSigns sg) hsg a β₁ (sharedFirstProfile centers) F hFirst
  have hcard : S.card = ∑ q ∈ F, (S.filter fun k => sharedFirstProfile k=q).card :=
    card_eq_sum_card_fiberwise (fun k hk => mem_image.mpr ⟨k,hk,rfl⟩)
  have hcardR : (S.card : ℝ) = ∑ q ∈ F, ((S.filter fun k => sharedFirstProfile k=q).card : ℝ) := by exact_mod_cast hcard
  rw [hcardR]
  calc
    _ ≤ ∑ _q ∈ F, Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
      apply sum_le_sum
      intro q _hq
      exact shared_same_sign_fiber_bound d hd γ hγ.2.le hL1 hδ sg hall a b β₁ β₂ centers S hS q
    _ = (F.card : ℝ)*(Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ))) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (Ct*δ⁻¹*L^(2*((d : ℝ)-γ)))*(Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ))) :=
      mul_le_mul_of_nonneg_right hF
        (mul_nonneg (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _))
    _ = _ := by
      rw [show (3*((d : ℝ)-γ)-min γ (1-γ)) = 2*((d : ℝ)-γ)+((d : ℝ)-γ-min γ (1-γ)) by ring,
        Real.rpow_add hLp]
      ring

end WaveTurbulence.MoleProp
