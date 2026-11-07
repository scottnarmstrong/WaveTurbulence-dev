/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedSignedCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapPair
import Mathlib.Tactic

/-! # The seven-label count in DH23 Proposition 10.3 case (2)

Five labels satisfy the actual virtual-triple source system. Conditional
on these labels, the remaining opposite pair retains the original energy
window and its actual large gap. No local counting bound is a premise.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def sevenFirstFive {K : Type*} (k : Fin 7 → K) : Fin 5 → K :=
  fun i => k ⟨i.val,by omega⟩

def SevenLabelSource {d : ℕ} (L : ℝ) (sg : Fin 6 → Bool) (a c b : Fin d → ℤ)
    (βa βcut βb τ N gap : ℝ) (centers : Fin 7 → Mom d) (k : Fin 7 → (Fin d → ℤ)) : Prop :=
  SignedSharedSource L sg a c βa βcut (N*τ) (sevenFirstFive centers) (sevenFirstFive k) ∧
    -k 3+k 4-k 5+k 6=b ∧
    |-‖latticePoint L (k 3)‖^2+‖latticePoint L (k 4)‖^2-
      ‖latticePoint L (k 5)‖^2+‖latticePoint L (k 6)‖^2-βb| ≤ τ ∧
    NearLattice L (centers 5) (k 5) ∧ NearLattice L (centers 6) (k 6) ∧
    gap ≤ ‖latticePoint L (k 5-k 6)‖

private theorem seven_fiber_pair_injOn {d : ℕ} (S : Finset (Fin 7 → (Fin d → ℤ)))
    (q : Fin 5 → (Fin d → ℤ)) :
    Set.InjOn (fun k : Fin 7 → (Fin d → ℤ) => (k 5,k 6))
      ((S.filter fun k => sevenFirstFive k=q) : Set (Fin 7 → (Fin d → ℤ))) := by
  intro k hk k' hk' he
  have hp : sevenFirstFive k=sevenFirstFive k' := (mem_filter.mp hk).2.trans (mem_filter.mp hk').2.symm
  funext i
  fin_cases i
  · exact congrFun hp 0
  · exact congrFun hp 1
  · exact congrFun hp 2
  · exact congrFun hp 3
  · exact congrFun hp 4
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem seven_label_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ N ≥ (1 : ℝ),
    ∀ (sg : Fin 6 → Bool), SharedMixed sg false →
    ∀ (a c b : Fin d → ℤ) (βa βcut βb : ℝ) (centers : Fin 7 → Mom d)
      (S : Finset (Fin 7 → (Fin d → ℤ))),
      (∀ k ∈ S, SevenLabelSource L sg a c b βa βcut βb (δ⁻¹*L^(-2*γ)) N
        (L^(-γ+η)) centers k) →
      (S.card : ℝ) ≤ C*N^2*(δ⁻¹)^3*L^(4*((d : ℝ)-γ)-min γ (1-γ)-η) := by
  classical
  obtain ⟨Cf,Rf,hCf,hFive⟩ := signed_shared_count_bound d hd γ hγ
  obtain ⟨Cp,Rp,hCp,hPair⟩ := large_gap_pair_bound d hd γ hγ η hη hηmax
  refine ⟨Cf*Cp,max (max Rf Rp) 1,mul_nonneg hCf.le hCp,?_⟩
  intro L hL δ hδ N hN sg hsg a c b βa βcut βb centers S hS
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hLf : Rf ≤ L := (le_max_left Rf Rp).trans ((le_max_left _ _).trans hL)
  have hLp' : Rp ≤ L := (le_max_right Rf Rp).trans ((le_max_left _ _).trans hL)
  let F := S.image sevenFirstFive
  have hFirst : ∀ k ∈ F, SignedSharedSource L sg a c βa βcut (N*(δ⁻¹*L^(-2*γ)))
      (sevenFirstFive centers) k := by
    intro k hk
    change k ∈ S.image sevenFirstFive at hk
    obtain ⟨k7,hk7,hval⟩ := mem_image.mp hk
    simpa only [hval] using (hS k7 hk7).1
  have hF := hFive L hLf δ hδ N hN sg hsg a c βa βcut (sevenFirstFive centers) F hFirst
  let nk := fun q : Fin 5 → (Fin d → ℤ) => -q 3+q 4-b
  let bp := fun q : Fin 5 → (Fin d → ℤ) => -‖latticePoint L (q 3)‖^2+‖latticePoint L (q 4)‖^2-βb
  have hPairData {q k} (hk : k ∈ S.filter (fun k => sevenFirstFive k=q)) :
      k 5-k 6=nk q ∧
      |‖latticePoint L (k 5)‖^2-‖latticePoint L (k 6)‖^2-bp q| ≤ δ⁻¹*L^(-2*γ) := by
    obtain ⟨hk,hkq⟩ := mem_filter.mp hk
    obtain ⟨_h1,hm,he,_h5,_h6,_hg⟩ := hS k hk
    have h3 : k 3=q 3 := congrFun hkq 3
    have h4 : k 4=q 4 := congrFun hkq 4
    constructor
    · calc
        k 5-k 6 = -k 3+k 4-b := by rw [← hm]; abel
        _ = nk q := by rw [h3,h4]
    · have heq : ‖latticePoint L (k 5)‖^2-‖latticePoint L (k 6)‖^2-bp q =
          -(-‖latticePoint L (k 3)‖^2+‖latticePoint L (k 4)‖^2-
            ‖latticePoint L (k 5)‖^2+‖latticePoint L (k 6)‖^2-βb) := by
        dsimp only [bp]
        rw [← h3,← h4]
        ring
      rw [heq,abs_neg]
      exact he
  have hFiber (q : Fin 5 → (Fin d → ℤ)) :
      ((S.filter fun k => sevenFirstFive k=q).card : ℝ) ≤ Cp*δ⁻¹*L^((d : ℝ)-γ-η) := by
    let K := S.filter (fun k => sevenFirstFive k=q)
    by_cases hne : K.Nonempty
    · obtain ⟨k0,hk0⟩ := hne
      have hnk := (hPairData hk0).1
      have hgap := (hS k0 (mem_filter.mp hk0).1).2.2.2.2.2
      rw [hnk] at hgap
      obtain ⟨hf,hb⟩ := hPair L hLp' δ hδ (centers 5) (centers 6) (nk q) (bp q) (-1) (fun _ => hgap)
      let T := K.image (fun k => (k 5,k 6))
      have hcard : T.card=K.card := card_image_of_injOn (seven_fiber_pair_injOn S q)
      have hsub : (T : Set _) ⊆ atomPairSet L (centers 5) (centers 6) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) (-1) := by
        intro z hz
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
        have hd := hPairData hk
        have hsrc := hS k (mem_filter.mp hk).1
        exact ⟨hsrc.2.2.2.1,hsrc.2.2.2.2.1,
          by simpa only [Units.val_neg,Units.val_one,neg_one_zsmul,sub_eq_add_neg] using hd.1,
          by simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_mul,one_mul,sub_eq_add_neg] using hd.2⟩
      have hn := Set.ncard_le_ncard hsub hf
      rw [Set.ncard_coe_finset,hcard] at hn
      have hnR : (K.card : ℝ) ≤ (atomPairSet L (centers 5) (centers 6) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) (-1)).ncard := by exact_mod_cast hn
      exact hnR.trans hb
    · have he : K=∅ := not_nonempty_iff_eq_empty.mp hne
      change (K.card : ℝ) ≤ _
      rw [he,card_empty,Nat.cast_zero]
      exact mul_nonneg (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _)
  have hc : S.card=∑ q ∈ F, (S.filter fun k => sevenFirstFive k=q).card :=
    card_eq_sum_card_fiberwise (fun k hk => mem_image.mpr ⟨k,hk,rfl⟩)
  have hcR : (S.card : ℝ)=∑ q ∈ F, ((S.filter fun k => sevenFirstFive k=q).card : ℝ) := by exact_mod_cast hc
  rw [hcR]
  calc
    _ ≤ ∑ _q ∈ F, Cp*δ⁻¹*L^((d : ℝ)-γ-η) := sum_le_sum (fun q _ => hFiber q)
    _ = (F.card : ℝ)*(Cp*δ⁻¹*L^((d : ℝ)-γ-η)) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (Cf*N^2*(δ⁻¹)^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)))*(Cp*δ⁻¹*L^((d : ℝ)-γ-η)) :=
      mul_le_mul_of_nonneg_right hF
        (mul_nonneg (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _))
    _ = _ := by
      rw [show 4*((d : ℝ)-γ)-min γ (1-γ)-η =
        (3*((d : ℝ)-γ)-min γ (1-γ))+((d : ℝ)-γ-η) by ring,Real.rpow_add hLp]
      ring

end WaveTurbulence.MoleProp
