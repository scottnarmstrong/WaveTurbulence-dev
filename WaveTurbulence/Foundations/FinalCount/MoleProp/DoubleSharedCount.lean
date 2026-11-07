/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoubleSharedSigns
public import WaveTurbulence.Foundations.FinalCount.MoleProp.TriplePositivePair
import Mathlib.Tactic

/-! # All virtual two-shared-label quad signs, without a balance premise

Equal remaining signs use a conditional positive pair. Opposite signs
use the balanced model when the shared signs differ, and the genuine
unbalanced selector1 model when they agree.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

private theorem same_sign_pair_reduction {E : Type*} [AddCommGroup E] (sign : Bool)
    (x y rest b : E) (X Y restE β τ : ℝ)
    (hm : -rest+doubleSign sign • x+doubleSign sign • y=b)
    (he : |-restE+doubleSign sign • X+doubleSign sign • Y-β| ≤ τ) :
    x+y=doubleSign sign • (b+rest) ∧ |X+Y-doubleSign sign • (β+restE)| ≤ τ := by
  cases sign
  · simp only [doubleSign,Bool.false_eq_true,ite_false,neg_one_zsmul] at hm he ⊢
    constructor
    · rw [← hm]; abel
    · obtain ⟨hl,hu⟩ := abs_le.mp he
      apply abs_le.mpr
      constructor <;> linarith
  · simp only [doubleSign,ite_true,one_smul] at hm he ⊢
    constructor
    · rw [← hm]; abel
    · obtain ⟨hl,hu⟩ := abs_le.mp he
      apply abs_le.mpr
      constructor <;> linarith

private theorem doubleShared_first_sum {E : Type*} [AddCommGroup E]
    (sg : Fin 5 → Bool) (k : Fin 5 → E) :
    (∑ i : Fin 5, doubleSharedCoefficients sg false i • k i)=
      ∑ i : Fin 3, doubleSign (sharedFirstProfile sg i) • sharedFirstProfile k i := by
  simp [doubleSharedCoefficients,sharedFirstProfile,Fin.sum_univ_succ]

/-- The remaining same-sign pair is normalized from the literal source
equations, rather than assumed to obey a fiber-count estimate. -/
theorem doubleSharedSource_to_positive_pair {d : ℕ} (L : ℝ) (sg : Fin 5 → Bool)
    (hpair : sg 3=sg 4) (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ)
    (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ))
    (hk : SignedDoubleSharedSource L sg a b β₁ β₂ τ centers k) :
    TriplePositiveSource L (sharedFirstProfile sg) a β₁ τ centers
      (fun q => doubleSign (sg 3) • (b+doubleSign (sg 0) • q 0+doubleSign (sg 1) • q 1))
      (fun q => doubleSign (sg 3) • (β₂+doubleSign (sg 0) • ‖latticePoint L (q 0)‖^2+
        doubleSign (sg 1) • ‖latticePoint L (q 1)‖^2)) k := by
  obtain ⟨hn,hs⟩ := hk
  have hm : -(doubleSign (sg 0) • k 0+doubleSign (sg 1) • k 1)+
      doubleSign (sg 3) • k 3+doubleSign (sg 3) • k 4=b := by
    simpa [doubleSharedCoefficients,Fin.sum_univ_succ,← hpair,neg_add,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using (hs true).1
  have he : |-(doubleSign (sg 0) • ‖latticePoint L (k 0)‖^2+doubleSign (sg 1) • ‖latticePoint L (k 1)‖^2)+
      doubleSign (sg 3) • ‖latticePoint L (k 3)‖^2+doubleSign (sg 3) • ‖latticePoint L (k 4)‖^2-β₂| ≤ τ := by
    have hh := (hs true).2
    simp only [doubleSharedCoefficients,ite_true,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,zero_smul,add_zero,neg_smul,← hpair] at hh
    simp only [zsmul_eq_mul] at hh ⊢
    change |-(↑(doubleSign (sg 0))*‖latticePoint L (k 0)‖^2)+
      (-(↑(doubleSign (sg 1))*‖latticePoint L (k 1)‖^2)+
        (0+(↑(doubleSign (sg 3))*‖latticePoint L (k 3)‖^2+
          ↑(doubleSign (sg 3))*‖latticePoint L (k 4)‖^2)))-β₂| ≤ τ at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hp := same_sign_pair_reduction (sg 3) (k 3) (k 4)
    (doubleSign (sg 0) • k 0+doubleSign (sg 1) • k 1) b
    (‖latticePoint L (k 3)‖^2) (‖latticePoint L (k 4)‖^2)
    (doubleSign (sg 0) • ‖latticePoint L (k 0)‖^2+doubleSign (sg 1) • ‖latticePoint L (k 1)‖^2) β₂ τ hm he
  refine ⟨hn,?_,?_,?_,?_⟩
  · exact (doubleShared_first_sum sg k).symm.trans (hs false).1
  · simpa only [doubleShared_first_sum,sharedFirstProfile,Bool.false_eq_true,ite_false] using (hs false).2
  · simpa [sharedFirstProfile,add_assoc] using hp.1
  · simpa [sharedFirstProfile,add_assoc] using hp.2

private theorem labels_comp_injective {K : Type*} (p : Fin 5 ≃ Fin 5) :
    Function.Injective (fun k : Fin 5 → K => fun i => k (p i)) := by
  intro k k' h
  funext i
  obtain ⟨j,rfl⟩ := p.surjective i
  exact congrFun h j

/-- Literal local source bound for a mixed first triple and any virtual
quad with its two shared coefficients opposite the first. -/
theorem signed_double_shared_base_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (sg : Fin 5 → Bool), ¬(sg 0=sg 1 ∧ sg 1=sg 2) →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, SignedDoubleSharedSource L sg a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨Cb,Rb,hCb,hB⟩ := signed_double_five_local_count_bound d hd γ hγ
  obtain ⟨Cu,Ru,_hCu,hU⟩ := unbalanced_double_local_count_bound d hd γ hγ
  obtain ⟨Cp,Rp,_hCp,hP⟩ := triple_positive_pair_count_bound d hd γ hγ
  let C := max Cb (max Cu Cp)
  refine ⟨C,max (max Rb (max Ru Rp)) 1,hCb.trans_le (le_max_left _ _),?_⟩
  intro L hL δ hδ sg hfirst a b β₁ β₂ centers S hS
  have hLbase : max Rb (max Ru Rp) ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := zero_le_one.trans ((le_max_right _ _).trans hL)
  have hmono {A : ℝ} (hA : A ≤ C) : A*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) ≤
      C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (sq_nonneg δ⁻¹)) (Real.rpow_nonneg hL0 _)
  by_cases hpair : sg 3=sg 4
  · have hfirst' : ¬(sharedFirstProfile sg 0=sharedFirstProfile sg 1 ∧
        sharedFirstProfile sg 1=sharedFirstProfile sg 2) := hfirst
    have hp := hP L ((le_max_right Ru Rp).trans ((le_max_right Rb _).trans hLbase)) δ hδ
      (sharedFirstProfile sg) hfirst' a β₁ centers
      (fun q => doubleSign (sg 3) • (b+doubleSign (sg 0) • q 0+doubleSign (sg 1) • q 1))
      (fun q => doubleSign (sg 3) • (β₂+doubleSign (sg 0) • ‖latticePoint L (q 0)‖^2+
        doubleSign (sg 1) • ‖latticePoint L (q 1)‖^2)) S
      (fun k hk => doubleSharedSource_to_positive_pair L sg hpair a b β₁ β₂ _ centers k (hS k hk))
    exact hp.trans (hmono ((le_max_right Cu Cp).trans (le_max_right Cb _)))
  · by_cases hshared : sg 0=sg 1
    · let p := doubleSharedUnbalancedPermutation sg
      let T := S.image (fun k => fun i => k (p i))
      have hc : T.card=S.card := card_image_of_injective _ (labels_comp_injective p)
      have hu := hU L ((le_max_left Ru Rp).trans ((le_max_right Rb _).trans hLbase)) δ hδ
        (doubleSign (sg 0) • a) (doubleSign (sg 0) • b) (doubleSign (sg 0) • β₁) (doubleSign (sg 0) • β₂)
        (fun i => centers (p i)) T ?_
      · rw [hc] at hu
        exact hu.trans (hmono ((le_max_left Cu Cp).trans (le_max_right Cb _)))
      · intro z hz
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
        exact doubleSharedSource_to_unbalanced L sg hfirst hshared hpair a b β₁ β₂ _ centers k (hS k hk)
    · let p := doubleSharedBalancedPermutation sg
      let T := S.image (fun k => fun i => k (p i))
      have hc : T.card=S.card := card_image_of_injective _ (labels_comp_injective p)
      have hb := hB L ((le_max_left Rb _).trans hLbase) δ hδ (sg 0) (sg 1) (sg 2) hfirst
        a b β₁ β₂ (fun i => centers (p i)) T ?_
      · rw [hc] at hb
        exact hb.trans (hmono (le_max_left Cb _))
      · intro z hz
        obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
        exact doubleSharedSource_to_balanced L sg hshared hpair a b β₁ β₂ _ centers k (hS k hk)

/-- Enlarging both source windows by N costs N squared. No degree-four
balance assumption is added to this virtual-star model. -/
theorem signed_double_shared_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ N ≥ (1 : ℝ),
    ∀ (sg : Fin 5 → Bool), ¬(sg 0=sg 1 ∧ sg 1=sg 2) →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, SignedDoubleSharedSource L sg a b β₁ β₂ (N*(δ⁻¹*L^(-2*γ))) centers k) →
      (S.card : ℝ) ≤ C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  obtain ⟨C,R,hC,hB⟩ := signed_double_shared_base_count_bound d hd γ hγ
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ N hN sg hfirst a b β₁ β₂ centers S hS
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hδN : δ/N ∈ Set.Ioc (0 : ℝ) 1 := ⟨div_pos hδ.1 hNp,(div_le_one hNp).mpr (hδ.2.trans hN)⟩
  have hτ : (δ/N)⁻¹*L^(-2*γ)=N*(δ⁻¹*L^(-2*γ)) := by rw [inv_div,div_eq_mul_inv]; ring
  have hb := hB L hL (δ/N) hδN sg hfirst a b β₁ β₂ centers S (fun k hk => by rw [hτ]; exact hS k hk)
  have he : C*(δ/N)⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) =
      C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by rw [inv_div,div_eq_mul_inv]; ring
  exact hb.trans_eq he

end WaveTurbulence.MoleProp
