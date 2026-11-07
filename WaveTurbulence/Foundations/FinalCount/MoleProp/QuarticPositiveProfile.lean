/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.ActualAffineDoubleEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.TriplePositivePair
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairOrientations
import Mathlib.Tactic

/-! # Conditional finite-family positive-pair estimate at a quartic star

This is a conditional helper, not a source endpoint. Actual cut wrappers
must derive the bridge-label dependence before applying it.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem conditional_quartic_positive_profile_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    ∀ p q x y z r s : D, x ≠ y → x ≠ z → y ≠ z → p ≠ q → p ≠ r → q ≠ r →
      s ∉ ({p,q,r} : Finset D) → M.out s=M.out r →
      M.dartsAt a={x,y,z} → M.dartsAt b={p,q,r,s} →
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (F : Finset (D → (Fin d → ℤ))),
      (∀ κ ∈ F, M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ) →
      (∀ κ ∈ F, ∀ κ' ∈ F,
        sharedFirstProfile (doubleFiveProfile x y z r s κ)=sharedFirstProfile (doubleFiveProfile x y z r s κ') →
          κ p=κ' p ∧ κ q=κ' q) →
      ((F.image (doubleFiveProfile x y z r s)).card : ℝ) ≤
        C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := triple_positive_pair_count_bound d hd γ hγ
  refine ⟨C+1,max R 1,add_pos_of_nonneg_of_pos hC zero_lt_one,?_⟩
  intro L hL δ hδ V D _ _ _ M hM a ha b hb p q x y z r s hxy hxz hyz hpq hpr hqr hs hout hA hStarB c β k0 F hF hfixed
  have hLR := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  by_cases hne : F.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let first := fun κ : D → (Fin d → ℤ) => sharedFirstProfile (doubleFiveProfile x y z r s κ)
    let Ref : (Fin 3 → (Fin d → ℤ)) → (D → (Fin d → ℤ)) := fun v =>
      if h : ∃ κ ∈ F, first κ=v then Classical.choose h else κ0
    have href (κ) (hκ : κ ∈ F) : Ref (first κ) ∈ F ∧ first (Ref (first κ))=first κ := by
      have hh : ∃ κ' ∈ F, first κ'=first κ := ⟨κ,hκ,rfl⟩
      simp only [Ref,dif_pos hh]
      exact Classical.choose_spec hh
    let nk := fun v => Ref v r+Ref v s
    let bp := fun v => doubleSign (M.out r) • (β b-M.dartSign p*‖latticePoint L (Ref v p)‖^2-
      M.dartSign q*‖latticePoint L (Ref v q)‖^2)
    let sg : Fin 3 → Bool := ![M.out x,M.out y,M.out z]
    let aq := doubleSign (M.out x) • κ0 x+doubleSign (M.out y) • κ0 y+doubleSign (M.out z) • κ0 z
    let centers : Fin 5 → Mom d := ![k0 x,k0 y,k0 z,k0 r,k0 s]
    let Q := F.image (doubleFiveProfile x y z r s)
    have hcap : ¬(sg 0=sg 1 ∧ sg 1=sg 2) := not_all_out_equal_of_triple_star M hM ha hxy hxz hyz hA
    have hQS : ∀ k ∈ Q, TriplePositiveSource L sg aq (β a) (δ⁻¹*L^(-2*γ)) centers nk bp k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκD := (hF κ hκ).1
      have hκR := (hF κ hκ).2
      have hrefF := (href κ hκ).1
      have hRefD := (hF _ hrefF).1
      obtain ⟨hp,hq⟩ := hfixed κ hκ _ hrefF (href κ hκ).2.symm
      have hm := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA hκD
      have hm0 := momentum_of_dartsAt_triple M L ha hxy hxz hyz hA (hF κ0 hκ0).1
      have he := energy_of_dartsAt_triple M L γ δ ha hxy hxz hyz hA hκR
      have hbM := momentum_of_dartsAt_quadruple M L hb hpq hpr hqr hs hStarB hκD
      have hbM0 := momentum_of_dartsAt_quadruple M L hb hpq hpr hqr hs hStarB hRefD
      have hbE := energy_of_dartsAt_quadruple M L γ δ hb hpq hpr hqr hs hStarB hκR
      have hsSign : M.dartSign s=M.dartSign r := by simp only [Molecule.dartSign,hout]
      have hpair : κ r+κ s=nk (first κ) := by
        dsimp only [nk]
        apply latticePointHom_injective hLp.ne'
        simp only [map_add,latticePointHom_apply]
        have hh := hbM.trans hbM0.symm
        rw [hp,hq,hsSign] at hh
        have hh' : M.dartSign r • (latticePoint L (κ r)+latticePoint L (κ s)) =
            M.dartSign r • (latticePoint L (Ref (first κ) r)+latticePoint L (Ref (first κ) s)) := by
          have : M.dartSign p • latticePoint L (Ref (first κ) p)+M.dartSign q • latticePoint L (Ref (first κ) q)+
              M.dartSign r • (latticePoint L (κ r)+latticePoint L (κ s)) =
            M.dartSign p • latticePoint L (Ref (first κ) p)+M.dartSign q • latticePoint L (Ref (first κ) q)+
              M.dartSign r • (latticePoint L (Ref (first κ) r)+latticePoint L (Ref (first κ) s)) := by
            simpa only [smul_add,add_assoc] using hh
          exact add_left_cancel this
        cases ho : M.out r <;> simpa only [Molecule.dartSign,ho,Bool.false_eq_true,ite_false,ite_true,neg_one_smul,one_smul,neg_inj] using hh'
      have hpairE : |‖latticePoint L (κ r)‖^2+‖latticePoint L (κ s)‖^2-bp (first κ)| ≤ δ⁻¹*L^(-2*γ) := by
        rw [hp,hq,hsSign] at hbE
        cases ho : M.out r
        · simp only [Molecule.dartSign,ho,Bool.false_eq_true,ite_false,neg_one_mul] at hbE
          dsimp only [bp]
          simp only [ho,doubleSign,Bool.false_eq_true,ite_false,neg_one_zsmul]
          rw [← abs_neg] at hbE
          convert hbE using 1 <;> congr 1 <;> simp only [Molecule.dartSign] <;> ring
        · simp only [Molecule.dartSign,ho,ite_true,one_mul] at hbE
          dsimp only [bp]
          simp only [ho,doubleSign,ite_true,one_smul]
          convert hbE using 1 <;> congr 1 <;> simp only [Molecule.dartSign] <;> ring
      refine ⟨?_,?_,?_,hpair,hpairE⟩
      · intro i
        fin_cases i
        · change ‖latticePoint L (κ x)-k0 x‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκR.2 x
        · change ‖latticePoint L (κ y)-k0 y‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκR.2 y
        · change ‖latticePoint L (κ z)-k0 z‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκR.2 z
        · change ‖latticePoint L (κ r)-k0 r‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκR.2 r
        · change ‖latticePoint L (κ s)-k0 s‖ ≤ 1
          simpa only [Molecule.kvec,zero_add] using hκR.2 s
      · apply latticePointHom_injective hLp.ne'
        dsimp only [aq]
        simp only [map_sum,map_add,map_zsmul,latticePointHom_apply]
        simpa [sg,aq,sharedFirstProfile,doubleFiveProfile,Fin.sum_univ_succ,doubleSign_out_smul,add_assoc] using hm.trans hm0.symm
      · simpa [sg,sharedFirstProfile,doubleFiveProfile,Fin.sum_univ_succ,zsmul_eq_mul,doubleSign_out_cast,add_assoc] using he
    have hh := hB L hLR δ hδ sg hcap aq (β a) centers nk bp Q hQS
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg δ⁻¹))
      (Real.rpow_nonneg hLp.le _))
  · have hFempty : F=∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hFempty,image_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg hC zero_le_one) (sq_nonneg _)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.MoleProp
