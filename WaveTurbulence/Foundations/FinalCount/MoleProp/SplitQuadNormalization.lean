/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadDeletion
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadScalar
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.ThreeLabelNormalization
import Mathlib.Tactic

/-! # Normalization of the actual mixed-cut four-label branch

This branch helper takes the actual circuit change as graph data. The
source beta operation must produce it, along with the cut and ordered
star. No local count or normalized deviation is assumed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp

theorem split_quad_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L → ∀ C1 ≥ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ v ∈ M.atoms, ∀ x y r s : D, x ≠ y → x ≠ r → y ≠ r → s ∉ ({x,y,r} : Finset D) →
      M.dartsAt v = {x,y,r,s} →
      M.out x = false → M.out y = true → M.out r = false → M.out s = true →
    ∀ U : Finset V, U ⊆ M.atoms → Degen.boundaryDarts M U = {M.mate x,M.mate y} →
      (Degen.eraseAtoms M {v}).circuitRank = M.circuitRank-2 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (((U.card : ℝ)+1)^2*L^(-η))*
          countAFree (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d) (erasedFreeAdmissibility M {v} Adm) P := by
  classical
  obtain ⟨C,R,hC,hCount⟩ := split_quad_deletion_bound d hd γ hγ η hη hηmax
  refine ⟨max (max R 1) (((C+1)*(δ⁻¹)^2)^(η⁻¹)),?_⟩
  intro L hL hlog C1 hC1 V D _ _ _ M hsimp v hv x y r s hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut hχ Adm P hAdm
  have hLR : R ≤ L := (le_max_left R 1).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right R 1).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hlog0 : 0 < Real.log L^2 := by have hh : 0 < Real.log L := zero_lt_one.trans_le hlog; positivity
  have hP : ∀ T ∈ ladderCells M, 0 ≤ P T := by rw [ladderCells_eq_empty_of_simple M hsimp]; simp
  have hsimp' := simple_eraseAtoms M {v} hsimp
  have hP' : ∀ T ∈ ladderCells (Degen.eraseAtoms M {v}), 0 ≤ P T := by
    rw [ladderCells_eq_empty_of_simple _ hsimp']; simp
  have hprod : cellProduct M L γ δ P = cellProduct (Degen.eraseAtoms M {v}) L γ δ P := by
    rw [cellProduct_eq_one_of_simple M hsimp,cellProduct_eq_one_of_simple _ hsimp']
  have hc := hCount L hLR δ hδ M v hv x y r s hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut Adm hAdm
  have hh := countAFree_le_ratio_of_countEFree_le M (Degen.eraseAtoms M {v}) L γ δ C1 (0 : Mom d)
    Adm (erasedFreeAdmissibility M {v} Adm) P P _ hc
    (freeNormalization_pos M (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP).le
    (freeNormalization_pos _ (d := d) (γ := γ) hLp hδ.1 hC1p hlog0 P hP')
  have hj : M.circuitRank-(Degen.eraseAtoms M {v}).circuitRank = 2 := by omega
  have hr := freeNormalization_ratio_of_product_eq M (Degen.eraseAtoms M {v}) (d := d) (γ := γ)
    hLp hδ.1 hC1p P hprod (by rw [cellProduct_eq_one_of_simple _ hsimp']; norm_num)
  rw [hj] at hr
  norm_num only [Int.cast_ofNat,zpow_ofNat] at hr
  have hB0 : 0 ≤ C1⁻¹*δ^(1/2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hC1p.le) (Real.rpow_nonneg hδ.1.le _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 := by
    have hδhalf : δ^(1/2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have hCinv : C1⁻¹ ≤ 1 := (inv_le_one₀ hC1p).mpr hC1
    simpa only [one_mul] using mul_le_mul hCinv hδhalf (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)
  have ha : η ≤ (d : ℝ)-γ := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := min_le_left γ (1-γ)
    linarith only [hηmax,hm,hdR,hγ.2]
  have hN : 1 ≤ (U.card : ℝ)+1 := by have hn : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _; linarith
  have hscl := split_quad_scalar_le_gain hL1 ha hη hN hδ hB0 hB1 hC ((le_max_right _ _).trans hL)
  have hscl' : (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η))⌉₊ : ℝ)*
      freeNormalization M (d := d) L γ δ C1 P / freeNormalization (Degen.eraseAtoms M {v}) (d := d) L γ δ C1 P ≤
      ((U.card : ℝ)+1)^2*L^(-η) := by
    rw [mul_div_assoc,hr,show -((d : ℝ)-γ)*2 = -2*((d : ℝ)-γ) by ring]
    simpa only [mul_assoc] using hscl
  exact hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hscl') bot_le)

end WaveTurbulence.MoleProp
