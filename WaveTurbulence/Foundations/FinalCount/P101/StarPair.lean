/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarPair
public import WaveTurbulence.Foundations.FinalCount.P101.Basic
import Mathlib.Tactic

/-! # DH23 large-gap local pair count with both possible directions -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 basiccount(1) at an actual degree-two star. Same directions use
the sharp shell bound; opposite directions use the actual large-gap
predicate, so the forbidden zero conserved difference is never used. -/
theorem star_two_count_bound_at (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (v : V), v ∈ M.atoms → ∀ e : Fin 2 ≃ IncidentDart M v,
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (S : Finset (D → (Fin d → ℤ))),
      (∀ κ ∈ S, M.IsDecoration L (0 : Mom d) c κ ∧
        M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ LargeGapAt M v L γ η (0 : Mom d) κ) →
      ((S.image (starLabels M v)).card : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ)-γ-η) := by
  classical
  obtain ⟨Cn,R,hB⟩ := CountLemmas.atomCountLemma_bound d hdim γ hγ η hη hηmax
  let Cp : ℝ := 3^(d-2)*(2*(6*Real.pi+1284002))
  let C : ℝ := max Cp (max Cn 0)
  have hC : 0 ≤ C := (le_max_right Cn 0).trans (le_max_right Cp (max Cn 0))
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V' D' _ _ _ M v hv e c β k0 S hS
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  by_cases hne : S.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let eps := pairUnit (M.out (e 0).val) (M.out (e 1).val)
    let nk := κ0 (e 0).val + (eps : ℤ) • κ0 (e 1).val
    let β' := if M.out (e 0).val then β v else -β v
    let a0 := k0 (e 0).val
    let a1 := k0 (e 1).val
    let f := fun q : IncidentDart M v → (Fin d → ℤ) => (q (e 0),q (e 1))
    let T := (S.image (starLabels M v)).image f
    have hcard : T.card = (S.image (starLabels M v)).card := card_image_of_injective _ (starPair_injective M v e)
    have hf := CountLemmas.finite_atomPairSet hLp a0 a1 nk β' (δ⁻¹*L^(-2*γ)) eps
    have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
        CountLemmas.atomPairSet L a0 a1 nk β' (δ⁻¹*L^(-2*γ)) eps := by
      intro q hq
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hq
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp ht
      have hd := (hS κ hκ).1
      have hr := (hS κ hκ).2.1
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels,a0] using hr.2 (e 0).val
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels,a1] using hr.2 (e 1).val
      · exact ordered_pair_integer_momentum_eq M hLp.ne' hv e hd (hS κ0 hκ0).1
      · exact ordered_pair_energy M L γ δ hv e hr
    have hn : T.card ≤ (CountLemmas.atomPairSet L a0 a1 nk β' (δ⁻¹*L^(-2*γ)) eps).ncard := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
    have hnR : (T.card : ℝ) ≤ (CountLemmas.atomPairSet L a0 a1 nk β' (δ⁻¹*L^(-2*γ)) eps).ncard := by exact_mod_cast hn
    rw [hcard] at hnR
    apply hnR.trans
    rcases Int.units_eq_one_or eps with heps | heps
    · rw [heps]
      have hp := positive_pair_sharp_bound (by omega : 2 ≤ d) hL1 hδ hγ.2.le a0 a1 nk β'
      have hη0 : η ≤ min γ (1-γ) := by linarith only [hη,hηmax]
      have hpow := Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith only [hη0] : (d : ℝ)-γ-min γ (1-γ) ≤ (d : ℝ)-γ-η)
      have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
      have hm := mul_le_mul_of_nonneg_left hpow (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le))
      have hc : Cp ≤ C := le_max_left _ _
      exact hp.trans (hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hδ.1.le)) (by positivity)))
    · rw [heps]
      have hdir : M.out (e 0).val ≠ M.out (e 1).val := by
        intro hh
        have he : eps = 1 := by simp only [eps,pairUnit,hh,ite_true]
        have hbad : (1 : ℤˣ) = -1 := he.symm.trans heps
        norm_num at hbad
      have hnk : nk = κ0 (e 0).val - κ0 (e 1).val := by
        dsimp only [nk]
        rw [heps]
        change κ0 (e 0).val + (-1 : ℤ) • κ0 (e 1).val = κ0 (e 0).val - κ0 (e 1).val
        simp only [neg_one_zsmul,sub_eq_add_neg]
      have hgap : L^(-γ+η) ≤ ‖latticePoint L nk‖ := by
        rw [hnk,WeylSums.latticePoint_sub_eq]
        simpa only [Molecule.kvec,zero_add] using (hS κ0 hκ0).2.2 (e 0).val (e 1).val
          (e 0).property (e 1).property hdir
      have hb := (hB L ((le_max_left R 1).trans hL) δ hδ β' nk a0 a1 (0 : Mom d)).2.2.1 hgap
      have hc : Cn ≤ C := (le_max_left Cn 0).trans (le_max_right Cp (max Cn 0))
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hδ.1.le)) (by positivity))
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [image_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.FinalCountG8.P101
