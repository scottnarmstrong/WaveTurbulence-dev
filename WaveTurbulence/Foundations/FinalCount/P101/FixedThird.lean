/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarFixedEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapPair
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FixedThirdPair
public import WaveTurbulence.Foundations.FinalCount.P101.Basic
import Mathlib.Tactic

/-! # DH23 Proposition 10.1: three-valent star with one fixed label

The prescribed dart is actual graph data. The remaining labels obey the
canonical local pair constraints obtained from the original three-dart
conservation and energy equations, with arbitrary old charges.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The enumerated actual star count. The only fixed-label premise is a
prescribed third incidence, not a cardinality or normalized estimate. -/
theorem star_three_fixed_third_count_bound_at (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (v : V), v ∈ M.atoms → ∀ e : Fin 3 ≃ IncidentDart M v,
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (q : Fin d → ℤ)
      (S : Finset (D → (Fin d → ℤ))),
      (∀ κ ∈ S, M.IsDecoration L (0 : Mom d) c κ ∧
        M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ LargeGapAt M v L γ η (0 : Mom d) κ ∧
        κ (e 2).val = q) →
      ((S.image (starLabels M v)).card : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ)-γ-η) := by
  classical
  obtain ⟨C,R,hC,hbound⟩ := large_gap_pair_bound d hdim γ hγ η hη hηmax
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V' D' _ _ _ M v hv e c β k0 q S hS
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  by_cases hne : S.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let eps := pairUnit (M.out (e 0).val) (M.out (e 1).val)
    let nk := κ0 (e 0).val + (eps : ℤ) • κ0 (e 1).val
    let β' := if M.out (e 0).val then β v - M.dartSign (e 2).val * ‖latticePoint L q‖^2
      else -(β v - M.dartSign (e 2).val * ‖latticePoint L q‖^2)
    let f := fun t : IncidentDart M v → (Fin d → ℤ) => (t (e 0),t (e 1))
    let T := (S.image (starLabels M v)).image f
    have hcard : T.card = (S.image (starLabels M v)).card :=
      card_image_of_injOn (fixedThirdPair_injOn M v e S q (fun κ hκ => (hS κ hκ).2.2.2))
    have hgap : eps = -1 → L^(-γ+η) ≤ ‖latticePoint L nk‖ := by
      intro heps
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
      rw [hnk,WeylSums.latticePoint_sub_eq]
      simpa only [Molecule.kvec,zero_add] using (hS κ0 hκ0).2.2.1 (e 0).val (e 1).val
        (e 0).property (e 1).property hdir
    obtain ⟨hf,hb⟩ := hbound L ((le_max_left R 1).trans hL) δ hδ
      (k0 (e 0).val) (k0 (e 1).val) nk β' eps hgap
    have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
        CountLemmas.atomPairSet L (k0 (e 0).val) (k0 (e 1).val) nk β' (δ⁻¹*L^(-2*γ)) eps := by
      intro t ht
      obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hz
      have hd := (hS κ hκ).1
      have hr := (hS κ hκ).2.1
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels] using hr.2 (e 0).val
      · simpa only [CountLemmas.NearLattice,Molecule.kvec,zero_add,f,starLabels] using hr.2 (e 1).val
      · exact ordered_fixed_third_integer_momentum_eq M hLp.ne' hv e hd (hS κ0 hκ0).1
          (hS κ hκ).2.2.2 (hS κ0 hκ0).2.2.2
      · exact ordered_fixed_third_energy M L γ δ hv e hr (hS κ hκ).2.2.2
    have hn : T.card ≤ (CountLemmas.atomPairSet L (k0 (e 0).val) (k0 (e 1).val) nk β' (δ⁻¹*L^(-2*γ)) eps).ncard := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
    have hnR : (T.card : ℝ) ≤ (CountLemmas.atomPairSet L (k0 (e 0).val) (k0 (e 1).val) nk β' (δ⁻¹*L^(-2*γ)) eps).ncard := by exact_mod_cast hn
    rw [hcard] at hnR
    exact hnR.trans hb
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [image_empty,card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _)

/-- DH23 Proposition 10.1 fixed-label branch: the prescribed actual dart
is placed last internally, using only the actual degree-three identity. -/
theorem star_three_fixed_incident_count_bound_at (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (v : V), v ∈ M.atoms → M.deg v = 3 →
    ∀ (x : D), M.atom x = v →
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (q : Fin d → ℤ)
      (S : Finset (D → (Fin d → ℤ))),
      (∀ κ ∈ S, M.IsDecoration L (0 : Mom d) c κ ∧
        M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ LargeGapAt M v L γ η (0 : Mom d) κ ∧ κ x = q) →
      ((S.image (starLabels M v)).card : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ)-γ-η) := by
  obtain ⟨C,R,hC,hB⟩ := star_three_fixed_third_count_bound_at d hdim γ hγ η hη hηmax
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ V' D' _ _ _ M v hv hdeg x hx c β k0 q S hS
  obtain ⟨e,he⟩ := exists_three_enumeration_last M hdeg x hx
  apply hB L hL δ hδ M v hv e c β k0 q S
  intro κ hκ
  obtain ⟨hd,hr,hg,hq⟩ := hS κ hκ
  exact ⟨hd,hr,hg,by simpa only [he] using hq⟩

end WaveTurbulence.FinalCountG8.P101
