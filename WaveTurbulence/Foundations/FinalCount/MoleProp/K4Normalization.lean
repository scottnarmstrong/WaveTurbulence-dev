/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4ActualCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4NormalizationScalar
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleNormalization
import Mathlib.Tactic

/-! # DH23 Proposition 10.3: the actual terminal K4 estimate -/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
namespace WaveTurbulence.MoleProp

theorem K4_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/200) :
    ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ C1 ≥ (1 : ℝ),
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ x, M.atom x ≠ M.atom (M.mate x)) →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
      M.atoms.Nonempty → (∀ a ∈ M.atoms, 3 ≤ M.deg a) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) → M.circuitRank = 3 →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        ENNReal.ofReal (L^(-min γ (1-γ)-η)) := by
  classical
  obtain ⟨C,hC,hB⟩ := K4_countEFree_bound d hd γ hγ
  let g := min γ (1-γ)
  have hg : 0 < g := lt_min hγ.1 (by linarith only [hγ.2])
  have hηg : η < g/100 := by linarith only [hηmax,hg]
  intro δ hδ
  obtain ⟨R,hR⟩ := hB δ hδ
  refine ⟨max (max R 1) (((C+1)*(δ^3)⁻¹)^((g/100-η)⁻¹)),?_⟩
  intro L hL C1 hC1 V D _ _ _ M hM hloop hsimple hne hmin hconn hrank Adm P
  have hLR : R ≤ L := (le_max_left R 1).trans ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right R 1).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hC1p : 0 < C1 := zero_lt_one.trans_le hC1
  have hB0 : 0 ≤ C1⁻¹*δ^(1/2 : ℝ) :=
    mul_nonneg (inv_nonneg.mpr hC1p.le) (Real.rpow_nonneg hδ.1.le _)
  have hB1 : C1⁻¹*δ^(1/2 : ℝ) ≤ 1 := by
    have hδhalf : δ^(1/2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    have hCinv : C1⁻¹ ≤ 1 := (inv_le_one₀ hC1p).mpr hC1
    simpa only [one_mul] using mul_le_mul hCinv hδhalf (Real.rpow_nonneg hδ.1.le _) (by norm_num : (0 : ℝ) ≤ 1)
  have ha : (101 : ℝ)/100*g ≤ 3*((d : ℝ)-γ) := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hgg : g ≤ γ := min_le_left _ _
    linarith only [hdR,hgg,hγ.2]
  have hs := K4_deletion_scalar_le_gain hL1 ha hηg hδ hB0 hB1 hC.le ((le_max_right _ _).trans hL)
  have hc := hR L hLR M hM hloop hsimple hne hmin hconn hrank Adm
  have hc' := ENat.toENNReal_mono hc
  rw [countAFree_eq_of_simple M hsimple,hrank]
  norm_num only [Int.cast_ofNat,zpow_ofNat] at *
  calc
    _ ≤ (⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*g)⌉₊ : ℝ≥0∞) *
        ENNReal.ofReal (L^(-((d : ℝ)-γ)*3)*(C1⁻¹*δ^(1/2 : ℝ))^3) :=
      mul_le_mul_of_nonneg_right hc' bot_le
    _ = ENNReal.ofReal ((⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*g)⌉₊ : ℝ)*
        L^(-3*((d : ℝ)-γ))*(C1⁻¹*δ^(1/2 : ℝ))^3) := by
      rw [show -((d : ℝ)-γ)*3 = -3*((d : ℝ)-γ) by ring]
      have hh : ENNReal.ofReal ((⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*g)⌉₊ : ℝ)*
          (L^(-3*((d : ℝ)-γ))*(C1⁻¹*δ^(1/2 : ℝ))^3)) =
          (⌈C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(101 : ℝ)/100*g)⌉₊ : ℝ≥0∞)*
          ENNReal.ofReal (L^(-3*((d : ℝ)-γ))*(C1⁻¹*δ^(1/2 : ℝ))^3) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
      simpa only [mul_assoc] using hh.symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hs

end WaveTurbulence.MoleProp
