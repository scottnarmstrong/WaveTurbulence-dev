/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceLowGammaNormalBlock
public import WaveTurbulence.Foundations.SumintPar.SourceHighGammaNormalBlock
public import WaveTurbulence.Foundations.SumintPar.SourceLowGammaNormalIncoherence

/-!
# The normal-block estimate in the exact source product

The same beta/20 incoherence reserve holds in both gamma ranges.
In the high-gamma range every normal block has that reserve, so no
endpoint-strip estimate is needed there. In the low-gamma range the
half-moment estimate supplies it precisely for discrepant labels.
The exponential-in-size constant is chosen before delta and Dsteps.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- The literal label discrepancy counted for one normal block in the source M₀. -/
@[expose] def normalIncoherent {d : ℕ} (D : SumintDatum d)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : Prop :=
  ¬ (D.q (.inr (.inr ⟨i,0⟩)) = D.q (.inr (.inr ⟨i,1⟩)) ∧
    D.q (.inr (.inr ⟨i,1⟩)) = D.q (.inr (.inr ⟨i,2⟩)))

/-- TARGET sumint Step 2: a uniform actual normal-block bound with the exact discrepancy indicator. -/
theorem exists_source_normal_block_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar)
    (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/16 →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N → γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c : ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}),
      linearFactorMass D L γ δ p ν r t c (L^(-β)) i.1 *
        normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c (L^(-β)))
          (enlargedTimeUpper D c (L^(-β))) i ≤
      ENNReal.ofReal (C*δ^(-2:ℝ)*L^(4*((d:ℝ)-γ)-(if normalIncoherent D i then β/20 else 0))) := by
  by_cases hg : 1/2 < γ
  · refine ⟨1,le_rfl,?_⟩
    intro δ hδ hδsmall
    obtain ⟨R,hR,hbound⟩ := exists_high_gamma_source_normal_block_bound d hd γ ⟨hg,hγ.2⟩
      τstar hτstar (β/20) (hhigh hg) δ hδ hδsmall
    refine ⟨R,hR,?_⟩
    intro L hL D N hτ A η hD hγη p ν r hr hrupper t c i
    have hL1 : 1 ≤ L := by linarith [hR.trans hL]
    have hLp : 0 < L := zero_lt_one.trans_le hL1
    have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩
    apply (hbound L hL D N hτ A η hD hγη p ν r hr hrupper t c (L^(-β)) i hh).trans
    apply ENNReal.ofReal_le_ofReal
    rw [one_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
    apply Real.rpow_le_rpow_of_exponent_le hL1
    split_ifs <;> linarith only [hβ]
  · have hg' : γ ∈ Ioc (0:ℝ) (1/2) := ⟨hγ.1,le_of_not_gt hg⟩
    obtain ⟨C,R,hC,hR,hbound⟩ := exists_low_gamma_source_normal_block_bound d hd γ hg' τstar hτstar
    refine ⟨C,hC,?_⟩
    intro δ hδ hδsmall
    have hδ1 : δ ≤ 1 := by linarith only [hδsmall]
    obtain ⟨R',hR',hinc⟩ := exists_low_gamma_source_normal_incoherence_bound d hd γ hg' τstar hτstar
      β hβ hβγ δ ⟨hδ,hδ1⟩
    refine ⟨max R R',hR.trans (le_max_left _ _),?_⟩
    intro L hL D N hτ A η hD hγη p ν r hr hrupper t c i
    have hLR : R ≤ L := (le_max_left _ _).trans hL
    have hLR' : R' ≤ L := (le_max_right _ _).trans hL
    have hL1 : 1 ≤ L := by linarith [hR.trans hLR]
    have hLp : 0 < L := zero_lt_one.trans_le hL1
    by_cases hq : normalIncoherent D i
    · rw [ite_eq_left hq]
      apply (hinc L hLR' D N hτ A η hD p ν r t c i hq).trans
      apply ENNReal.ofReal_le_ofReal
      have hδpow : 1 ≤ δ^(-2:ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by norm_num)
      have hcoeff : 1 ≤ C*δ^(-2:ℝ) := by nlinarith only [hC,hδpow]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff
        (Real.rpow_nonneg hLp.le (4*((d:ℝ)-γ)-β/20))
    · rw [ite_eq_right hq,sub_zero]
      exact hbound L hLR D δ N ⟨hδ,hδ1⟩ hτ A η hD p ν r t c (L^(-β)) i
        ⟨Real.rpow_nonneg hLp.le _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hβ])⟩

end WaveTurbulence.SumintPar
