/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreBareLinear
public import WaveTurbulence.Foundations.SumintPar.SourceBadLinearBounds

/-!
# Actual case-(b) and case-(d) coarse-core power bounds

The core mass includes the literal case-(b) momentum multiplier. The
case-(d) loss is the established F23 linear loss, paid by its weight gain.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- Cases (b) and (d) have no collapsed first pair in their distinguished core. -/
theorem no_special_pair_of_kind_b_or_d {d : ℕ} (D : SumintDatum d) (i : Fin D.S.I)
    (hi : D.badKind i = 1 ∨ D.badKind i = 3)
    (a : Σ j : Fin D.S.I, Fin (D.S.m j)) (hai : a.1 = i) : ¬ (caseAPair D a ∨ caseCPair D a) := by
  intro ha
  have hk : D.badKind a.1 = 0 ∨ D.badKind a.1 = 2 := by
    rcases ha with ha | ha
    · exact Or.inl ha.2.1
    · exact Or.inr ha.2.1
  rw [hai] at hk
  rcases hi with hi | hi <;> rcases hk with hk | hk <;> rw [hi] at hk <;> norm_num at hk

/-- TARGET sumint Step 3: actual bare bad cores keep the case-(b) gain or the permitted F23 case-(d) loss. -/
theorem exists_source_bare_linear_core_power_bound (d : ℕ) {γ : ℝ} (hγ : γ ∈ Ioo (0:ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (η : ℝ), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c h : ℝ) (i : Fin D.S.I), h ∈ Icc (0:ℝ) 1 → D.S.nor i = false →
      D.badKind i = 1 ∨ D.badKind i = 3 →
      (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inl i) z) ≤
        ENNReal.ofReal (L^((d:ℝ)-γ+(if D.badKind i = 3 then 3*gammaBase γ/2 else -gammaBase γ/2))) := by
  obtain ⟨RB,hRB,hB⟩ := exists_source_case_b_linear_bound d hγ δ hδ hδsmall
  obtain ⟨RD,hRD,hDlinear⟩ := exists_source_case_d_linear_bound d hγ δ hδ hδsmall
  refine ⟨max RB RD,hRB.trans (le_max_left _ _),?_⟩
  intro L hL D η hγη p ν r hr hrupper t c h i hh hnor hi
  have hLB : RB ≤ L := (le_max_left _ _).trans hL
  have hLD : RD ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hRB,hLB]
  have hcore := lintegral_sourceCore_bare_linear_le D hLp γ δ η p ν r t c h i hnor
    (no_special_pair_of_kind_b_or_d D i hi)
  rcases hi with hi | hi
  · have hr0 : r ≠ 0 := by
      intro hzero
      rw [hzero,norm_zero] at hr
      exact (one_div_pos.mpr hLp).not_ge hr
    have hkind : D.badKind i ≠ 3 := by rw [hi]; norm_num
    simp only [caseBMultiplier,hnor,hi,and_self,ite_true] at hcore
    simpa only [ite_eq_right hkind,sub_eq_add_neg,neg_div] using hcore.trans (hB L hLB D η hγη p ν r hr0 hrupper t c h i hh)
  · have hkind : D.badKind i ≠ 1 := by rw [hi]; norm_num
    simp only [caseBMultiplier,hkind,and_false,ite_false,one_mul] at hcore
    simpa only [ite_eq_left hi] using hcore.trans (hDlinear L hLD D η hγη p ν r hr hrupper t c h i hh)

end WaveTurbulence.SumintPar
