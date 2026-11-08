/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1TM

/-! # RT-GATE (ii), fork C: `RtOneOn` on type-1 couples

The partner root below its window (`rt1t_t1_fix`) or in its layer (`rt1t_t1_move`); the windowed signed ambient
`CplAmbient` supplies the raw embedding data of `tc_t1_cohR`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A finite constant in front of the budget, into the real constant of `RtOneOn`. -/
theorem rt1t_conv {C : ℝ≥0∞} (hC : C < ⊤) {Ct X : ℝ} (hX : 0 ≤ X) (hle : C.toReal ≤ Ct) (Y : ℝ≥0∞) :
    C * ENNReal.ofReal X * Y ≤ ENNReal.ofReal (Ct * X) * Y := by
  refine mul_le_mul' ?_ le_rfl
  rw [ENNReal.ofReal_mul ((ENNReal.toReal_nonneg).trans hle)]
  refine mul_le_mul' ?_ le_rfl
  calc C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
    _ ≤ ENNReal.ofReal Ct := ENNReal.ofReal_le_ofReal hle

theorem rt1t_budget_nonneg {P : WTParams} (hL : 1 ≤ P.L) (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (c' : ℝ) (n g : ℕ)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) :
    0 ≤ P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P n g) * leaf * CS)) := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have := rb_nonneg hC1 hδ hL0 n g
  have := Real.rpow_nonneg hL0 (4 * c')
  have : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  positivity

/-- **`RtOneOn` on type-1 couples.** -/
theorem rt1t_T1 {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT1 := by
  obtain ⟨C₁, hC₁, hfix⟩ := rt1t_t1_fix hθ0 hθ1
  obtain ⟨C₂, hC₂, hmove⟩ := rt1t_t1_move hθ0 hθ1
  refine ⟨C₁.toReal + C₂.toReal, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hC11 hθc p hp nr hn Q LGc hwf hsz hdec hle j hC q' hq' hamb hj hjb hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  obtain ⟨c, Q₁, Q₂, Q₃, rfl⟩ := hC
  obtain ⟨LG₁, LG₂, LG₃, h, hlA, hlB, hlC⟩ := T1Data.exists_of_decodes LGc c Q₁ Q₂ Q₃ hdec hwf
  obtain ⟨w', Hm, a, b, hcan, hE, hsa, hsb, -, -, hlay⟩ := hamb
  have hL1 := K.hL
  have hX := rt1t_budget_nonneg hL1 (by linarith) K.hδ c' (nr - 1)
    (LGc.incoherency (RegCpl.type1 c Q₁ Q₂ Q₃).links) (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _ :
      0 ≤ leafSizeProduct LGc Bc) (starCost_nonneg' S cω)
  rcases hr.lt_or_eq with hlt | heq
  · refine (hfix K hFC hc' hC11 hθc hp hn h hlA hlB hlC hwf hsz hle hcan hE hsa hsb hlay j hj hq' hlt hps hsp
      Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans ?_
    exact rt1t_conv hC₁ hX (le_add_of_nonneg_right ENNReal.toReal_nonneg) _
  · refine (hmove K hFC hc' hC11 hθc hp hn h hlA hlB hlC hwf hsz hle hcan hE hsa hsb hlay j hj hq' heq hps hsp
      Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k).trans ?_
    exact rt1t_conv hC₂ hX (le_add_of_nonneg_left ENNReal.toReal_nonneg) _

end WaveTurbulence.Flower.ProtRT
