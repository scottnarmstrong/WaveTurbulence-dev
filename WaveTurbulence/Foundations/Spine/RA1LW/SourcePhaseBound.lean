/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalClassifiedProfile
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Uniform elementary bounds on the original source phase integrals -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory MainCoef Set

/-- The original couple phase has unit modulus at every time array. -/
theorem norm_cplPhase_eq_one (G : Garden 2) (α : Fin 2 × TTree.Path → ℝ)
    (τ : GBranch G.tree → ℝ) : ‖cplPhase G α τ‖ = 1 := by
  unfold cplPhase
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro b _
  rw [Complex.norm_exp]
  simp

/-- The original couple domain lies in the unit cube when both upper
root times are at most1. -/
theorem cplDom_subset_unitCube (G : Garden 2) {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) :
    cplDom G t s ⊆ Icc (0 : GBranch G.tree → ℝ) 1 := by
  intro τ hτ
  constructor
  · intro b
    exact (hτ b).1.le
  · intro b
    have hb := (hτ b).2.1
    split_ifs at hb
    · exact hb.le.trans ht
    · exact hb.le.trans hs

/-- The literal source couple phase integral is uniformly bounded by1,
before selecting any Fourier representation or making a lattice exchange. -/
theorem norm_cplB_le_one (G : Garden 2) {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1)
    (α : Fin 2 × TTree.Path → ℝ) : ‖cplB G t s α‖ ≤ 1 := by
  classical
  have hsub := cplDom_subset_unitCube G ht hs
  have hv : volume (Icc (0 : GBranch G.tree → ℝ) 1) = 1 := by
    rw [Real.volume_Icc_pi]
    simp
  have hfin : volume (Icc (0 : GBranch G.tree → ℝ) 1) < ⊤ := by
    rw [hv]
    exact ENNReal.one_lt_top
  have he : cplB G t s α = ∫ τ in Icc (0 : GBranch G.tree → ℝ) 1,
      (cplDom G t s).indicator (cplPhase G α) τ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro τ hτ
    exact Set.indicator_of_notMem (fun h => hτ (hsub h)) _
  rw [he]
  have hb : ∀ τ ∈ Icc (0 : GBranch G.tree → ℝ) 1,
      ‖(cplDom G t s).indicator (cplPhase G α) τ‖ ≤ (1:ℝ) := by
    intro τ _
    by_cases hτ : τ ∈ cplDom G t s
    · rw [Set.indicator_of_mem hτ,norm_cplPhase_eq_one]
    · rw [Set.indicator_of_notMem hτ]
      simp only [norm_zero,zero_le_one]
  have hh := norm_setIntegral_le_of_norm_le_const hfin hb
  exact hh.trans_eq (by simp [Measure.real,hv])

/-- Layer-zero plain source phase integrals have the same unit bound,
with their original lower endpoint and frozen-parent time parameters. -/
theorem norm_phaseIntegral_layer_zero_le_one {d : ℕ} (L γ δ : ℝ)
    (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0) (hp : LG.garden.IsPlain)
    {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (s₁ s₂ : ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    ‖phaseIntegral L γ δ LG.garden (kDomain LG (fun b => if b.1.1=0 then t else s) s₁) s₂ k‖ ≤ 1 := by
  rw [kDomain_eq_cplDom LG h0 hp ht hs s₁,phaseIntegral_cplDom_eq L γ δ hp]
  exact norm_cplB_le_one LG.garden ht hs _

end WaveTurbulence.RA1Leafwise
