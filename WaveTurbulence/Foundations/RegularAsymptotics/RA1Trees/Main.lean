/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRemainderRestriction
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeDominantFactors
public import WaveTurbulence.Foundations.IncohInst.NormBridge

/-! # Exact RA1Tree: DH23 Prop6.1 for original regular tree kernels -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef Set

/-- DH23 Prop6.1 for trees, at the exact pinned REGREF obligation type. Every
coefficient, singular identification, physical remainder and norm input is proved. -/
theorem ra1Tree : Regref.RA1Tree := by
  intro d hd γ hγ
  obtain ⟨η₀,hη₀,hsmall⟩ := exists_couple_eta_range hd hγ
  refine ⟨η₀,hη₀,?_⟩
  intro η hη B
  obtain ⟨hηsmall,hηγ,hηγ',hηsqrt⟩ := hsmall η hη
  let Binput := max B 0
  have hBinput : 0 ≤ Binput := le_max_right _ _
  obtain ⟨Cr,hCr,hr⟩ := exists_tree_remainder_restriction_bound hd hγ hη.1 hηsmall hηγ hηγ' hBinput hηsqrt
  obtain ⟨Cd,hCd,hdFactors⟩ := exists_tree_dominant_factor_bounds hd hη.1 (by linarith) hBinput
  let C := max Cr Cd
  have hC : 1 ≤ C := hCr.trans (le_max_left _ _)
  refine ⟨C,hC,1/2,by norm_num,?_⟩
  intro δ hδ A
  obtain ⟨L₁,hL₁⟩ := hr δ hδ A
  refine ⟨max L₁ 2,?_⟩
  intro L hL F hF n hnlog
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₁ 2).trans hL]
  have hFsp : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B := by
    rw [← NormBridgeScratch.SNormR_eq_spatialNorm]
    exact hF
  have hFinput := hFsp.trans (ENNReal.ofReal_le_ofReal (le_max_left B 0))
  have hgeom (a : ℝ) (ha : 1 ≤ a) (haC : a ≤ C) : a*a^n ≤ C*C^n :=
    mul_le_mul haC (pow_le_pow_left₀ (zero_le_one.trans ha) haC n)
      (pow_nonneg (zero_le_one.trans ha) _) (zero_le_one.trans hC)
  refine ⟨?_,?_⟩
  · intro X hwf hsize LG hX h0
    apply (hL₁ L ((le_max_left _ _).trans hL) F hFinput n hnlog X hwf hsize LG hX h0).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hL1) _)
    exact mul_le_mul (le_max_left Cr Cd)
      (pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hCr) hδ.1.le)
        (mul_le_mul_of_nonneg_right (le_max_left Cr Cd) hδ.1.le) n)
      (pow_nonneg (mul_nonneg (zero_le_one.trans hCr) hδ.1.le) n) (zero_le_one.trans hC)
  · intro X hwf hdom hsize ζ
    have hbox (t : Fin 2 → ℝ) (ht : t ∈ timeBoxGt 0 0) :
        ((t 0∈Icc (0:ℝ) 1) ∧ (t 1∈Icc (0:ℝ) 1)) ∧ t 1<t 0 := by
      simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using ht
    obtain ⟨hTime,hSpace⟩ := hdFactors F hFinput X hwf hdom n hsize ζ (timeBoxGt 0 0)
      (fun t ht i => by fin_cases i; exact (hbox t ht).1.1; exact (hbox t ht).1.2)
      (fun t ht => (hbox t ht).2.le)
    refine ⟨hTime.trans (ENNReal.ofReal_le_ofReal (hgeom Cd hCd (le_max_right Cr Cd))),?_⟩
    intro Z hZ
    rw [NormBridgeScratch.SNormR_eq_spatialNorm]
    have hSpecial : IsSpecialSet (X.treeLinks ζ) Z := (Finset.mem_filter.mp hZ).2
    exact (hSpace Z hSpecial).trans
      (ENNReal.ofReal_le_ofReal (hgeom Cd hCd (le_max_right Cr Cd)))

end WaveTurbulence.RegAsymp
