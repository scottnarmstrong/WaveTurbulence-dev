/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.CoupleKernelEstimate
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalZeroApp
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceMstarBound
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleParameters
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.RestrictionZero
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleTimeFactor
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs

/-! # DH23 Proposition 6.1 for couples with individually modified leaf inputs (RA1-LEAFWISE)

The leafwise form of `WaveTurbulence.RegAsymp.regular_couple_asymptotics` (RA1Couple, F80 form): the same
statement with the common profile `F` replaced by a leaf-indexed family `H : LeafProfiles 2 d` of real profiles,
each with `𝔖^{40d,40d}` norm at most `B`, the kernel `KQstar` by `LGSpine.coupleLeaves` and the leading term by
the leafwise `LGSpine.LeafApp.couple`. Packet RA1-LEAFWISE; sources DH23 Prop 6.1 (L920–L934), TARGET L2065–2067. -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp MeasureTheory Set Links

private theorem geometric_coefficient_mono {a b δ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hδ : 0 ≤ δ) (n : ℕ) : a*(a*δ)^n ≤ b*(b*δ)^n :=
  mul_le_mul hab (pow_le_pow_left₀ (mul_nonneg ha hδ) (mul_le_mul_of_nonneg_right hab hδ) n)
    (pow_nonneg (mul_nonneg ha hδ) n) (ha.trans hab)

private theorem timeBox_zero_unit (t : Fin 2 → ℝ) (ht : t ∈ timeBox 0 0) (i : Fin 2) :
    t i ∈ Icc (0:ℝ) 1 := by
  have hh : t 0 ∈ Icc (0:ℝ) 1 ∧ t 1 ∈ Icc (0:ℝ) 1 := by
    simpa only [timeBox,Set.mem_ofPred_eq,zero_add] using ht
  fin_cases i
  · exact hh.1
  · exact hh.2

/-- **RA1-LEAFWISE, couples.** DH23 Prop 6.1 (layer 0) with a separate profile at every leaf. -/
theorem ra1_couple_leafwise :
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ B : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₁ → ∀ A : ℝ, ∃ L₀ : ℝ,
  ∀ L : ℝ, L₀ ≤ L → ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
    (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
      (∀ a, LG.layer a = 0) → ∀ H : LGSpine.LeafProfiles 2 d,
      (∀ z, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal B) →
      Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => LGSpine.coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 -
          LGSpine.LeafApp.couple δ 0 H Q (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (C * (C * δ) ^ n * L ^ (-(gam1L d γ - Real.sqrt η)))) ∧
    (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
      XNorm00Restr (V := Unit) (1 - η) (timeBox 0 0) Set.univ
          (fun ts _ => (Q.JB 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n) ∧
        ∀ H : LGSpine.LeafProfiles 2 d, (∀ z, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal B) →
        ∀ Z ∈ specialSets Q.links,
          SNormR (30 * d) (30 * d) (LGSpine.LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
            ENNReal.ofReal (C * C ^ n)) := by
  intro d hd γ hγ
  obtain ⟨η₀,hη₀,hηrange⟩ := exists_couple_eta_range hd hγ
  refine ⟨η₀,hη₀,?_⟩
  intro η hη B
  obtain ⟨hηsmall,hηγ,hηγ',hηrate⟩ := hηrange η hη
  let B₀ := max 0 B
  have hB₀ : 0 ≤ B₀ := le_max_left _ _
  obtain ⟨Ce,hCe,hKernel⟩ := exists_couple_kernel_remainder_bound hd hγ hη.1 hηsmall hηγ hηγ' hB₀
  obtain ⟨Ct,hCt,hTime⟩ := exists_couple_JB_time_bound hη.1 (by linarith : η ≤ 1)
  obtain ⟨Cs,hCs,hSpatial⟩ := literal_Mstar_spatial_bound hd hB₀
  let C := max Ce (max Ct Cs)
  have hCeC : Ce ≤ C := le_max_left _ _
  have hCtC : Ct ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCsC : Cs ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 1 ≤ C := hCe.trans hCeC
  refine ⟨C,hC,1/2,by norm_num,?_⟩
  intro δ hδ A
  obtain ⟨Lk,hKernel⟩ := hKernel A
  obtain ⟨Ld,hDelta⟩ := exists_physical_delta_threshold hη.1 hδ.1
  refine ⟨max 1 (max Lk Ld),?_⟩
  intro L hL n hnlog
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLk : Lk ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLd : Ld ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  constructor
  · intro Q hwf hsize LG hQ h0 H hH
    have hF' : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B₀ := by
      intro z
      have := hH z
      rw [NormBridgeScratch.SNormR_eq_spatialNorm] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (le_max_right 0 B))
    by_cases hn : n = 0
    · have hsize0 : Q.size = 0 := by omega
      have hz : (fun ts : timeBox 0 0 => fun k : (Set.univ : Set (Mom d)) =>
          LGSpine.coupleLeaves L γ δ LG H (ts.val 0) (ts.val 1) k.val -
            LGSpine.LeafApp.couple δ 0 H Q (ts.val 0) (ts.val 1) k.val) = fun _ _ => 0 := by
        funext ts k
        rw [coupleLeaves_eq_app_of_size_zero L γ δ H LG h0 hwf hsize0 hQ
          (timeBox_zero_unit ts.val ts.property 0) (timeBox_zero_unit ts.val ts.property 1) k.val]
        exact sub_self _
      rw [hz,mixedRestrictionNorm_zero]
      exact zero_le
    · have hnpos : 0 < n := by omega
      have hk := hKernel L hLk δ (hDelta L hLd) (by linarith only [hδ.2] : 2*δ ≤ 1)
        n hnpos hnlog Q hwf hsize LG hQ h0 H hF' (timeBox 0 0) timeBox_zero_unit
      apply hk.trans
      apply ENNReal.ofReal_le_ofReal
      have hrate : L^(-ApproxNT.gamma1 d γ+2*η) ≤ L^(-(gam1L d γ-Real.sqrt η)) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        change -ApproxNT.gamma1 d γ+2*η ≤ -(gam1L d γ-Real.sqrt η)
        have hg : ApproxNT.gamma1 d γ = gam1L d γ := rfl
        rw [hg]
        linarith only [hηrate]
      exact mul_le_mul (geometric_coefficient_mono (zero_le_one.trans hCe) hCeC hδ.1.le n)
        hrate (Real.rpow_nonneg (zero_le_one.trans hL1) _)
        (mul_nonneg (zero_le_one.trans hC)
          (pow_nonneg (mul_nonneg (zero_le_one.trans hC) hδ.1.le) n))
  · intro Q hwf hdom hsize
    refine ⟨?_, ?_⟩
    · exact (hTime Q hwf hdom n hsize (timeBox 0 0) timeBox_zero_unit).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [mul_one] using geometric_coefficient_mono (zero_le_one.trans hCt) hCtC
            (by norm_num : (0:ℝ) ≤ 1) n))
    · intro H hH Z hZ
      have hF' : ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B₀ := by
        intro z
        have := hH z
        rw [NormBridgeScratch.SNormR_eq_spatialNorm] at this
        exact this.trans (ENNReal.ofReal_le_ofReal (le_max_right 0 B))
      rw [NormBridgeScratch.SNormR_eq_spatialNorm]
      have hlinks : Q.links.length = n := links_length_eq_half hsize
      have hspecial : IsSpecialSet (Q.linksAt (0,[]) (1,[])) Z :=
        (Finset.mem_filter.mp hZ).2
      have hm := hSpatial Q hdom 2 H hF' Z (0,[]) (1,[]) indep_roots hspecial
      apply hm.trans
      apply ENNReal.ofReal_le_ofReal
      rw [hlinks]
      simpa only [mul_one] using geometric_coefficient_mono (zero_le_one.trans hCs) hCsC
        (by norm_num : (0:ℝ) ≤ 1) n

end WaveTurbulence.RA1Leafwise
