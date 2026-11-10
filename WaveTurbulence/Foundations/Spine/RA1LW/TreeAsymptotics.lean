/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeRemainderRestriction
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeNstarBound
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeTimeFactor
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs

/-! # DH23 Proposition 6.1 for trees with individually modified leaf inputs (RA1-LEAFWISE)

Leafwise form of `WaveTurbulence.RegAsymp.ra1Tree` (RA1Tree): the common profile `F` is replaced by a family
`H : LeafProfiles 1 d` with `𝔖^{40d,40d}` norm at most `B` at every address, the kernel `KTstar` by
`LGSpine.treeLeaves` and the leading term by `LGSpine.LeafApp.tree` / `LGSpine.LeafApp.chainNstar`. -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef Set

/-- **RA1-LEAFWISE, trees.** DH23 Prop 6.1 (tree part, layer 0) with a separate profile at every leaf. -/
theorem ra1_tree_leafwise :
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ B : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₁ → ∀ A : ℝ, ∃ L₀ : ℝ,
  ∀ L : ℝ, L₀ ≤ L → ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
    (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
      (∀ a, LG.layer a = 0) → ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal B) →
      Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => LGSpine.treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1 -
          LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (C * (C * δ) ^ n * L ^ (-(gam1L d γ - Real.sqrt η)))) ∧
    (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
      XNorm00Restr (V := Unit) (1 - η) (timeBoxGt 0 0) Set.univ
          (fun ts _ => (X.JBtree 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n) ∧
        ∀ H : LGSpine.LeafProfiles 1 d, (∀ z, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal B) →
        ∀ Z ∈ specialSets (X.treeLinks ζ),
          SNormR (30 * d) 0 (LGSpine.LeafApp.chainNstar H Z X ζ (0, [])) ≤
            ENNReal.ofReal (C * C ^ n)) := by
  intro d hd γ hγ
  obtain ⟨η₀,hη₀,hsmall⟩ := exists_couple_eta_range hd hγ
  refine ⟨η₀,hη₀,?_⟩
  intro η hη B
  obtain ⟨hηsmall,hηγ,hηγ',hηsqrt⟩ := hsmall η hη
  let Binput := max B 0
  have hBinput : 0 ≤ Binput := le_max_right _ _
  obtain ⟨Cr,hCr,hr⟩ := exists_tree_remainder_restriction_bound hd hγ hη.1 hηsmall hηγ hηγ' hBinput hηsqrt
  obtain ⟨Ct,hCt,ht⟩ := exists_tree_JB_time_bound hη.1 (by linarith)
  obtain ⟨Cs,hCs,hs⟩ := literal_Nstar_spatial_bound hd hBinput
  let Cd := max Ct Cs
  have hCd : 1 ≤ Cd := hCt.trans (le_max_left _ _)
  let C := max Cr Cd
  have hC : 1 ≤ C := hCr.trans (le_max_left _ _)
  refine ⟨C,hC,1/2,by norm_num,?_⟩
  intro δ hδ A
  obtain ⟨L₁,hL₁⟩ := hr δ hδ A
  refine ⟨max L₁ 2,?_⟩
  intro L hL n hnlog
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₁ 2).trans hL]
  have hgeom (a : ℝ) (ha : 1 ≤ a) (haC : a ≤ C) : a*a^n ≤ C*C^n :=
    mul_le_mul haC (pow_le_pow_left₀ (zero_le_one.trans ha) haC n)
      (pow_nonneg (zero_le_one.trans ha) _) (zero_le_one.trans hC)
  have hFin (H : LGSpine.LeafProfiles 1 d)
      (hH : ∀ z, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal B) :
      ∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal Binput := by
    intro z
    have := hH z
    rw [NormBridgeScratch.SNormR_eq_spatialNorm] at this
    exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left B 0))
  refine ⟨?_,?_⟩
  · intro X hwf hsize LG hX h0 H hH
    apply (hL₁ L ((le_max_left _ _).trans hL) H (hFin H hH) n hnlog X hwf hsize LG hX h0).trans
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
    refine ⟨?_,?_⟩
    · exact (ht X n hsize (timeBoxGt 0 0)
        (fun t ht i => by fin_cases i; exact (hbox t ht).1.1; exact (hbox t ht).1.2)
        (fun t ht => (hbox t ht).2.le)).trans
        (ENNReal.ofReal_le_ofReal (hgeom Ct hCt ((le_max_left Ct Cs).trans (le_max_right Cr Cd))))
    · intro H hH Z hZ
      rw [NormBridgeScratch.SNormR_eq_spatialNorm]
      have hSpecial : IsSpecialSet (X.treeLinks ζ) Z := (Finset.mem_filter.mp hZ).2
      exact (hs X hwf hdom n hsize ζ H (hFin H hH) Z hSpecial).trans
        (ENNReal.ofReal_le_ofReal ((hgeom Cs hCs ((le_max_right Ct Cs).trans (le_max_right Cr Cd)))))

end WaveTurbulence.RA1Leafwise
