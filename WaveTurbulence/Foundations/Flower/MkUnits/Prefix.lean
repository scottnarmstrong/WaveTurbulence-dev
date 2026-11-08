/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WAssembly
public import WaveTurbulence.Foundations.Flower.MkUnits.NoVine
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WPrefix
public import WaveTurbulence.Foundations.Flower.V5WT.Final

/-! # MK-UNITS: the exports on the prefix

* `vineCaseRepresentsFWMk : WTPrefix VineCaseRepresentsFWMk` (O3′ at a marking), from V5W-T's unconditional
  `v5FrontierClassBound` (the weighted vine class bound) through `vineCaseRepresentsFWMk_of_frontier`;
* `noVineRepresentsFWMk : WTPrefix NoVineRepresentsFWMk` (O4′ at a marking, `NoVine`);
* `representsIntMK_pieceMK`: `RepresentsInt` of a producer piece gives `RepresentsIntMK` of `pieceMK` (no pins, no
  filters, indicator `1`: the spliced kernels agree, FINALMK-DEFS' `splicedKernelMK_toMK`; the loss
  `L^{cP·d·nProt} ≥ 1`);
* **`markedUnitsRepresentsFW : WTPrefix MarkedUnitsRepresentsFW`** (the B3 main export);
* non-vacuity: `vineCaseRepresentsFW_of_Mk`, `noVineRepresentsFW_of_Mk` (at the empty markings the statements imply
  the world's unmarked O3′/O4′).

Adapted from `Flower/Stage1WVine/WPrefix.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs MeasureTheory WaveTurbulence.RedSplice WaveTurbulence.VineA
open scoped ENNReal

/-! ## The prefix of the vine case and of both cases -/

/-- The prefix data shared by the vine case and the combined export. -/
theorem markedUnits_prefix_data (hV : V5FrontierClassBound) :
    WTPrefix (fun P => ((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundAt P) := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  have hthree : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hgates IncTop.topIncoherentDecayGateR hm1 Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  exact prefix_and hthree hV (hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone)
    v5FrontierClassBoundAt_mono

/-- **Both cases at one record**: with the large constant `C ≥ max(CvineFW, CminFW)`, the vine case and the vine-free
case at a marking hold at `{Pg with C₁ := C}`. -/
theorem markedUnits_at_gate (Pg : WTParams) (C : ℝ) (E : GateEnv Pg) (htop0 : TopIncoherentDecayAtR Pg)
    (hη : 0 < Pg.η) (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂)
    (hCv : CvineFW Pg.d Pg.η Pg.C₁ ≤ C) (hCm : Stage1WNoVine.CminFW Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : V5FrontierClassBoundAt (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C)) :
    VineCaseRepresentsFWMk (PB Pg C) ∧ NoVineRepresentsFWMk (PB Pg C) := by
  have hC1 : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCv
  refine ⟨vineCaseRepresentsFWMk_of_gate Pg C E htop0 hη hδ hL2 hC2 Vine.Param.vineparam hCv hV htop, ?_⟩
  exact noVineRepresentsFWMk_of_atNWMk (PB Pg C) hC1 E.hL1 (noVineRepresentsAtNWMk_of_gate Pg E htop0 C hCm)

/-- The combined statement on the prefix, from the staged `V5FrontierClassBound` (conditional helper). -/
theorem markedUnits_pieces_of_frontier (hV : V5FrontierClassBound) :
    WTPrefix (fun P => 1 ≤ P.L ∧ VineCaseRepresentsFWMk P ∧ NoVineRepresentsFWMk P) := by
  have hall := markedUnits_prefix_data hV
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  set Cc : ℝ := max C₁g (max (CvineFW d η C₁g) (Stage1WNoVine.CminFW d η C₁g)) with hCc
  refine ⟨Cc, hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨⟨hincP, hcohP⟩, htopP⟩, hVP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have hL2 : 2 ≤ L := hL₀.trans hL
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have hV' : V5FrontierClassBoundAt (PB Pg Cc) :=
    v5FrontierClassBoundAt_mono Pg Cc C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg Cc) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg Cc C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl htopP
  have h := markedUnits_at_gate Pg Cc E htopP hηm.1 hδ.1 hL2 hC₂
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _)) hV' htop'
  exact ⟨show (1 : ℝ) ≤ L by linarith, h.1, h.2⟩

/-- **O3′ at a marking on the prefix** (unconditional: V5W-T's `v5FrontierClassBound`). -/
theorem vineCaseRepresentsFWMk : WTPrefix VineCaseRepresentsFWMk :=
  prefix_map (fun _ h => h.2.1) (markedUnits_pieces_of_frontier V5WT.v5FrontierClassBound)

/-! ## The `RepresentsIntMK` form -/

/-- `RepresentsInt` of a producer piece is `RepresentsIntMK` of `pieceMK` (no pins, no filters, indicator `1`), for
every survivor datum, every `nProt` and every `cP ≥ 0`. -/
theorem representsIntMK_pieceMK {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (surv : SurvivorData π.Gsb) (nProt : ℕ)
    {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (hcP : 0 ≤ cP) (hL : 1 ≤ P.L) (h : π.RepresentsInt n tt base roots s val) :
    (pieceMK π surv nProt).RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  have hk : ∀ ξ, splicedKernelMK (pieceMK π surv nProt).Gsb
      ((pieceMK π surv nProt).dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)) P.L P.γ P.η P.δ base roots =
      splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)) P.L P.γ P.η P.δ base roots := fun ξ =>
    FinalMKDefs.splicedKernelMK_toMK (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)) P.L P.γ P.η P.δ base roots
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, ?_, ?_, hwint, ?_, hD⟩
  · simp only [hk]; exact hint
  · simp only [hk]; exact hv
  · show ∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (nProt : ℝ)) * s
    have h1 : 1 ≤ P.L ^ (cP * P.d * (nProt : ℝ)) := Real.one_le_rpow hL (by positivity)
    have h0 : 0 ≤ ∫ ξ, ‖w ξ‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    have hAs := h0.trans hwb
    calc ∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
          P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s := hwb
      _ ≤ ((P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
          P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s) *
            P.L ^ (cP * P.d * (nProt : ℝ)) := le_mul_of_one_le_right hAs h1
      _ = _ := by ring

/-- Both cases give the `RepresentsIntMK` form at one record. -/
theorem markedUnitsRepresentsFW_of_pieces (P : WTParams) (hL : 1 ≤ P.L) (hv : VineCaseRepresentsFWMk P)
    (hnv : NoVineRepresentsFWMk P) : MarkedUnitsRepresentsFW P := by
  intro p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π
    surv nProt cP hcP
  refine representsIntMK_pieceMK _ surv nProt hcP hL ?_
  by_cases hu : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) = []
  · exact hnv p hp R hR hRmax N hN1 hN A hA mkF mkC hok tt htt base roots g cψ hcψ hg U s hs0 hb hsize π hu
  · exact hv p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb
      hsize π hu

/-- **The B3 main export on the prefix**: the marked producer for the unmarked units, in `RepresentsIntMK` form. -/
theorem markedUnitsRepresentsFW : WTPrefix MarkedUnitsRepresentsFW :=
  prefix_map (fun P h => markedUnitsRepresentsFW_of_pieces P h.1 h.2.1 h.2.2)
    (markedUnits_pieces_of_frontier V5WT.v5FrontierClassBound)

/-! ## Non-vacuity: the empty markings -/

/-- At the empty markings, O3′ at a marking implies the world's unmarked O3′. -/
theorem vineCaseRepresentsFW_of_Mk (P : WTParams) (h : VineCaseRepresentsFWMk P) : VineCaseRepresentsFW P := by
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have he : mkAt (fun _ => ∅) (repPt π) = ∅ := Set.empty_inter _
  have hv' : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt (fun _ => ∅) (repPt π)) ≠ [] := by
    rw [he]; exact hv
  have h1 := h p hp R hR hRmax N hN1 hN A (fun LG hLG => Stage1Mk.stage1CarriesW_of_stage1Carries (hA LG hLG))
    (fun _ => True) (twistClosedAdm_of_twistClosed hcl _) (fun _ => ∅) (fun _ => ∅) markingOK_empty
    (fun _ _ => trivial) tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv'
  rw [he] at h1
  exact h1

/-- At the empty markings, O4′ at a marking implies the world's unmarked O4′. -/
theorem noVineRepresentsFW_of_Mk (P : WTParams) (h : NoVineRepresentsFWMk P) : NoVineRepresentsFW P := by
  intro p hp R hR hRmax N hN1 hN A hA _ tt htt base roots g cψ hcψ hg _ U s hs0 hb hsize π hv
  have he : mkAt (fun _ => ∅) (repPt π) = ∅ := Set.empty_inter _
  have hv' : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt (fun _ => ∅) (repPt π)) = [] := by
    rw [he]; exact hv
  have h1 := h p hp R hR hRmax N hN1 hN A (fun LG hLG => Stage1Mk.stage1CarriesW_of_stage1Carries (hA LG hLG))
    (fun _ => ∅) (fun _ => ∅) markingOK_empty tt htt base roots g cψ hcψ hg U s hs0 hb hsize π hv'
  rw [he] at h1
  exact h1

end WaveTurbulence.Flower.MkUnits
