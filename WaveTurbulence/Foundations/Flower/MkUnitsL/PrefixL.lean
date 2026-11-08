/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.AssemblyL
public import WaveTurbulence.Foundations.Flower.MkUnits.Prefix
public import WaveTurbulence.Foundations.Flower.V5W2L.Final

/-! # MK-UNITS-L (B3-2): the exports on the prefix

* `v5FrontierClassBoundAtL_mono`: V5W-2L's `V5FrontierClassBoundAtL` is monotone in the large constants (Stage1WVine's
  `v5FrontierClassBoundAt_mono`, verbatim).
* `vineCaseRepresentsFWMkL (hV : V5W2L.V5FrontierClassBoundL) : WTPrefix VineCaseRepresentsFWMkL`.
* `noVine_valueL`: in the vine-free case the unit top filters present `E = 1` on the run class, so the class sum with
  the extra weight is B3's.
* **`markedUnitsRepresentsFWL (hV : V5W2L.V5FrontierClassBoundL) : WTPrefix MarkedUnitsRepresentsFWL`** (the B3-2 main
  export, the V5W-2L bound as isolated hypothesis), and the unconditional `markedUnitsRepresentsFWL'`,
  `vineCaseRepresentsFWMkL'` through V5W-2L's `v5FrontierClassBoundL`.
* The `S = none` exports of B3 are the instances `SU = fun _ => []`, `E = 1`: `vineCaseRepresentsFWMk_of_L`,
  `markedUnitsRepresentsFW_of_L`.

Adapted from `Flower/MkUnits/Prefix.lean` and `Flower/Stage1WVine/WPrefix.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs MeasureTheory WaveTurbulence.RedSplice WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Flower.MkUnits WaveTurbulence.VineC
  WaveTurbulence.VineAlign WaveTurbulence.LFTwist
open WaveTurbulence.Flower.V5W2L (topFilterWeightL V5FrontierClassBoundAtL V5FrontierClassBoundL)
open WaveTurbulence.VineSpaceK (nodeWeight)
open scoped ENNReal

/-- **The bound with a product of top filters is monotone in the large constants** (Stage1WVine's
`v5FrontierClassBoundAt_mono`, verbatim: only the factor `(C₁ √δ)^{n₂}` depends on them). -/
theorem v5FrontierClassBoundAtL_mono : LargeConstantMonotone V5FrontierClassBoundAtL := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ
    hc hgp hre S hS hrow
  have hN := vineEstHalfMK_N P c₁ c₂ (p + 1)
  have key := @h p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay
    (by rw [← hN]; exact hord) (by have := vineEstHalfMK_N P c₁ c₂ 1; rw [← this]; exact hcl) centre wBar lam g cψ
    hc hgp hre S hS hrow
  refine le_trans key (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hL0 : 0 ≤ P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) :=
    Real.rpow_nonneg (by linarith) _
  have hleaf := WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀
  have hs : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hc0 : 0 ≤ P.C₁ * Real.sqrt P.δ := mul_nonneg (by linarith) hs
  have hcc : P.C₁ * Real.sqrt P.δ ≤ c₁ * Real.sqrt P.δ := mul_le_mul_of_nonneg_right h₁ hs
  have hpow := pow_le_pow_left₀ hc0 hcc (clLocalOrder2 RD hG R)
  have h1 : 0 ≤ (1 + |lam|) ^ (6 * P.η ^ 6) := Real.rpow_nonneg (by positivity) _
  show (1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _) ≤
    (1 + |lam|) ^ (6 * P.η ^ 6) * ((c₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _)
  gcongr

/-! ## The prefix of the vine case and of both cases -/

/-- The prefix data shared by the vine case and the combined export (B3's `markedUnits_prefix_data` with V5W-2L's
bound). -/
theorem markedUnits_prefix_dataL (hV : V5FrontierClassBoundL) :
    WTPrefix (fun P => ((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundAtL P) := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  have hthree : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hgates IncTop.topIncoherentDecayGateR hm1 Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  exact prefix_and hthree hV (hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone)
    v5FrontierClassBoundAtL_mono

/-- **Both cases at one record** (B3's `markedUnits_at_gate` with per-unit top filters in the vine case). -/
theorem markedUnits_at_gateL (Pg : WTParams) (C : ℝ) (E : GateEnv Pg) (htop0 : TopIncoherentDecayAtR Pg)
    (hη : 0 < Pg.η) (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂)
    (hCv : CvineFWL Pg.d Pg.η Pg.C₁ ≤ C) (hCm : Stage1WNoVine.CminFW Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : V5FrontierClassBoundAtL (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C)) :
    VineCaseRepresentsFWMkL (PB Pg C) ∧ NoVineRepresentsFWMk (PB Pg C) := by
  have hC1 : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCv
  refine ⟨vineCaseRepresentsFWMkL_of_gate Pg C E htop0 hη hδ hL2 hC2 Vine.Param.vineparam hCv hV htop, ?_⟩
  exact noVineRepresentsFWMk_of_atNWMk (PB Pg C) hC1 E.hL1 (noVineRepresentsAtNWMk_of_gate Pg E htop0 C hCm)

/-- The combined statement on the prefix, from V5W-2L's bound (B3's `markedUnits_pieces_of_frontier`). -/
theorem markedUnits_pieces_of_frontierL (hV : V5FrontierClassBoundL) :
    WTPrefix (fun P => 1 ≤ P.L ∧ VineCaseRepresentsFWMkL P ∧ NoVineRepresentsFWMk P) := by
  have hall := markedUnits_prefix_dataL hV
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
  set Cc : ℝ := max C₁g (max (CvineFWL d η C₁g) (Stage1WNoVine.CminFW d η C₁g)) with hCc
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
  have hV' : V5FrontierClassBoundAtL (PB Pg Cc) :=
    v5FrontierClassBoundAtL_mono Pg Cc C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg Cc) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg Cc C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl htopP
  have h := markedUnits_at_gateL Pg Cc E htopP hηm.1 hδ.1 hL2 hC₂
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _)) hV' htop'
  exact ⟨show (1 : ℝ) ≤ L by linarith, h.1, h.2⟩

/-- **O3′ at a marking with per-unit top filters, on the prefix** (V5W-2L's bound as isolated hypothesis). -/
theorem vineCaseRepresentsFWMkL (hV : V5FrontierClassBoundL) : WTPrefix VineCaseRepresentsFWMkL :=
  prefix_map (fun _ h => h.2.1) (markedUnits_pieces_of_frontierL hV)

/-! ## The vine-free case -/

/-- **In the vine-free case the extra weight is invisible**: the unit top filters present `E = 1` on the run class
(an empty product), so the class sum with the weight `fwWeight · E` is the class sum with `fwWeight`. -/
theorem noVine_valueL (P : WTParams) {p R N : ℕ} {A : Finset (LayeredGarden (2 * R))}
    (hA : ∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG)
    {Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop} (hcl : TwistClosedAdm p A Adm)
    {mkF mkC : Stage1Mk.MarkFn (2 * R)} (hok : MarkingOK mkF mkC)
    (hadm : ∀ a : PrescribedPrimeGarden (2 * R), a.layered ∈ A → Adm (startAt a (mkAt mkF a)))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (g : Fin (2 * R) → Mom P.d → ℂ)
    (U : TypeFamily P (2 * R)) (π : PcA R p (objKind (2 * R)) A mkF)
    (hu : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) = [])
    (SU : Fin (unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π))).length → List ℝ)
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (hTF : UnitTopFilters P.L p (repPt π) (mkAt mkF (repPt π)) SU base roots E) :
    ∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fun κ => fwWeight p g base LG κ * E LG κ) =
      ∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fwWeight p g base LG) := by
  obtain ⟨a, ha⟩ : ∃ a, repPt π = a := ⟨_, rfl⟩
  have haA : a.layered ∈ A := ha ▸ repPt_layered_memMk π
  have hcan : IsCanonGC (p + 1) a.layered := (hA a.layered haA).1
  obtain ⟨T, hT⟩ := exists_outputs_finsetMk (p := p) a mkF
  obtain ⟨mkU, hset, hout⟩ : ∃ mkU : Stage1Mk.MarkFn (2 * R), mkU a.prime = mkAt mkF a ∧
      a.outputs (p := p) (kind := objKind (2 * R)) mkU = a.outputs (p := p) (kind := objKind (2 * R)) mkF :=
    ⟨fixMark a (mkAt mkF a), fixMark_self a (mkAt mkF a), outputs_fixMark_mkAt mkF a⟩
  have hadmA : Adm (sourceStart a mkU) := by
    show Adm (startAt a (mkU a.prime))
    rw [hset]
    exact hadm a haA
  obtain ⟨SU', hTF', -⟩ : ∃ SU' : Fin (unitBlocks a.prime.skeleton a.totalSigma (mkU a.prime)).length → List ℝ,
      UnitTopFilters P.L p a (mkU a.prime) SU' base roots E ∧ True := by
    obtain ⟨SUa, hTFa⟩ : ∃ SUa : Fin (unitBlocks a.prime.skeleton a.totalSigma (mkAt mkF a)).length → List ℝ,
        UnitTopFilters P.L p a (mkAt mkF a) SUa base roots E := by
      subst ha
      exact ⟨SU, hTF⟩
    obtain ⟨SU', h', -⟩ := unitTopFilters_transport hset.symm SUa hTFa
    exact ⟨SU', h', trivial⟩
  have hu' : unitBlocks a.prime.skeleton a.totalSigma (mkU a.prime) = [] := by
    rw [hset]
    subst ha
    exact hu
  have hE1 : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mkU)),
      y ∈ sourceClass a p (objKind (2 * R)) mkU →
      ∀ κ : GenDecoration y.1.layered.garden P.d roots 0, E y.1.layered κ = 1 := by
    intro y hy
    have h2 : ∀ κ : GenDecoration (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)).garden P.d roots 0, E _ κ = 1 := fun κ => by
      rw [hTF'.2 y hy κ]
      refine Finset.prod_eq_one fun j _ => ?_
      have hj := j.2
      simp [hu'] at hj
    rw [stateLayer_spec y.1] at h2
    exact h2
  have hcanR : IsCanonGC (p + 1) (repPt π).layered := by rw [ha]; exact hcan
  have hTR : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF := by
    rw [ha]; exact hT
  have houtR : (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF := by rw [ha]; exact hout
  have hadmR : Adm (sourceStart (repPt π) mkU) := by rw [ha]; exact hadmA
  rw [sum_members_eqWMk hcl hok.fine hok.sub π houtR hadmR hcanR P U.toLF tt base roots
      (fun LG κ => fwWeight p g base LG κ * E LG κ) T hTR,
    sum_members_eqWMk hcl hok.fine hok.sub π houtR hadmR hcanR P U.toLF tt base roots (fwWeight p g base) T hTR]
  have hT' := sourceClass_hTMk (p := p) (kind := objKind (2 * R)) a mkU T (hT.trans hout.symm)
  rw [sum_layered_eq_sum_classU (Us := unitsSplit (sourceAssemblyMk a mkU)) (A := sourceStart a mkU) a.prime.prime
      (sourceUnitsMk a mkU) T hT',
    sum_layered_eq_sum_classU (Us := unitsSplit (sourceAssemblyMk a mkU)) (A := sourceStart a mkU) a.prime.prime
      (sourceUnitsMk a mkU) T hT']
  refine Finset.sum_congr rfl fun y hy => ?_
  congr 1
  funext κ
  show fwWeight p g base y.1.layered κ * E y.1.layered κ = fwWeight p g base y.1.layered κ
  rw [hE1 y hy κ, mul_one]

/-! ## The main export -/

/-- Both cases give the `RepresentsIntMK` form with per-unit top filters at one record. -/
theorem markedUnitsRepresentsFWL_of_pieces (P : WTParams) (hL : 1 ≤ P.L) (hv : VineCaseRepresentsFWMkL P)
    (hnv : NoVineRepresentsFWMk P) : MarkedUnitsRepresentsFWL P := by
  intro p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π
    SU E hTF surv nProt cP hcP
  refine representsIntMK_pieceMK _ surv nProt hcP hL ?_
  by_cases hu : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) = []
  · have h0 : ∑ j, (SU j).length = 0 := Finset.sum_eq_zero fun j _ => by
      have hj := j.2
      simp [hu] at hj
    rw [h0, pow_zero, mul_one, noVine_valueL P hA hcl hok hadm tt base roots g U π hu SU E hTF]
    exact hnv p hp R hR hRmax N hN1 hN A hA mkF mkC hok tt htt base roots g cψ hcψ hg U s hs0 hb hsize π hu
  · exact hv p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb
      hsize π hu SU E hTF

/-- **The B3-2 main export on the prefix**: the marked producer for the unmarked units with per-unit top filters, in
`RepresentsIntMK` form (V5W-2L's bound as isolated hypothesis). -/
theorem markedUnitsRepresentsFWL (hV : V5FrontierClassBoundL) : WTPrefix MarkedUnitsRepresentsFWL :=
  prefix_map (fun P h => markedUnitsRepresentsFWL_of_pieces P h.1 h.2.1 h.2.2) (markedUnits_pieces_of_frontierL hV)

/-- The B3-2 main export, unconditional (V5W-2L's `v5FrontierClassBoundL`). -/
theorem markedUnitsRepresentsFWL' : WTPrefix MarkedUnitsRepresentsFWL :=
  markedUnitsRepresentsFWL V5W2L.v5FrontierClassBoundL

/-- O3′ at a marking with per-unit top filters, unconditional (V5W-2L's `v5FrontierClassBoundL`). -/
theorem vineCaseRepresentsFWMkL' : WTPrefix VineCaseRepresentsFWMkL :=
  vineCaseRepresentsFWMkL V5W2L.v5FrontierClassBoundL

/-! ## The `S = none` exports are the instances without filters -/

/-- The trivial filter data: no filter at any unit and `E = 1`. -/
theorem unitTopFilters_nil {d R : ℕ} (L : ℝ) (p : ℕ) (a : PrescribedPrimeGarden (2 * R))
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) :
    UnitTopFilters L p a Mk (fun _ => []) base roots (fun _ _ => 1) := by
  refine ⟨fun j s hs => by simp at hs, fun y _ κ => ?_⟩
  symm
  refine Finset.prod_eq_one fun j _ => ?_
  simp [nodeWeight, topFilterWeightL]

/-- At `SU = fun _ => []`, `E = 1`, the vine case with per-unit top filters is B3's (S = none). -/
theorem vineCaseRepresentsFWMk_of_L (P : WTParams) (h : VineCaseRepresentsFWMkL P) : VineCaseRepresentsFWMk P := by
  intro p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π hv
  have h1 := h p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb
    hsize π hv (fun _ => []) (fun _ _ => 1) (unitTopFilters_nil P.L p _ _ base roots)
  simp only [List.length_nil, Finset.sum_const_zero, pow_zero, mul_one] at h1
  exact h1

/-- At `SU = fun _ => []`, `E = 1`, the main export with per-unit top filters is B3's main export (S = none). -/
theorem markedUnitsRepresentsFW_of_L (P : WTParams) (h : MarkedUnitsRepresentsFWL P) : MarkedUnitsRepresentsFW P := by
  intro p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb hsize π
    surv nProt cP hcP
  have h1 := h p hp R hR hRmax N hN1 hN A hA Adm hcl mkF mkC hok hadm tt htt base roots g cψ hcψ hg hre U s hs0 hb
    hsize π (fun _ => []) (fun _ _ => 1) (unitTopFilters_nil P.L p _ _ base roots) surv nProt cP hcP
  simp only [List.length_nil, Finset.sum_const_zero, pow_zero, mul_one] at h1
  exact h1

end WaveTurbulence.Flower.MkUnitsL
