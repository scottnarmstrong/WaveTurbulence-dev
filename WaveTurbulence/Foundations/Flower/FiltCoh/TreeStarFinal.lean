/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeStarBound

/-! # FILT-COH (c2): star-weighted layer-zero paired trees, the final bound

`exists_tree_star_bound_theta`: layer-zero regular paired trees, separately normalized leaf profiles, any star
weights presented with `30d`-th total-frequency moments `cω`, order `n > 0`, every `θ ≤ 1 - η/8`:
`‖K‖_{X^{θ,30d,0}(timeBoxGt 0 0)} ≤ Ck (Ck δ)^n ∏ cω`. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst Set MainCoef
open WaveTurbulence.Flower.IncTop (PairedMomentum pairedLattice RootMeasure rootChar rootJetConstant)
open scoped ENNReal

variable {d : ℕ}

/-- The weighted mass of a sum envelope. -/
theorem lintegral_wL_ofReal_sum {I : Type*} [Fintype I] (θ x : ℝ) (hx : 0 ≤ x) (E : I → (ℝ × ℝ) → ℝ)
    (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam) :
    (∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ i, x * E i lam)) =
      ∑ i, ENNReal.ofReal x * ∫⁻ lam, wL θ lam * ENNReal.ofReal (E i lam) := by
  have hsum (lam : ℝ × ℝ) : ENNReal.ofReal (∑ i, x * E i lam) =
      ∑ i, ENNReal.ofReal x * ENNReal.ofReal (E i lam) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hx (hpE i lam))]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul hx
  simp_rw [hsum, Finset.mul_sum]
  rw [lintegral_finsetSum (f := fun i lam => wL θ lam * (ENNReal.ofReal x * ENNReal.ofReal (E i lam)))
    Finset.univ (fun i _ => (measurable_wL θ).mul (measurable_const.mul (ENNReal.measurable_ofReal.comp (hmE i))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_left_comm (wL θ _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Star-weighted layer-zero paired trees in `X^{θ,30d,0}`.** -/
theorem exists_tree_star_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ X : RegChain, X.wf = true → X.size = 2*n →
      ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden → (∀ a, LG.layer a = 0) →
      ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput) →
      ∀ (Sset : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ Sset, IncTop.StarPresented (30*d) (ω a) (cω a)) →
      Fourier.mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts.val 0) (ts.val 1) k.val
          (fun _ => 0) 0 (IncTop.starWeight Sset ω)) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
  classical
  let Cbase := max 1 |CTη η|
  have hCbase : 1 ≤ Cbase := le_max_left _ _
  obtain ⟨Kr,Cw,hKr,hCw,henv⟩ := physical_symbol_envelope_u hd hγ hη0 hη hηγ hθ0 hθ
    (Agev := ClassJR.A1) A1_nonneg hCbase
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  let a := rootLocalOverlapConstant d
  let b := treeRootLeafDerivativeConstant d (30*d)
  let p := leafMomentLocalizationConstant d (30*d+1) (40*d)*treeAugmentedInputBound d (40*d) (40*d) Binput
  let Hc := ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff
  have ha : 0 ≤ a := (rootLocalOverlapConstant_pos d).le
  have hb : 0 ≤ b := treeRootLeafDerivativeConstant_nonneg d (30*d)
  have hp : 0 ≤ p := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg _))
    · exact (treeAugmentedInputBound_pos d (40*d) (40*d) Binput).le
  have hH : Hc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top _)
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.tree_error_budget_absorption ha hb hCcover.le hp
    (by norm_num : (0:ℝ) ≤ 2) hKr.le (zero_le_one.trans hCw) Hc hH
  have hR0 : 0 < rootJetConstant (30*d) := IncTop.rootJetConstant_pos _
  set Cf := Ck * max 1 (rootJetConstant (30*d)) with hCf
  have hCf1 : 1 ≤ Cf := one_le_mul_of_one_le_of_one_le hCk (le_max_left _ _)
  refine ⟨Cf, hCf1, fun Aorder => ?_⟩
  obtain ⟨L₁,henv⟩ := henv Aorder
  refine ⟨max L₁ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog X hwf hsize LG hX h0 H hF Sset ω cω hpres
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₁ 2).trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδp : 0 < δ := by have := (Real.rpow_pos_of_pos hLp (-(η/2))).trans_le hδ; linarith
  set m := (X.treeLinks (LG.garden.sig 0)).length with hmdef
  have hlen : m = n := by
    have hh := chain_linksAt_length X (LG.garden.sig 0) ((0:Fin 1),[])
    change (X.treeLinks (LG.garden.sig 0)).length*2=X.size at hh
    omega
  have hmpos : 0 < m := by omega
  have hmlog : (m:ℝ) ≤ Real.log L^Aorder := by rw [hlen]; exact hnlog
  obtain ⟨C,hC,_hlead,hphase⟩ := RA1Leafwise.actual_tree_physical_phase_profiles_classified hη0
    (by linarith : η ≤ 2) (le_refl ClassJR.A1) X hwf (LG.garden.sig 0)
  choose S hS hcov using hcover LG.garden X hX
  let I := (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset
  let J := fun Z : I => treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val
  let cZ := fun Z : I => (∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)
  have hcZ (Z : I) : ‖LG.garden.zeta * cZ Z‖ ≤ 1 := by
    rw [norm_mul, tree_garden_zeta_norm, one_mul]
    exact tree_coefficient_weight_norm_le Z.val
  have hexp : 2*X.size+1=4*m+1 := by omega
  have hCs (Z : I) : SRep (1-η/8) (η/4) (1-η/2) ClassJR.A1 (Cbase^(4*m+1)) (C Z) := by
    apply tree_SRep_mono_mass (hC Z) A1_nonneg
    rw [hexp]
    exact tree_literal_coefficient_mass_le (CTη η) _
  have hE (Z : I) := henv L ((le_max_left _ _).trans hL) δ hδ hδ1 m hmpos hmlog (J Z) (C Z) (hCs Z)
  choose E hmE hpE hbE hgE using hE
  set P0 : ℝ := 2*(Kr*δ)^m with hP0
  have hP0n : 0 ≤ P0 := by positivity
  have hmE' (Z : I) : Measurable (fun lam => P0 * E Z lam) := measurable_const.mul (hmE Z)
  have hpE' (Z : I) (lam : ℝ × ℝ) : 0 ≤ P0 * E Z lam := mul_nonneg hP0n (hpE Z lam)
  have hwE (Z : I) : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) ≤
      ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m := by
    have he : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) =
        ENNReal.ofReal P0 * ∫⁻ lam, wL θ lam * ENNReal.ofReal (E Z lam) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun lam => ?_
      rw [ENNReal.ofReal_mul hP0n]
      ring
    rw [he]
    exact mul_le_mul' le_rfl (hbE Z)
  have hfE' (Z : I) : (∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam)) < ⊤ :=
    (hwE Z).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
  have hEnv' (Z : I) : ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin m × Fin 2) → Fin d → ℤ) (β γ' : Fin m → Mom d),
      ‖physicalWeightedCellSymbol L δ γ z β γ' (J Z) (C Z) lam‖ ≤ P0 * E Z lam := by
    filter_upwards [hgE Z] with lam hlam z β γ'
    exact hlam z β γ'
  have hH' : ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      RA1Leafwise.treeOriginalArrayCoefficient (d := d) L γ δ LG hX t s = fun g =>
      RA1Leafwise.treeWickArrayWeight g * ∑ Z : I, cZ Z * ∫ lam, resProfile (J Z) (fun Ω => C Z (ofLp Ω) lam)
        (fun j => (2*δ*L^(2*γ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s := by
    intro t s hs hst ht
    funext g
    unfold RA1Leafwise.treeOriginalArrayCoefficient RA1Leafwise.treeOriginalLatticeCoefficient
      RA1Leafwise.treeWickArrayWeight
    rw [hphase d L γ δ LG rfl h0 hX t s hs hst ht 0 (fun p => if p.2=0 then g.1 p.1 else g.2 p.1)]
    simp only [ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false, Complex.ofReal_prod]
    rfl
  have hf : ∀ b, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.treeInputFunctionsL LG H b) ≤
      ENNReal.ofReal Binput := fun _ => hF _
  set Gm := IncTop.starRootMeasure (30*d) Sset ω cω hpres (IncTop.treeRow hX) with hGm
  have hmom : Gm.momentMass (30*d) ≤ ∏ a ∈ Sset, ENNReal.ofReal (cω a) :=
    IncTop.starRootMeasure_momentMass_le (30*d) Sset ω cω hpres (IncTop.treeRow hX)
  have hfin : Gm.momentMass (30*d) < ⊤ :=
    hmom.trans_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))
  -- the extension
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Set.Icc (0:ℝ) 1) ∧ (t.val 1∈Set.Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  let Ext : (Fin 2 → ℝ) → Mom d → ℂ := fun t k =>
    ∫ u, (Gm.at k).amplitude u.2 *
      rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFunctionsL LG H) S) k u.1 *
      (unitSquareCutoff t * pairedInverseProfile (fun lam => treeStarProfile hX L δ γ Gm.base.frequency
        (fun Z => LG.garden.zeta * cZ Z) J C S lam u) t) ∂(treeLeafCellMeasure S).prod Gm.base.μ
  refine (Fourier.mixedRestrictionNorm_le_extension Ext (fun t k => (tree_star_kernel_eq_ext hX hwf h0 hd hL1 γ δ
    hBi H hf S hcov hS cZ hcZ J C (fun Z => (hC Z).reg) hH' hθ0 (fun Z lam => P0 * E Z lam) hmE' hpE' hfE' hEnv'
    (30*d) Sset ω cω hpres t.val (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val).symm)).trans ?_
  refine (tree_star_ext_norm_le hX hd hL1 γ δ hBi H hf S hS (fun Z => LG.garden.zeta * cZ Z) hcZ J C
    (fun Z => (hC Z).reg.meas) hθ0 (fun Z lam => P0 * E Z lam) hmE' hpE' hfE' hEnv' Gm hfin).trans ?_
  -- arithmetic
  set loss := treeSpectralFrequencyLoss X (LG.garden.sig 0) with hloss
  have hloss1 : 1 ≤ loss := one_le_treeSpectralFrequencyLoss X _
  have hcardI : Fintype.card I = 2^m := tree_coefficient_subset_count X (LG.garden.sig 0)
  have hint : (∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ Z : I, loss * (P0 * E Z lam))) ≤
      (2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m*loss) * (ENNReal.ofReal 1 * (2*ENNReal.ofReal Cw^m))) := by
    rw [lintegral_wL_ofReal_sum θ loss (zero_le_one.trans hloss1) _ hmE' hpE']
    calc (∑ Z : I, ENNReal.ofReal loss * ∫⁻ lam, wL θ lam * ENNReal.ofReal (P0 * E Z lam))
        ≤ ∑ _Z : I, ENNReal.ofReal loss * (ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m) :=
          Finset.sum_le_sum fun Z _ => mul_le_mul' le_rfl (hwE Z)
      _ = (2:ℝ≥0∞)^m * (ENNReal.ofReal loss * (ENNReal.ofReal P0 * ENNReal.ofReal Cw ^ m)) := by
          rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul]
          norm_num
      _ ≤ _ := by
          rw [ENNReal.ofReal_one, one_mul, hP0, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*(Kr*δ)^m)]
          have h2 : (1:ℝ≥0∞) ≤ 2 := by norm_num
          calc (2:ℝ≥0∞)^m * (ENNReal.ofReal loss * (ENNReal.ofReal (2*(Kr*δ)^m) * ENNReal.ofReal Cw ^ m))
              = (2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m) * ENNReal.ofReal loss * (1 * ENNReal.ofReal Cw ^ m)) := by
                ring
            _ ≤ _ := by gcongr
  have hcard : Fintype.card (TPlus LG.garden) + 1 = 2*m+1 := by rw [tree_input_count hX]
  have hb2 := hbudget m δ loss 1 hδp.le (zero_le_one.trans hloss1)
    (RA1Leafwise.treeSpectralFrequencyLoss_le_geometric X (LG.garden.sig 0)) zero_le_one
  rw [hcard]
  calc (ENNReal.ofReal a * (ENNReal.ofReal (rootJetConstant (30*d)) *
        ((ENNReal.ofReal b * (ENNReal.ofReal (Ccover^m) * ENNReal.ofReal p^(2*m+1))) *
          Gm.momentMass (30*d)))) *
        (ENNReal.ofReal (2^θ) * Fourier.timeFourierNorm θ unitSquareCutoff *
          ∫⁻ lam, wL θ lam * ENNReal.ofReal (∑ Z : I, loss * (P0 * E Z lam)))
      ≤ (ENNReal.ofReal a * (ENNReal.ofReal (rootJetConstant (30*d)) *
        ((ENNReal.ofReal b * (ENNReal.ofReal (Ccover^m) * ENNReal.ofReal p^(2*m+1))) *
          ∏ a ∈ Sset, ENNReal.ofReal (cω a)))) *
        (Hc * ((2:ℝ≥0∞)^m * (ENNReal.ofReal (2*(Kr*δ)^m*loss) * (ENNReal.ofReal 1 * (2*ENNReal.ofReal Cw^m))))) := by
        gcongr
    _ = ((ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (Ccover^m)*ENNReal.ofReal p^(2*m+1)))) *
          (Hc*(ENNReal.ofReal (2*(Kr*δ)^m*loss)*((2:ℝ≥0∞)^m*(ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m)))))) *
        (ENNReal.ofReal (rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) := by ring
    _ ≤ ENNReal.ofReal (Ck*(Ck*δ)^m*1) *
        (ENNReal.ofReal (rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a)) :=
        mul_le_mul' hb2 le_rfl
    _ = ENNReal.ofReal (Ck*(Ck*δ)^m*rootJetConstant (30*d)) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
        rw [mul_one, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Cf*(Cf*δ)^n) * ∏ a ∈ Sset, ENNReal.ofReal (cω a) := by
        rw [← hlen]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have hM1 : 1 ≤ max 1 (rootJetConstant (30*d)) := le_max_left _ _
        have hMR : rootJetConstant (30*d) ≤ max 1 (rootJetConstant (30*d)) := le_max_right _ _
        have hCk0 : 0 ≤ Ck := zero_le_one.trans hCk
        have h1 : (Ck*δ)^m ≤ (Cf*δ)^m := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hCf]
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCk0 hM1) hδp.le
        calc Ck*(Ck*δ)^m*rootJetConstant (30*d) ≤ Ck*(Cf*δ)^m*max 1 (rootJetConstant (30*d)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hCk0) hMR hR0.le (by positivity)
          _ = Cf*(Cf*δ)^m := by rw [hCf]; ring

end WaveTurbulence.Flower.FiltCoh
