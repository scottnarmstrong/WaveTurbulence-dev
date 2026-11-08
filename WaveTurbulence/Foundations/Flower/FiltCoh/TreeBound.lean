/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolMass
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeRemainderExtension
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeKernelProfileMixtures
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteScalarEstimate
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeQualitativeInverseProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootScalarIntegrability
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeProfileScalarMass
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeErrorMassBudget

/-! # FILT-COH: layer-zero regular paired trees at an arbitrary time weight (bound only)

Main's exact tree identity `RA1Leafwise.KTstar_classified_leaf_profile_mixtures` writes the kernel as a moving-root
mixture of the normalized tree scalar; with the physical normalization pushed in, the scalar is the physical cell
symbol (`physicalWeightedCellSymbol_eq_tree`). Main's weight-generic tree assembly
`tree_root_finite_scalar_profile_le` and budget `RA1Leafwise.tree_error_budget_absorption` then bound it in
`X^{θ,30d,0}` by the weight-`θ` symbol envelope. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh IncohInst MainCoef
open scoped ENNReal

variable {d : ℕ}

/-- **Layer-zero paired-tree kernels in `X^{θ,30d,0}`, `0 ≤ θ ≤ 1 - η/8`**, for leaf profiles of `𝔖^{40d,40d}` size
at most `Binput`, positive polylogarithmic order. -/
theorem exists_tree_kernel_bound_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8) {Binput : ℝ} (hBi : 0 ≤ Binput) :
    ∃ Ck : ℝ, 1 ≤ Ck ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ X : RegChain, X.wf = true → X.size = 2*n →
      ∀ (LG : LayeredGarden 1), X.DecodesTree LG.garden → (∀ a, LG.layer a = 0) →
      ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (RA1Leafwise.addrFam H z) ≤ ENNReal.ofReal Binput) →
      Fourier.mixedRestrictionNorm θ (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => LGSpine.treeLeaves L γ δ LG H (ts.val 0) (ts.val 1) k.val) ≤
        ENNReal.ofReal (Ck*(Ck*δ)^n) := by
  classical
  let Cbase := max 1 |CTη η|
  have hCbase : 1 ≤ Cbase := le_max_left _ _
  obtain ⟨Kr,Cw,hKr,hCw,henv⟩ := physical_symbol_envelope_theta hd hγ hη0 hη hηγ hηγ' hθ0 hθ
    A1_nonneg hCbase
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  let a := rootLocalOverlapConstant d
  let b := treeRootLeafDerivativeConstant d (30*d)
  let p := leafMomentLocalizationConstant d (30*d+1) (40*d)*treeAugmentedInputBound d (40*d) (40*d) Binput
  let e := 1+2*Real.pi
  let Hc := ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff
  have ha : 0 ≤ a := (rootLocalOverlapConstant_pos d).le
  have hb : 0 ≤ b := treeRootLeafDerivativeConstant_nonneg d (30*d)
  have hp : 0 ≤ p := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg _))
    · exact (treeAugmentedInputBound_pos d (40*d) (40*d) Binput).le
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hH : Hc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top _)
  obtain ⟨Ck,hCk,hbudget⟩ := RA1Leafwise.tree_error_budget_absorption ha hb hCcover.le hp he hKr.le hCw Hc hH
  refine ⟨Ck,hCk,fun Aorder => ?_⟩
  obtain ⟨L₁,henv⟩ := henv Aorder
  refine ⟨max L₁ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog X hwf hsize LG hX h0 H hF
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
  obtain ⟨C,hC,_hlead,hkernel⟩ := RA1Leafwise.KTstar_classified_leaf_profile_mixtures hη0
    (by linarith : η ≤ 2) (le_refl ClassJR.A1) X hwf (LG.garden.sig 0)
  choose S hS hcov using hcover LG.garden X hX
  let I := (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset
  let J := fun Z : I => treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val
  let coef := fun Z : I => LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)
  let Rs : I → (ℝ × ℝ) → (Fin m → Mom d) → (Fin m → Mom d) → ((Fin m × Fin 2) → Fin d → ℤ) → ℂ :=
    fun Z lam β γ' z => physicalWeightedCellSymbol L δ γ z β γ' (J Z) (C Z) lam
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*m):ℝ):ℂ)
  have hcoef (Z : I) : ‖coef Z‖ ≤ 1 := by
    rw [show coef Z=LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹) from rfl,
      norm_mul,tree_garden_zeta_norm,one_mul]
    exact tree_coefficient_weight_norm_le Z.val
  have hexp : 2*X.size+1=4*m+1 := by omega
  have hCs (Z : I) : SRep (1-η/8) (η/4) (1-η/2) ClassJR.A1 (Cbase^(4*m+1)) (C Z) := by
    apply tree_SRep_mono_mass (hC Z) A1_nonneg
    rw [hexp]
    exact tree_literal_coefficient_mass_le (CTη η) _
  -- integrability of every normalized tree scalar (main's qualitative envelope)
  have hR0 (Z : I) := fun z : (Fin m × Fin 2) → Fin d → ℤ =>
    stronglyMeasurable_treeProfileArrayScalar_joint L (2*δ*L^(2*γ))
      RA1Leafwise.treeWickArrayWeight z (J Z) (hC Z).reg.meas
  have hEnv0 (Z : I) := treeProfileArrayScalar_uniform_integrable_envelope (d := d) hL1 (2*δ*L^(2*γ))
    RA1Leafwise.treeWickArrayWeight zero_le_one RA1Leafwise.treeWickArrayWeight_norm_le (J Z) (hC Z).reg
  choose E0 _hmE0 _hpE0 hiE0 hbE0 using hEnv0
  have hQ (Z : I) := tree_normalized_inverseProfile_qualitative hX
      (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ'
        (J Z) (C Z) lam) (hR0 Z) (E0 Z) (hiE0 Z) (hbE0 Z) S
  have hRs (Z : I) (lam : ℝ × ℝ) (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
      treeNormalizedScalar hX (Rs Z) S lam u = q * treeNormalizedScalar hX
        (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ'
          (J Z) (C Z) lam) S lam u := by
    unfold treeNormalizedScalar
    dsimp only [Rs]
    rw [physicalWeightedCellSymbol_eq_tree hLp δ γ, mul_div_assoc]
  have hiLam (Z : I) (u) : Integrable (fun lam => coef Z * treeNormalizedScalar hX (Rs Z) S lam u) := by
    simp_rw [hRs]
    exact (((hQ Z).1 u).const_mul q).const_mul (coef Z)
  have hpIP (Z : I) (t : Fin 2 → ℝ) (u) :
      pairedInverseProfile (fun lam => treeNormalizedScalar hX (Rs Z) S lam u) t =
        q * pairedInverseProfile (fun lam => treeNormalizedScalar hX
          (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ'
            (J Z) (C Z) lam) S lam u) t := by
    simp_rw [hRs]
    exact tree_pairedInverseProfile_const_mul _ _ _
  have hiU (Z : I) (t : Fin 2 → ℝ) (k : Mom d) :
      Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude (RA1Leafwise.treeInputFam LG.garden H) S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (Rs Z) S lam u) t)
        (treeLeafCellMeasure S) := by
    have hh := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar (RA1Leafwise.treeInputFam LG.garden H)
      (K := 40*d) (M := 40*d) (by omega) (by omega) hBi (fun _ => hF _) S hS
      (fun u => pairedInverseProfile (fun lam => treeNormalizedScalar hX
        (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ'
          (J Z) (C Z) lam) S lam u) t) ((hQ Z).2.1 t) ((hQ Z).2.2 t) k
    refine (hh.const_mul q).congr (ae_of_all _ fun u => ?_)
    dsimp only
    rw [hpIP Z t u]
    ring
  -- the kernel as one moving-root mixture of the physical symbols
  let Ext := treeRootLeafMixture (RA1Leafwise.treeInputFam LG.garden H) S
    (fun t u => unitSquareCutoff t*pairedInverseProfile
      (fun lam => ∑ Z : I, coef Z*treeNormalizedScalar hX (Rs Z) S lam u) t)
  have hId (t s : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) (k : Mom d) :
      LGSpine.treeLeaves L γ δ LG H t s k = Ext ![t,s] k := by
    have htvec : ∀ i : Fin 2, (![t,s] : Fin 2 → ℝ) i ∈ Set.Icc (0:ℝ) 1 := by
      intro i
      fin_cases i
      · exact ⟨hs.trans hst.le,ht⟩
      · exact ⟨hs,hst.le.trans ht⟩
    have hker := hkernel d (40*d) (40*d) L γ δ LG rfl h0 hX Binput hBi hL1 (by omega) (by omega) H
      (fun _ => hF _) S hcov Ccover hS t s hs hst ht k
    rw [tree_order_eq_twice_links hX] at hker
    have hq : (coupling d L γ δ:ℂ)^(2*m) = q := by
      simp only [q,coupling,Complex.ofReal_pow]
    rw [hq] at hker
    rw [hker]
    dsimp only [Ext, treeRootLeafMixture]
    rw [unitSquareCutoff_eq_one htvec]
    simp only [one_mul]
    have hsum (u : SourceCellIndex S × (Fin (Fintype.card (TPlus LG.garden)+1) → Fin d → ℝ)) :
        pairedInverseProfile (fun lam => ∑ Z : I, coef Z*treeNormalizedScalar hX (Rs Z) S lam u) ![t,s] =
          ∑ Z : I, coef Z*pairedInverseProfile (fun lam => treeNormalizedScalar hX (Rs Z) S lam u) ![t,s] := by
      rw [tree_pairedInverseProfile_finsetSum Finset.univ _ (fun Z _ => hiLam Z u)]
      exact Finset.sum_congr rfl fun Z _ => tree_pairedInverseProfile_const_mul _ _ _
    simp_rw [hsum, Finset.mul_sum]
    rw [integral_finsetSum _ (fun Z _ => ?_)]
    · refine Finset.sum_congr rfl fun Z _ => ?_
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      dsimp only
      rw [hpIP Z ![t,s] u]
      dsimp only [coef]
      ring
    · exact ((hiU Z ![t,s] k).const_mul (coef Z)).congr (ae_of_all _ fun u => by dsimp only; ring)
  -- the bound
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Set.Icc (0:ℝ) 1) ∧ (t.val 1∈Set.Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  have hEq (t : timeBoxGt 0 0) (k : (Set.univ : Set (Mom d))) :
      Ext t.val k.val = LGSpine.treeLeaves L γ δ LG H (t.val 0) (t.val 1) k.val := by
    have ht : (![t.val 0,t.val 1] : Fin 2 → ℝ)=t.val := by funext i; fin_cases i <;> rfl
    rw [← ht]
    exact (hId _ _ (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val).symm
  apply (Fourier.mixedRestrictionNorm_le_extension Ext hEq).trans
  have hE (Z : I) := henv L ((le_max_left _ _).trans hL) δ hδ hδ1 m hmpos hmlog (J Z) (C Z) (hCs Z)
  choose E hmE hpE hbE hgE using hE
  let P : ℝ := e*(Kr*δ)^m
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hfE (Z : I) : (∫⁻ lam, wL θ lam*ENNReal.ofReal (E Z lam)) < ⊤ :=
    (hbE Z).trans_lt (ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))
  have hbR (Z : I) : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ',
      ‖Rs Z lam β γ' z‖ ≤ P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*E Z lam := by
    filter_upwards [hgE Z] with lam hlam
    intro z β γ'
    refine (hlam z β γ').trans (le_of_eq ?_)
    dsimp only [P, e]
    ring
  have hh := tree_root_finite_scalar_profile_le hX hθ0 (RA1Leafwise.treeInputFam LG.garden H) (J := 30*d)
    (K := 40*d) (M := 40*d) (by omega) (by omega) hBi (fun _ => hF _) S hS Rs
    (fun Z z => stronglyMeasurable_physicalWeightedCellSymbol_joint hLp δ γ (J Z) (hC Z).reg.meas z)
    (fun _ => P) (fun _ => hP) coef hcoef E hmE hpE hfE hbR
  apply hh.trans
  have hcardI : Fintype.card I = 2^m := tree_coefficient_subset_count X (LG.garden.sig 0)
  have hsumle : (∑ Z : I, ENNReal.ofReal (P*treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
      ∫⁻ lam, wL θ lam*ENNReal.ofReal (E Z lam)) ≤
      (2:ℝ≥0∞)^m*(ENNReal.ofReal (P*treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
        (ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m))) := by
    calc _ ≤ ∑ _Z : I, ENNReal.ofReal (P*treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
          (ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m)) :=
          Finset.sum_le_sum fun Z _ => by rw [ENNReal.ofReal_one, one_mul]; gcongr; exact hbE Z
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, hcardI, nsmul_eq_mul]; norm_num
  have hb2 := hbudget m δ (treeSpectralFrequencyLoss X (LG.garden.sig 0)) 1 hδp.le
    (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (LG.garden.sig 0)))
    (RA1Leafwise.treeSpectralFrequencyLoss_le_geometric X (LG.garden.sig 0)) zero_le_one
  have hsecond : ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff *
        ∑ Z : I, ENNReal.ofReal (P*treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
          ∫⁻ lam, wL θ lam*ENNReal.ofReal (E Z lam) ≤
      Hc*(ENNReal.ofReal (e*(Kr*δ)^m*treeSpectralFrequencyLoss X (LG.garden.sig 0))*
        ((2:ℝ≥0∞)^m*(ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m)))) := by
    calc _ ≤ Hc * ((2:ℝ≥0∞)^m*(ENNReal.ofReal (P*treeSpectralFrequencyLoss X (LG.garden.sig 0)) *
          (ENNReal.ofReal 1*(2*ENNReal.ofReal Cw^m)))) := mul_le_mul' (le_refl _) hsumle
      _ = _ := by dsimp only [P]; ring
  have hcard : Fintype.card (TPlus LG.garden) + 1 = 2*m+1 := by rw [tree_input_count hX]
  rw [hcard, ← hlen]
  exact (mul_le_mul' (le_refl _) hsecond).trans (by simpa only [mul_one] using hb2)

end WaveTurbulence.Flower.FiltCoh
