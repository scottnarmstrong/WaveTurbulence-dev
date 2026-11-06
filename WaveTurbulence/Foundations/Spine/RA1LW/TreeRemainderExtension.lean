/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeOriginalErrorDensity
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalErrorFourier
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeErrorAbsorption
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeSubsetCount
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCoefficientWeights
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeCellCover

/-! # Uniform full mixed-norm extension of the literal original tree remainder -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef
open scoped ENNReal

/-- The actual source kernel-minus-app has the required full mixed-norm extension,
with constants before the order exponent and a single weak2eta loss in L. -/
theorem exists_tree_remainder_extension_bound {d : ℕ} (hd : 3 ≤ d) {γ η B : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → δ ≤ 1/2 →
      ∀ H : LGSpine.LeafProfiles 1 d, (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ (X : RegChain), X.wf=true → ∀ (LG : LayeredGarden 1) (_hX : X.DecodesTree LG.garden),
      (∀ a, LG.layer a=0) → 0 < (X.treeLinks (LG.garden.sig 0)).length →
      ((X.treeLinks (LG.garden.sig 0)).length:ℝ) ≤ Real.log L^Aorder →
      ∃ E : (Fin 2 → ℝ) → Mom d → ℂ,
        (∀ t s : ℝ, 0 ≤ s → s<t → t≤1 → ∀ k,
          E ![t,s] k=LGSpine.treeLeaves L γ δ LG H t s k-LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) t s k) ∧
        Fourier.mixedFourierNorm η (30*d) 0 E ≤
          ENNReal.ofReal (C*(C*δ)^(X.treeLinks (LG.garden.sig 0)).length*L^(-gamma1 d γ+2*η)) := by
  classical
  let Agev := max 1 ClassJR.A1
  let Cbase := max 1 |CTη η|
  have hAgev : 0 ≤ Agev := zero_le_one.trans (le_max_left _ _)
  have hCbase : 1 ≤ Cbase := le_max_left _ _
  obtain ⟨K,D,hK,hD,hFourier⟩ := tree_finite_physical_error_fourier_bound hd hγ hη0 hη hηγ hηγ'
    Agev Cbase hAgev hCbase
  obtain ⟨Ccover,hCcover,hcover⟩ := actual_tree_augmented_uniform_cell_cover d (by omega)
  let a := rootLocalOverlapConstant d
  let b := treeRootLeafDerivativeConstant d (30*d)
  let p := leafMomentLocalizationConstant d (30*d+1) (40*d)*treeAugmentedInputBound d (40*d) (40*d) B
  let e := 1+2*Real.pi
  let Hc := ENNReal.ofReal (2^η)*Fourier.timeFourierNorm η unitSquareCutoff
  have ha : 0 ≤ a := (rootLocalOverlapConstant_pos d).le
  have hb : 0 ≤ b := treeRootLeafDerivativeConstant_nonneg d (30*d)
  have hp : 0 ≤ p := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg _))
    · exact (treeAugmentedInputBound_pos d (40*d) (40*d) B).le
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hH : Hc < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top _)
  obtain ⟨C,hC,hbudget⟩ := tree_error_budget_absorption ha hb hCcover.le hp he hK.le
    (zero_le_one.trans hD) Hc hH
  refine ⟨C,hC,fun Aorder => ?_⟩
  obtain ⟨L₁,hL₁⟩ := hFourier Aorder
  refine ⟨max L₁ 2,?_⟩
  intro L hL δ hδ hδ1 H hF X hwf LG hX h0 hn hnlog
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₁ 2).trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδp : 0 < δ := by have := (Real.rpow_pos_of_pos hLp (-(η/2))).trans_le hδ; linarith
  choose S hS hcov using hcover LG.garden X hX
  obtain ⟨Csym,hCsym,hId⟩ := exists_tree_original_error_density hd hη0 (by linarith)
    (le_max_right _ _) hwf LG hX h0 hL1 δ γ hδp.ne' hB hF S
      (fun c k x hx z hz => hcov c k x hx z hz) hS
  let I := (ClassJR.chosenSet ((toJRc X).linksAt (LG.garden.sig 0) (rootT (LG.garden.sig 0)))).powerset
  let J := fun Z : I => treeMarkedIndices (treeChosenAddress X (LG.garden.sig 0)) Z.val
  let coef := fun Z : I => LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹)
  let density := fun lam u => ∑ Z : I, coef Z*treeNormalizedScalar hX
    (treePhysicalErrorScalar L δ γ (J Z) (Csym Z)) S lam u
  let Ext := treeRootLeafMixture (treeInputFam LG.garden H) S
    (fun t u => unitSquareCutoff t*pairedInverseProfile (fun lam => density lam u) t)
  have hcoef (Z : I) : ‖coef Z‖ ≤ 1 := by
    rw [show coef Z=LG.garden.zeta*(∏ z ∈ Z.val, ((nodeSgn z:ℂ)*Real.pi*Complex.I)⁻¹) from rfl,
      norm_mul,tree_garden_zeta_norm,one_mul]
    exact tree_coefficient_weight_norm_le Z.val
  have hsize : X.size=2*(X.treeLinks (LG.garden.sig 0)).length := by
    have hh := chain_linksAt_length X (LG.garden.sig 0) ((0:Fin 1),[])
    change (X.treeLinks (LG.garden.sig 0)).length*2=X.size at hh
    omega
  have hexp : 2*X.size+1=4*(X.treeLinks (LG.garden.sig 0)).length+1 := by omega
  have hCs (Z : I) : SRep (1-η/8) (η/4) (1-η/2) Agev
      (Cbase^(4*(X.treeLinks (LG.garden.sig 0)).length+1)) (Csym Z) := by
    apply tree_SRep_mono_mass (hCsym Z) hAgev
    rw [hexp]
    exact tree_literal_coefficient_mass_le (CTη η) _
  refine ⟨Ext,?_,?_⟩
  · intro t s hs hst ht k
    have htvec : ∀ i : Fin 2, (![t,s] : Fin 2 → ℝ) i ∈ Set.Icc (0:ℝ) 1 := by
      intro i
      fin_cases i
      · exact ⟨hs.trans hst.le,ht⟩
      · exact ⟨hs,hst.le.trans ht⟩
    have hh := hId t s hs hst ht k
    simpa only [Ext,density,coef,J,I,treeRootLeafMixture,unitSquareCutoff_eq_one htvec,one_mul] using hh.symm
  · have hh := hL₁ L ((le_max_left _ _).trans hL) δ hδ hδ1 LG.garden X hX hn hnlog I J Csym hCs
      coef hcoef (30*d) (40*d) (40*d) (by omega) (by omega) B Ccover hB
      (treeInputFam LG.garden H) (fun _ => hF _) S hS
    simp only [tree_input_count hX,I,tree_coefficient_subset_count,Nat.cast_pow,Nat.cast_ofNat] at hh
    apply hh.trans
    exact hbudget (X.treeLinks (LG.garden.sig 0)).length δ (treeSpectralFrequencyLoss X (LG.garden.sig 0))
      (L^(-gamma1 d γ+2*η)) hδp.le
      (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (LG.garden.sig 0)))
      (treeSpectralFrequencyLoss_le_geometric X (LG.garden.sig 0)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.RA1Leafwise
