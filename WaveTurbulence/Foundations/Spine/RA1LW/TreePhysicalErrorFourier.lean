/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeSourceErrorEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteScalarEstimate

/-! # The complete finite original physical error family satisfies the full mixed norm bound -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT
open scoped ENNReal

/-- The actual source envelope controls a finite family of physical errors in the
full landed mixed norm; constants precede every logarithmic order exponent and tree. -/
theorem tree_finite_physical_error_fourier_bound {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    (Agev Cbase : ℝ) (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ K D : ℝ, 0 < K ∧ 1 ≤ D ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → δ ≤ 1/2 →
      ∀ (G : Garden 1) (X : RegChain) (hX : X.DecodesTree G),
      0 < (X.treeLinks (G.sig 0)).length →
      ((X.treeLinks (G.sig 0)).length:ℝ) ≤ Real.log L^Aorder →
      ∀ (ι : Type) [Fintype ι] (J : ι → Finset (Fin (X.treeLinks (G.sig 0)).length))
        (C : (i : ι) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ),
      (∀ i, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*(X.treeLinks (G.sig 0)).length+1)) (C i)) →
      ∀ (c : ι → ℂ), (∀ i, ‖c i‖ ≤ 1) →
      ∀ N Ksp M : ℕ, d+2+N ≤ Ksp → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ,
      (∀ a, Fourier.spatialNorm Ksp M (f a) ≤ ENNReal.ofReal Binput) →
      ∀ S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
        Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ),
      (∀ q, ((S q).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length) →
      Fourier.mixedFourierNorm η N 0
        (treeRootLeafMixture f S (fun t u => unitSquareCutoff t * pairedInverseProfile
          (fun lam => ∑ i, c i*treeNormalizedScalar hX
            (treePhysicalErrorScalar L δ γ (J i) (C i)) S lam u) t)) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d N) *
          (ENNReal.ofReal (Ccover^(X.treeLinks (G.sig 0)).length) *
            ENNReal.ofReal (leafMomentLocalizationConstant d (N+1) M *
              treeAugmentedInputBound d Ksp M Binput)^(Fintype.card (TPlus G)+1)))) *
        (ENNReal.ofReal (2^η)*Fourier.timeFourierNorm η unitSquareCutoff*
          (ENNReal.ofReal (((1+2*Real.pi)*(K*δ)^(X.treeLinks (G.sig 0)).length)*
              treeSpectralFrequencyLoss X (G.sig 0)) *
            ((Fintype.card ι:ℝ≥0∞)*(ENNReal.ofReal (L^(-gamma1 d γ+2*η))*
              (2*ENNReal.ofReal D^(X.treeLinks (G.sig 0)).length))))) := by
  obtain ⟨K,D,hK,hD,hEnv⟩ := tree_physical_error_scalar_envelope hd hγ hη0 hη hηγ hηγ' Agev Cbase hAgev hCbase
  refine ⟨K,D,hK,hD,fun Aorder => ?_⟩
  obtain ⟨L₁,hL₁⟩ := hEnv Aorder
  refine ⟨max L₁ 2,?_⟩
  intro L hL δ hδ hδ1 G X hX hn hnlog ι _ J C hC c hc N Ksp M hKsp hM Binput Ccover hBinput f hf S hS
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hδp : 0 < δ := by have := (Real.rpow_pos_of_pos hLp (-(η/2))).trans_le hδ; linarith
  choose E hmE hpE hfE hbE hgood using (fun i => hL₁ L ((le_max_left _ _).trans hL) δ hδ hδ1
    (X.treeLinks (G.sig 0)).length hn hnlog (J i) (C i) (hC i))
  let P := (1+2*Real.pi)*(K*δ)^(X.treeLinks (G.sig 0)).length
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hh := tree_root_finite_scalar_profile_le hX hη0.le f hKsp hM hBinput hf S hS
    (fun i => treePhysicalErrorScalar L δ γ (J i) (C i))
    (fun i z => stronglyMeasurable_treePhysicalErrorScalar_joint hd hn hLp δ γ (J i) (hC i).reg.meas z)
    (fun _ => P) (fun _ => hP) c hc E hmE hpE hfE hgood
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑ _i : ι, ENNReal.ofReal (P*treeSpectralFrequencyLoss X (G.sig 0))*
      (ENNReal.ofReal (L^(-gamma1 d γ+2*η))*(2*ENNReal.ofReal D^(X.treeLinks (G.sig 0)).length)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (hbE i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp only [P]
      ring

end WaveTurbulence.RA1Leafwise
