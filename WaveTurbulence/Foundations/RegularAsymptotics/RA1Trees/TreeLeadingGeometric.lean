/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeGeometricBudget
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingSpatialEstimate
public import WaveTurbulence.Foundations.IncohInst.TreeLeafRows

/-! # The actual moving-root tree leading profile has a uniform geometric spatial bound -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh IncohInst Links

/-- All actual spatial constants precede every tree, order and order-cutoff exponent. -/
theorem exists_treeLeadingSpatialProfile_geometric_bound {d : ℕ} (hd : 3 ≤ d)
    (N K M : ℕ) (hK : d+2+N ≤ K) (hM : 2*d ≤ M) (B Ccover : ℝ) (hB : 0 ≤ B) (hCc : 0 ≤ Ccover) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Garden 1) (X : RegChain) (hX : X.DecodesTree G),
      0 < (X.treeLinks (G.sig 0)).length →
      ∀ (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
        (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ),
      (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
      ∀ S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
        Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length) →
      Fourier.spatialNorm N 0 (treeLeadingSpatialProfile hX J f S) ≤
        ENNReal.ofReal (C*C^(X.treeLinks (G.sig 0)).length) := by
  obtain ⟨Mcell,hMcell,hbound⟩ := treeLeadingSpatialProfile_spatialNorm hd
  let a := rootLocalOverlapConstant d
  let b := treeRootLeafDerivativeConstant d N
  let p := leafMomentLocalizationConstant d (N+1) M*treeAugmentedInputBound d K M B
  let e := 1+2*Real.pi
  let q := (2*max 1 (Real.sqrt d)+5)^(2*d)
  let s := halfLinkFirstMomentConstant d
  have ha : 0 ≤ a := (rootLocalOverlapConstant_pos d).le
  have hb : 0 ≤ b := treeRootLeafDerivativeConstant_nonneg d N
  have hp : 0 ≤ p := by
    apply mul_nonneg
    · unfold leafMomentLocalizationConstant
      exact mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _) (tsum_nonneg (cellCenterWeight_nonneg M))
    · exact (treeAugmentedInputBound_pos d K M B).le
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hs : 0 ≤ s := (halfLinkFirstMomentConstant_pos d).le
  have hMc : 0 ≤ Mcell := zero_le_one.trans hMcell
  obtain ⟨C,hC,hgeom⟩ := exists_common_geometric_bound (a*b*p*e) (Ccover*p^2*q*Mcell*s^2*9)
  refine ⟨C,hC,?_⟩
  intro G X hX hn J f hf S hS
  have hh := hbound G X hX hn J N K M hK hM B Ccover hB f hf S hS
  rw [tree_input_count hX] at hh
  have hx := zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (G.sig 0))
  have hrow := treeSpectralFrequencyLoss_le_geometric X (G.sig 0)
  change Fourier.spatialNorm N 0 (treeLeadingSpatialProfile hX J f S) ≤
    (ENNReal.ofReal a*(ENNReal.ofReal b*(ENNReal.ofReal (Ccover^(X.treeLinks (G.sig 0)).length)*
      ENNReal.ofReal p^(2*(X.treeLinks (G.sig 0)).length+1))))*
      ENNReal.ofReal (e*(q^(X.treeLinks (G.sig 0)).length*Mcell^(X.treeLinks (G.sig 0)).length*
        s^(2*(X.treeLinks (G.sig 0)).length))*treeSpectralFrequencyLoss X (G.sig 0)) at hh
  rw [tree_ofReal_spatial_budget ha hb hCc hp he hq hMc hs hx] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal ((tree_spatial_budget_le_geometric ha hb hCc hp he hq hMc hs _ hrow).trans (hgeom _)))

end WaveTurbulence.RegAsymp
