/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeUnintegratedSingularKernel
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeCountableHalfCellSingular
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingSpatialEstimate

/-! # Actual leading singular mixture equals the original continuum tree singular integral -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ApproxNT

/-- Original input moments justify counted singular Fubini for the actual leading profile. -/
theorem treeLeadingSpatialProfile_eq_singInt_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G) (hn : 0 < (X.treeLinks (G.sig 0)).length)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {Binput Ccover : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hBi : 0 ≤ Binput)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    treeLeadingSpatialProfile hX J f S k =
      singInt J (fun x y => (treeCarrier hX).sourceLeafWeight f k
        (fun j i => if i=0 then x j else y j)) := by
  obtain ⟨Mcell,hMcell,hcell⟩ := exists_cellOp_bound hd
  let P := (1+2*Real.pi)*
    (((2*max 1 (Real.sqrt d)+5)^(2*d))^(X.treeLinks (G.sig 0)).length*
      Mcell^(X.treeLinks (G.sig 0)).length*
        halfLinkFirstMomentConstant d^(2*(X.treeLinks (G.sig 0)).length))
  have hP : 0 ≤ P := by
    have := (halfLinkFirstMomentConstant_pos d).le
    have := zero_le_one.trans hMcell
    dsimp only [P]
    positivity
  let R := fun (_ : ℝ × ℝ) β γ z => singInt (d := d) J (halfCellAmplitude z β γ)
  have hmR (z) : StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R p.1 p.2.1 p.2.2 z) :=
    (stronglyMeasurable_singInt_halfCellAmplitude hd hn J z).comp_measurable measurable_snd
  have hbR (u) : ‖treeNormalizedScalar hX R S (0,0) u‖ ≤
      P*treeSpectralFrequencyLoss X (G.sig 0) := by
    have hh := treeNormalizedScalar_norm_le hX R S hP (by norm_num : (0:ℝ) ≤ 1)
      (0,0) (fun z β γ => by
        have h := norm_singInt_halfCellAmplitude_le hd hn (zero_le_one.trans hMcell) hcell J z β γ
        apply h.trans_eq
        dsimp only [P]
        ring) u
    simpa only [mul_one] using hh
  have hm : StronglyMeasurable (treeNormalizedScalar hX R S (0,0)) :=
    (stronglyMeasurable_treeNormalizedScalar hX R hmR S).comp_measurable
      (g := fun u : SourceCellIndex S ×
        (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ) => (((0,0):ℝ × ℝ),u))
      (measurable_const.prodMk measurable_id)
  have hi := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar f hK hM hBi hf S hS
    (treeNormalizedScalar hX R S (0,0)) hm hbR k
  have hs := treeRootSingularCoefficient_countable_moments hX f hK hM hBi hf S hS k
  have hcoef := stronglyMeasurable_treeRootSingularCoefficient hX f (by omega) hf S k
  have he := tree_singInt_tsum_integral_halfCells volume hd hn J
    (fun c : SourceCellIndex S => c.2.val)
    (fun α => (treeLeafModulations hX α).1) (fun α => (treeLeafModulations hX α).2)
    (continuous_treeLeafModulations hX).fst.measurable
    (continuous_treeLeafModulations hX).snd.measurable
    (treeRootSingularCoefficient hX f S k)
    (fun c => hcoef.comp_measurable (g := fun α => (c,α))
      (measurable_const.prodMk measurable_id)) hs.1 hs.2
  have hk : (fun x y => ∑' c : SourceCellIndex S, ∫ α,
      treeRootSingularCoefficient hX f S k c α *
        halfCellAmplitude c.2.val (treeLeafModulations hX α).1 (treeLeafModulations hX α).2 x y) =
      (fun x y => (treeCarrier hX).sourceLeafWeight f k (fun j i => if i=0 then x j else y j)) := by
    funext x y
    exact treeUnintegratedSingularKernel_eq_source hX f hK hM hBi hf S hcover hS k x y
  rw [hk] at he
  rw [treeLeadingSpatialProfile, integral_treeLeafCellMeasure_eq_tsum S _ hi]
  apply Eq.trans _ he.symm
  apply tsum_congr
  intro c
  apply integral_congr_ae
  apply ae_of_all
  intro α
  unfold treeRootSingularCoefficient treeNormalizedScalar
  dsimp only [R]
  ring

end WaveTurbulence.RA1Leafwise
