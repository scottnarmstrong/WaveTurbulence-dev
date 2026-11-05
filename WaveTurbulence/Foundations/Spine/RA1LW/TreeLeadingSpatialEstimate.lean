/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile
public import WaveTurbulence.Foundations.RegAsymp.TreeRootSpatialMixture
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellSingularRepresentation
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ParametricHalfCell

/-! # The actual singular tree spectral mixture has a full spatial bound -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ApproxNT

/-- Literal leading spatial mixture before recursive Nstar identification. -/
def treeLeadingSpatialProfile {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) (k : Mom d) : ℂ :=
  ∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
    treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0) u
      ∂treeLeafCellMeasure S

/-- One linear modulation loss, paid by the original leaf Fourier moment, suffices
for the full tree leading spatial norm. The constant precedes codes and input functions. -/
theorem treeLeadingSpatialProfile_spatialNorm {d : ℕ} (hd : 3 ≤ d) :
    ∃ Mcell : ℝ, 1 ≤ Mcell ∧
      ∀ (G : Garden 1) (X : RegChain) (hX : X.DecodesTree G),
      0 < (X.treeLinks (G.sig 0)).length →
      ∀ J : Finset (Fin (X.treeLinks (G.sig 0)).length),
      ∀ N K M : ℕ, d+2+N ≤ K → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ,
      (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal Binput) →
      ∀ S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
        Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length) →
      Fourier.spatialNorm N 0 (treeLeadingSpatialProfile hX J f S) ≤
        (ENNReal.ofReal (rootLocalOverlapConstant d) *
          (ENNReal.ofReal (treeRootLeafDerivativeConstant d N) *
            (ENNReal.ofReal (Ccover^(X.treeLinks (G.sig 0)).length) *
              ENNReal.ofReal (leafMomentLocalizationConstant d (N+1) M *
                treeAugmentedInputBound d K M Binput)^(Fintype.card (TPlus G)+1)))) *
          ENNReal.ofReal (((1+2*Real.pi)*
            (((2*max 1 (Real.sqrt d)+5)^(2*d))^(X.treeLinks (G.sig 0)).length*
              Mcell^(X.treeLinks (G.sig 0)).length*
                halfLinkFirstMomentConstant d^(2*(X.treeLinks (G.sig 0)).length)))*
                  treeSpectralFrequencyLoss X (G.sig 0)) := by
  obtain ⟨Mcell,hMcell,hcell⟩ := exists_cellOp_bound hd
  refine ⟨Mcell,hMcell,?_⟩
  intro G X hX hn J N K M hK hM Binput Ccover hBi f hf S hS
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
  change Fourier.spatialNorm N 0 (fun k => ∫ u,
    rootAmplitudeSum (treeRootLeafAmplitude f S) k u * treeNormalizedScalar hX R S (0,0) u
      ∂treeLeafCellMeasure S) ≤ _
  exact spatialNorm_treeRootLeafMixture_le (d := d)
    (n := (X.treeLinks (G.sig 0)).length) (m := Fintype.card (TPlus G))
    (K := K) (M := M) (J := N) (B := Binput) (C := Ccover)
    (Q := P*treeSpectralFrequencyLoss X (G.sig 0)) f hK hM hBi hf S hS
    (treeNormalizedScalar hX R S (0,0))
    hm hbR

end WaveTurbulence.RA1Leafwise
