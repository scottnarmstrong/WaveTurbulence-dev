/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeLeadingSpatialEstimate
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePointScalar

/-! # Actual bounded measurable scalar control of the leading tree mixture -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ApproxNT

/-- The original singular operator at empty order is exactly evaluation at zero. -/
theorem tree_singInt_eq_eval_of_zero {d n : ℕ} (hn : n=0) (J : Finset (Fin n))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) : singInt J W=W 0 0 := by
  subst n
  rfl

/-- The actual leading scalar after paying its single leaf moment is bounded and
measurable, including the empty-order case. No source spatial estimate is assumed. -/
theorem exists_treeLeadingScalar_control {d : ℕ} (hd : 3 ≤ d)
    {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ)) :
    ∃ D : ℝ, 0 ≤ D ∧
      StronglyMeasurable (treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0)) ∧
      ∀ u, ‖treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0) u‖ ≤ D := by
  by_cases hn : 0 < (X.treeLinks (G.sig 0)).length
  · obtain ⟨Mcell,hMcell,hcell⟩ := exists_cellOp_bound hd
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

    refine ⟨P*treeSpectralFrequencyLoss X (G.sig 0),
      mul_nonneg hP (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (G.sig 0))),hm,hbR⟩
  · have hn0 : (X.treeLinks (G.sig 0)).length=0 := by omega
    have he : treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0) =
        treePointScalar hX 0 0 S := by
      funext u
      dsimp only [treePointScalar,treeNormalizedScalar]
      rw [tree_singInt_eq_eval_of_zero hn0]
    rw [he]
    exact ⟨1,zero_le_one,stronglyMeasurable_treePointScalar hX 0 0 S,treePointScalar_norm_le_one hX 0 0 S⟩

end WaveTurbulence.RA1Leafwise
