/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.OneRootKernelFromInputs
public import WaveTurbulence.Foundations.IncohInst.OneRootExternalBox
public import WaveTurbulence.Foundations.IncohInst.NormBridge
public import WaveTurbulence.Foundations.Incoh.OneClockUpperPropositionRate

/-! # B2.2 for actual decoded couples with two branching roots -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The exact original source couple satisfies Proposition 5.1 on B2's external box.
Every finite momentum field, source norm bridge, time-domain identity and Fubini premise
is discharged from the decoded source and its input spatial norms. -/
theorem exists_KQstar_oneRoot_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        ∀ a : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree a).branching →
        (∀ b : GBranch LG.garden.tree, b.1.1 = a) →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ F : ℕ → Mom d → ℝ,
        (∀ r ≤ p, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B) →
        XNormRestr η (30 * d) (30 * d) (timeBox q q') univ
          (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) ≤
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)) := by
  obtain ⟨C, hC, hb⟩ := exists_rawOneClockKernel_upper_propositionRate d hd B hB
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ hsmall (finiteLayerCutoff D)
    (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D) γ hγ hηγ δ hδ hδ₁
    ((D : ℝ) + 1) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL p hpD Q LG hQ a hroot hwidth hlayers q q' hq hq' hrootq hrootq' hg F hF
  have hLone := hL₀.trans hL
  have hcount := coupleLayerLinks_incoherenceCount d hQ
  have hg' : 1 ≤ incoherenceCount (coupleLayerLinks (d := d) LG hQ) := hcount ▸ hg
  have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ) hg'
  have hm : Fintype.card (PlusLeaf LG.garden) ≤ 3 * Q.links.length := by
    rw [coupleCarrier_input_count hQ]
    omega
  have hspan (j) : |(((coupleLayerLinks (d := d) LG hQ j).leftLayer : ℝ)) -
      (coupleLayerLinks (d := d) LG hQ j).rightLayer| + 1 ≤ (D : ℝ) + 1 :=
    (coupleLayerLinks_span d hQ hlayers j).trans (by exact_mod_cast Nat.add_le_add_right hpD 1)
  let R := oneRootCoordinates hQ hn a hroot
  let b := passiveClockBase q q' a
  have hshift (t : Fin 2 → ℝ) (ht : t ∈ timeBox q q') :=
    R.oneClockShift_upper_bounds (coupleLayerLinks (d := d) LG hQ) a b t
      (timeBox_above_oneRoot d hQ hn a hroot q q' hrootq hrootq' ht)
      (fun j hj => (timeBox_passive_bounds q q' a ht j hj).1)
  have hbase : 0 ≤ R.baseRootTimes (coupleLayerLinks (d := d) LG hQ) a := by
    rw [oneRootCoordinates_base]
    exact Nat.cast_nonneg _
  have hχrect (t : Fin 2 → ℝ) (ht : t ∈ timeBox q q') :=
    R.finiteLayerCutoff_one_on_oneClock_rectangle (coupleLayerLinks (d := d) LG hQ) a b D t hbase
      (timeBox_clock_upper D q q' (hq.trans hpD) (hq'.trans hpD) ht a)
      (fun j hj => (timeBox_passive_bounds q q' a ht j hj).2)
  have hraw := hb L hL Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2 hm
    (coupleCarrier hQ) (coupleRootInputCoordinates hQ) (coupleCarrier_all_leaves hQ)
    (coupleLayerLinks LG hQ) hspan hg' R a b
    (coupleInternalLinkDomain LG hQ) (measurableSet_coupleInternalLinkDomain hQ)
    (coupleInternalLinkDomain_subset_boxes d hQ) (coupleInputFunctions LG F)
    (fun a => coupleInputFunctions_spatialNorm_le LG F hlayers hF a)
    (timeBox q q') (fun t ht => (hshift t ht).1) (fun t ht => (hshift t ht).2) hχrect
    (gardenCircle LG.garden) univ
  rw [hcount] at hraw
  apply (XNormRestr_le_mixed (by omega : 30 * d ≠ 0) η (timeBox q q') univ _).trans
  convert hraw using 1
  congr 1
  funext ts k
  exact KQstar_eq_oneRoot_raw hQ hn a hroot hwidth (by omega) L γ δ hLone F hlayers hB hF k ts

end WaveTurbulence.IncohInst
