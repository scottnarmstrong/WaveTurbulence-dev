/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleDecay
public import WaveTurbulence.Foundations.IncohInst.OneRootDecay
public import WaveTurbulence.Foundations.IncohInst.TrivialTreeBranches
public import WaveTurbulence.Foundations.Incoh.Proposition51
public import WaveTurbulence.Foundations.IncohInst.CoupleExternalBox
public import WaveTurbulence.Foundations.IncohInst.NormBridge
public import WaveTurbulence.Foundations.Incoh.CoupleUpperPropositionRate

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
theorem exists_KQstar_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ F : ℕ → Mom d → ℝ,
        (∀ r ≤ p, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B) →
        XNormRestr η (30 * d) (30 * d) (timeBox q q') univ
          (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) ≤
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)) := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := exists_KQstar_twoRoot_decay d hd B hB
  obtain ⟨Cone, hCone, hone⟩ := exists_KQstar_oneRoot_decay d hd B hB
  refine ⟨max Ctwo Cone, hCtwo.trans_le (le_max_left _ _), ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lt, hLt, htwo⟩ := htwo η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lo, hLo, hone⟩ := hone η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  refine ⟨max Lt Lo, hLt.trans (le_max_left _ _), ?_⟩
  intro L hL p hpD Q LG hQ hlayers q q' hq hq' hrootq hrootq' hg F hF
  have hLone : 1 ≤ L := hLt.trans ((le_max_left Lt Lo).trans hL)
  have hpos : 0 ≤ L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) :=
    Real.rpow_nonneg (zero_le_one.trans hLone) _
  have ht (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) :=
    (htwo L ((le_max_left Lt Lo).trans hL) p hpD Q LG hQ hb hlayers q q' hq hq'
      hrootq hrootq' hg F hF).trans
      (sourceRate_mono_constant hCtwo.le (le_max_left Ctwo Cone) hδ.le hpos Q.links.length)
  have ho (a : Fin 2) (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
      (hw : ∀ b : GBranch LG.garden.tree, b.1.1 = a) :=
    (hone L ((le_max_right Lt Lo).trans hL) p hpD Q LG hQ a hb hw hlayers q q' hq hq'
      hrootq hrootq' hg F hF).trans
      (sourceRate_mono_constant hCone.le (le_max_right Ctwo Cone) hδ.le hpos Q.links.length)
  by_cases h0 : ([] : TTree.Path) ∈ (LG.garden.tree 0).branching
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · exact ht (fun i => by fin_cases i <;> assumption)
    · apply ho 0 h0
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 1 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h1
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · apply ho 1 h1
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 0 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h0
    · have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ)
        ((coupleLayerLinks_incoherenceCount d hQ).symm ▸ hg)
      let b := chosenBranch hQ (⟨0, by omega⟩ : Fin Q.links.length)
      have hr := root_mem_branching_of_mem b.2
      by_cases hb : b.1.1 = 0
      · rw [hb] at hr
        exact False.elim (h0 hr)
      · have hb1 : b.1.1 = 1 := by omega
        rw [hb1] at hr
        exact False.elim (h1 hr)

end WaveTurbulence.IncohInst
