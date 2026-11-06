/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRootLayers
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
public import WaveTurbulence.Foundations.Incoh.FiniteLayerCutoff

/-! # The exact B2 external boxes satisfy the proved analytic upper-box conditions -/

public section
noncomputable section
open Set
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh

variable {LG : LayeredGarden 2} {Q : RegCpl}

/-- B2's root-layer inequalities place its entire external box above the actual roots. -/
theorem timeBox_above_couple_roots (d : ℕ) (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) (q q' : ℕ)
    (hq : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hq' : LG.layer (GNode.root LG.garden.tree 1) ≤ q') :
    ∀ t ∈ timeBox q q', (coupleRootCoordinates hQ hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) ≤ t := by
  intro t ht i
  rw [couple_baseRootTimes]
  fin_cases i
  · exact (show (LG.layer (GNode.root LG.garden.tree 0) : ℝ) ≤ q by exact_mod_cast hq).trans ht.1.1
  · exact (show (LG.layer (GNode.root LG.garden.tree 1) : ℝ) ≤ q' by exact_mod_cast hq').trans ht.2.1

/-- One actual finite-layer cutoff covers every local integration rectangle on B2's box. -/
theorem finiteLayerCutoff_one_on_couple_box (d D : ℕ) (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) (q q' : ℕ)
    (hq : q ≤ D) (hq' : q' ≤ D) :
    ∀ t ∈ timeBox q q', ∀ j : Fin 2,
      ∀ s ∈ Icc (0 : ℝ) ((t - (coupleRootCoordinates hQ hb).baseRootTimes
        (coupleLayerLinks (d := d) LG hQ)) j), finiteLayerCutoff D s = 1 := by
  intro t ht j s hs
  apply finiteLayerCutoff_eq_one
  rw [abs_of_nonneg hs.1]
  have hbase : 0 ≤ (coupleRootCoordinates hQ hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) j := by
    rw [couple_baseRootTimes]
    exact Nat.cast_nonneg _
  have hts : t j ≤ (D : ℝ) + 1 := by
    fin_cases j
    · exact ht.1.2.trans (by exact_mod_cast Nat.add_le_add_right hq 1)
    · exact ht.2.2.trans (by exact_mod_cast Nat.add_le_add_right hq' 1)
  have hs' : s ≤ t j - (coupleRootCoordinates hQ hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) j := hs.2
  linarith only [hs', hbase, hts]

end WaveTurbulence.IncohLeafwise
