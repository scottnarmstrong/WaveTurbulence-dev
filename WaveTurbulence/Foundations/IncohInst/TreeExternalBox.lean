/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeKernelFromInputs
public import WaveTurbulence.Foundations.IncohInst.TreeLayers
public import WaveTurbulence.Foundations.WaveB.FrozenB2
public import WaveTurbulence.Foundations.Incoh.FiniteLayerCutoff

/-! # Actual tree clock boxes lie in the finite source cutoff -/

public section
noncomputable section
open Set
namespace WaveTurbulence.IncohInst
open Incoh

theorem finiteLayerCutoff_one_on_tree_clocks {d : ℕ} (D : ℕ) (LG : LayeredGarden 1)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (hp : ∀ a, LG.layer a ≤ D)
    {r : ℕ} (R : RootCoordinates (X.treeLinks (LG.garden.sig 0)).length r) :
    ∀ v ∈ R.rootBox (treeLayerLinks (d := d) LG hX), ∀ j, finiteLayerCutoff D (v j) = 1 := by
  intro v hv j
  apply finiteLayerCutoff_eq_one
  have hl := hv.1 j
  have hu := hv.2 j
  change (vertexLayer (treeLayerLinks (d := d) LG hX) (R.rootVertex j) : ℝ) ≤ v j at hl
  change v j ≤ (vertexLayer (treeLayerLinks (d := d) LG hX) (R.rootVertex j) : ℝ) + 1 at hu
  rw [tree_vertexLayer, Int.cast_natCast] at hl hu
  have hb : (LG.layer (treeLinkEquiv hX (R.rootVertex j)).toNode : ℝ) ≤ D := by exact_mod_cast hp _
  have hn : (0 : ℝ) ≤ LG.layer (treeLinkEquiv hX (R.rootVertex j)).toNode := Nat.cast_nonneg _
  rw [abs_of_nonneg (hn.trans hl)]
  linarith only [hu, hb]

theorem finiteLayerCutoff_one_on_timeBoxGt (D q q' : ℕ) (hq : q ≤ D) (hq' : q' ≤ D) :
    ∀ t ∈ timeBoxGt q q', ∀ j : Fin 2, finiteLayerCutoff D (t j) = 1 := by
  intro t ht j
  have hb : t ∈ timeBox q q' := ht.1
  apply finiteLayerCutoff_eq_one
  fin_cases j
  · change |t 0| ≤ (D : ℝ) + 2
    rw [abs_of_nonneg ((Nat.cast_nonneg q).trans hb.1.1)]
    have hh : (q : ℝ) ≤ D := by exact_mod_cast hq
    linarith only [hb.1.2, hh]
  · change |t 1| ≤ (D : ℝ) + 2
    rw [abs_of_nonneg ((Nat.cast_nonneg q').trans hb.2.1)]
    have hh : (q' : ℝ) ≤ D := by exact_mod_cast hq'
    linarith only [hb.2.2, hh]

end WaveTurbulence.IncohInst
