/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeGraphDomain

/-! # Exact almost-everywhere identification of the original internal tree domain -/

public section
noncomputable section
open scoped Classical
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- Closed upper layer endpoints recover the literal source constraints off their null boundaries. -/
theorem mem_internal_of_treeGraph {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden)
    {t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ}
    (ht : t ∈ graphStrictDomain (treeLayerLinks (d := d) LG hX) (treeClockEdges hX))
    (hne : ∀ b, treeClockEquiv hX t b ≠ (LG.layer b.toNode : ℝ) + 1) :
    treeClockEquiv hX t ∈ internalTimeDomain LG := by
  intro b
  obtain ⟨v, rfl⟩ := (treeLinkEquiv hX).surjective b
  have hv := ht.1 v
  rw [tree_vertexLayer, Int.cast_natCast] at hv
  have he : treeClockEquiv hX t (treeLinkEquiv hX v) = t v.1 v.2 := treeClockEquiv_link hX t v
  rw [← he] at hv
  refine ⟨hv.1, lt_of_le_of_ne hv.2 (hne _), ?_, ?_⟩
  · exact lt_of_le_of_lt (Nat.cast_nonneg _) hv.1
  · intro b' hb'
    obtain ⟨w, rfl⟩ := (treeLinkEquiv hX).surjective b'
    have hh := ht.2 w v ((mem_treeClockEdges hX w v).mpr hb')
    simpa only [treeClockEquiv_link] using hh

/-- All source upper-layer and graph-edge equalities are null in the actual link clocks. -/
theorem ae_treeClock_regular (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) :
    ∀ᵐ t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ,
      (∀ b, treeClockEquiv hX t b ≠ (LG.layer b.toNode : ℝ) + 1) ∧
      (∀ v w, (v,w) ∈ treeClockEdges hX → t v.1 v.2 ≠ t w.1 w.2) := by
  have hu : ∀ᵐ τ : GBranch LG.garden.tree → ℝ,
      ∀ b, τ b ≠ (LG.layer b.toNode : ℝ) + 1 := by
    apply ae_all_iff.mpr
    intro b
    exact Measure.ae_eval_ne (fun _ : GBranch LG.garden.tree => (volume : Measure ℝ)) b _
  have he : ∀ᵐ τ : GBranch LG.garden.tree → ℝ,
      ∀ v w, (v,w) ∈ treeClockEdges hX → τ (treeLinkEquiv hX v) ≠ τ (treeLinkEquiv hX w) := by
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro w
    by_cases hh : (v,w) ∈ treeClockEdges hX
    · have hn : treeLinkEquiv hX v ≠ treeLinkEquiv hX w :=
        fun eq => treeClockEdges_ne hX hh ((treeLinkEquiv hX).injective eq)
      filter_upwards [ae_clock_ne_clock _ _ hn] with τ hτ
      exact fun _ => hτ
    · exact Filter.Eventually.of_forall fun _ hh' => False.elim (hh hh')
  have hmp := (measurePreserving_treeClockEquiv hX).quasiMeasurePreserving
  filter_upwards [hmp.ae hu, hmp.ae he] with t htu hte
  refine ⟨htu, ?_⟩
  intro v w hw
  simpa only [treeClockEquiv_link] using hte v w hw

/-- The constructed actual fibers equal the original source internal domain almost everywhere. -/
theorem tree_internal_ae_actualFibers {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX) :
    treeClockEquiv hX ⁻¹' internalTimeDomain LG =ᵐ[volume]
      (actualTreeFibers (d := d) LG hX C).timeDomain := by
  filter_upwards [ae_treeClock_regular LG hX] with t ht
  apply propext
  constructor
  · exact mem_actualTreeFibers_of_internal LG hX C
  · intro hh
    exact mem_internal_of_treeGraph LG hX
      (mem_graphStrictDomain_of_fibers C.selection _ _ C.edge_index ht.2 hh) ht.1

end WaveTurbulence.IncohInst
