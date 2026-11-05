/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ReindexedPairingClosure
/-! Canonicity is invariant under exact relabelling of ordered roots. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem reindexLayeredGarden_criterion {v w : ℕ} (LG : LayeredGarden w) (e : Fin v ≃ Fin w)
    (q : ℕ) (hc : LG.CanonCriterion q) : (reindexLayeredGarden LG e).CanonCriterion q := by
  refine ⟨fun a => hc.1 (reindexNodeEquiv LG.garden.tree e a), ?_⟩
  intro a b hinc hcp
  have hic : (reindexNodeEquiv LG.garden.tree e a).Incomparable (reindexNodeEquiv LG.garden.tree e b) :=
    ⟨fun h => hinc.1 ((reindexNodeEquiv_isDesc_iff LG.garden.tree e a b).mp h),
      fun h => hinc.2 ((reindexNodeEquiv_isDesc_iff LG.garden.tree e b a).mp h)⟩
  have hleaves := congrArg₂ (fun (s t : Finset (GLeaf LG.garden.tree)) => s ∪ t)
    (reindexNodeEquiv_leavesBelow LG.garden.tree e a) (reindexNodeEquiv_leavesBelow LG.garden.tree e b)
  have hleaves' := hleaves.trans (Finset.map_union a.leavesBelow b.leavesBelow).symm
  have hp := (reindexGarden_completelyPaired_iff LG.garden e _).mpr hcp
  have hpair := (congrArg LG.garden.CompletelyPaired hleaves').mpr hp
  have hh := hc.2 _ _ hic hpair
  have he := congrArg₂ min (reindexLayeredGarden_parentLayer LG e q a)
    (reindexLayeredGarden_parentLayer LG e q b)
  exact he.le.trans hh

theorem reindexLayeredGarden_isCanonG {v w p : ℕ} (LG : LayeredGarden w) (e : Fin v ≃ Fin w)
    (hG : IsCanonG p LG) : IsCanonG p (reindexLayeredGarden LG e) := by
  cases p with
  | zero => exact False.elim hG
  | succ q =>
    have hvw : v = w := by simpa only [Fintype.card_fin] using Fintype.card_congr e
    have hw : 4 ≤ v := hvw.symm ▸ hG.1
    exact ⟨hw, fun ℓ => hG.2.1 (reindexLeafEquiv LG.garden.tree e ℓ),
      reindexGarden_irreducible LG.garden e hG.2.2.1,
      reindexLayeredGarden_criterion LG e q hG.2.2.2⟩

end WaveTurbulence.Induct
