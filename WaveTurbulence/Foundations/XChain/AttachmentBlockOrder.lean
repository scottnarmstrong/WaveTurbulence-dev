/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalTopDecomp
/-! The source attachment-order predicate counts exactly one CANON block. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem attachedOrder_eq_block_sum {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : P.parts) (u : GNode LG.garden.tree) (hu : u ∈ B.1) :
    LG.attachedOrder p u = ∑ v ∈ B.1, v.orderBelow := by
  classical
  have hcan := Canon.uniqueness p false (LG.attachNodes p) P hTD
  have he : (LG.attachNodes p).filter
      (fun v => Relation.EqvGen (LG.AttachLinkedOn p) u v) = B.1 := by
    ext v
    constructor
    · intro hv
      exact (hcan.2 B.1 B.2 u hu v (mem_filter.mp hv).1).mpr (mem_filter.mp hv).2
    · intro hv
      have hvU := P.le B.2 hv
      exact mem_filter.mpr ⟨hvU, (hcan.2 B.1 B.2 u hu v hvU).mp hv⟩
  change (∑ v ∈ (LG.attachNodes p).filter _, v.orderBelow) = _
  rw [he]

end WaveTurbulence.Induct
