/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftBlockClosure
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTopCut
public import WaveTurbulence.Foundations.XChain.ClosedPartitionUniqueness
/-! A canonical garden uniquely determines its top forest and its leaf partition. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem partition_unique_of_garden_eq {w : ℕ} (top : Fin w → TTree)
    (P Q : Finpartition (univ : Finset (GLeaf top))) (G H : Garden w) (hGH : G = H)
    (hP : ∀ B ∈ P.parts, TopRootsClosed G top B ∧
      ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ TopRootsClosed G top A)
    (hQ : ∀ B ∈ Q.parts, TopRootsClosed H top B ∧
      ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ TopRootsClosed H top A) : P = Q := by
  apply finpartition_eq_of_irreducible_closed_blocks P Q (TopRootsClosed G top)
    (topRootsClosed_inter G top) hP
  intro B hB
  refine ⟨(congrArg (fun K : Garden w => TopRootsClosed K top B) hGH).mpr (hQ B hB).1, ?_⟩
  intro A hAB hAn hAnB hclosed
  exact (hQ B hB).2 A hAB hAn hAnB
    ((congrArg (fun K : Garden w => TopRootsClosed K top A) hGH).mp hclosed)

theorem canonicalGraftData_top_eq {w p : ℕ} {sig : Fin w → ℤˣ}
    (C D : CanonicalGraftData sig p) (h : C.graft = D.graft) : C.top = D.top :=
  (canonicalGraftData_layerCutForest C).symm.trans
    ((congrArg (fun LG : LayeredGarden w => layerCutForest LG p) h).trans
      (canonicalGraftData_layerCutForest D))

theorem canonicalGraftData_partition_heq {w p : ℕ} {sig : Fin w → ℤˣ}
    (C D : CanonicalGraftData sig p) (htop : C.top = D.top)
    (h : C.graft.garden = D.graft.garden) : HEq C.partition D.partition := by
  have hC := C.partition_irreducible_closed_blocks
  have hD := D.partition_irreducible_closed_blocks
  cases C with
  | mk ct cp cl cpl cs ci cc =>
    cases D with
    | mk dt dp dl dpl ds di dc =>
      change ct = dt at htop
      cases htop
      exact heq_of_eq (partition_unique_of_garden_eq ct cp dp _ _ h hC hD)

end WaveTurbulence.Induct
