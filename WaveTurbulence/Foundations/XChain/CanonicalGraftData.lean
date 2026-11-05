/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGardenGraft
/-! Source construction data for canonical grafts, with genuinely zero-order terminal pairs. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

structure CanonicalGraftData {w : ℕ} (sig : Fin w → ℤˣ) (p : ℕ) where
  top : Fin w → TTree
  partition : Finpartition (univ : Finset (GLeaf top))
  low : (B : partition.parts) → LayeredGarden B.1.card
  plain : ∀ B, (low B).garden.IsPlain
  sign : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top partition).symm ⟨B, k⟩).1
  irreducible : TopPartitionIrreducible top partition
  component : ∀ B, IsCanonG p (low B) ∨
    B.1.card = 2 ∧ (∀ k, (low B).garden.tree k = TTree.leaf) ∧ ∀ a, (low B).layer a = p

namespace CanonicalGraftData

theorem layer_bound {w : ℕ} {sig : Fin w → ℤˣ} {p : ℕ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) (a : GNode (C.low B).garden.tree) : (C.low B).layer a ≤ p := by
  rcases C.component B with h | h
  · exact isCanonG_layer_le h a
  · exact (h.2.2 a).le

noncomputable def graft {w : ℕ} {sig : Fin w → ℤˣ} {p : ℕ} (C : CanonicalGraftData sig p) : LayeredGarden w :=
  layeredGardenGraft sig C.top C.partition C.low p C.plain C.sign C.layer_bound

theorem graft_isCanonG {w : ℕ} {sig : Fin w → ℤˣ} {p : ℕ} (C : CanonicalGraftData sig p) (hw : 4 ≤ w) :
    IsCanonG (p + 1) C.graft := by
  exact layeredGardenGraft_isCanonG hw sig C.top C.partition C.low p C.plain C.sign C.irreducible
    (fun B => (C.component B).imp_right (fun h => ⟨h.1, h.2.2⟩))

end CanonicalGraftData
end WaveTurbulence.Induct
