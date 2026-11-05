/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
/-! Independent source summation indices: bounded top trees, leaf partition, and bounded lower components. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

structure LowerGraftData {w : ℕ} (sig : Fin w → ℤˣ) (p Natt : ℕ) where
  low : LayeredGarden w
  sign : low.garden.sig = sig
  plain : low.garden.IsPlain
  component : IsCanonG p low ∨
    w = 2 ∧ (∀ j, low.garden.tree j = TTree.leaf) ∧ ∀ a, low.layer a = p
  order_le : low.garden.order ≤ Natt

structure GraftExpansionData {w : ℕ} (sig : Fin w → ℤˣ) (p Ntop Natt : ℕ) where
  top : Fin w → TrTree Ntop
  partition : Finpartition (univ : Finset (GLeaf (fun j => (top j).1)))
  irreducible : TopPartitionIrreducible (fun j => (top j).1) partition
  lower : (B : partition.parts) → LowerGraftData
    (fun k => nodeSign sig ((blockRootEquiv (fun j => (top j).1) partition).symm ⟨B, k⟩).1) p Natt

noncomputable def GraftExpansionData.toCanonical {w p Ntop Natt : ℕ} {sig : Fin w → ℤˣ}
    (D : GraftExpansionData sig p Ntop Natt) : CanonicalGraftData sig p where
  top j := (D.top j).1
  partition := D.partition
  low B := (D.lower B).low
  plain B := (D.lower B).plain
  sign B k := congrFun (D.lower B).sign k
  irreducible := D.irreducible
  component B := (D.lower B).component

theorem GraftExpansionData.toCanonical_isTrunc {w p Ntop Natt : ℕ} {sig : Fin w → ℤˣ}
    (D : GraftExpansionData sig p Ntop Natt) : D.toCanonical.IsTrunc Ntop Natt :=
  ⟨fun j => mem_truncatedTrees.mp (D.top j).2, fun B => (D.lower B).order_le⟩

noncomputable def CanonicalGraftData.toExpansion {w p Ntop Natt : ℕ} {sig : Fin w → ℤˣ}
    (C : CanonicalGraftData sig p) (htr : C.IsTrunc Ntop Natt) : GraftExpansionData sig p Ntop Natt where
  top j := ⟨C.top j, mem_truncatedTrees.mpr (htr.1 j)⟩
  partition := C.partition
  irreducible := C.irreducible
  lower B := ⟨C.low B, funext (C.sign B), C.plain B, C.component B, htr.2 B⟩

noncomputable def graftExpansionDataEquiv {w p : ℕ} (sig : Fin w → ℤˣ) (Ntop Natt : ℕ) :
    GraftExpansionData sig p Ntop Natt ≃ {C : CanonicalGraftData sig p // C.IsTrunc Ntop Natt} where
  toFun D := ⟨D.toCanonical, D.toCanonical_isTrunc⟩
  invFun C := C.1.toExpansion C.2
  left_inv D := by
    cases D
    rfl
  right_inv := by
    rintro ⟨C, htr⟩
    apply Subtype.ext
    cases C
    rfl

end WaveTurbulence.Induct
