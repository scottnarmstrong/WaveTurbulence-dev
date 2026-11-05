/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionData
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! The independent top/partition/lower summation carriers in T.cmattr are all finite. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

namespace LowerGraftData

theorem layer_le {w p N : ℕ} {sig : Fin w → ℤˣ} (D : LowerGraftData sig p N)
    (a : GNode D.low.garden.tree) : D.low.layer a ≤ p := by
  rcases D.component with h | h
  · exact isCanonG_layer_le h a
  · exact (h.2.2 a).le

theorem low_injective {w p N : ℕ} {sig : Fin w → ℤˣ} :
    Function.Injective (fun D : LowerGraftData sig p N => D.low) := by
  intro D E he
  cases D
  cases E
  cases he
  rfl

instance {w p N : ℕ} {sig : Fin w → ℤˣ} : Finite (LowerGraftData sig p N) := by
  haveI : Finite {LG : LayeredGarden w // LG.garden.order ≤ N ∧ ∀ a, LG.layer a ≤ p} :=
    (Canon.finite_layeredGardens w N p).to_subtype
  apply Finite.of_injective
    (fun D : LowerGraftData sig p N => (⟨D.low, D.order_le, D.layer_le⟩ :
      {LG : LayeredGarden w // LG.garden.order ≤ N ∧ ∀ a, LG.layer a ≤ p}))
  intro D E he
  exact low_injective (congrArg Subtype.val he)

noncomputable instance {w p N : ℕ} {sig : Fin w → ℤˣ} : Fintype (LowerGraftData sig p N) := Fintype.ofFinite _

end LowerGraftData

abbrev GraftExpansionIndex {w : ℕ} (sig : Fin w → ℤˣ) (p Ntop Natt : ℕ) :=
  Σ top : Fin w → TrTree Ntop,
  Σ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
    TopPartitionIrreducible (fun j => (top j).1) P},
  (B : P.1.parts) → LowerGraftData
    (fun k => nodeSign sig ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).1) p Natt

noncomputable def graftExpansionIndexEquiv {w p : ℕ} (sig : Fin w → ℤˣ) (Ntop Natt : ℕ) :
    GraftExpansionData sig p Ntop Natt ≃ GraftExpansionIndex sig p Ntop Natt where
  toFun D := ⟨D.top, ⟨D.partition, D.irreducible⟩, D.lower⟩
  invFun D := ⟨D.1, D.2.1.1, D.2.1.2, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {w p Ntop Natt : ℕ} {sig : Fin w → ℤˣ} : Finite (GraftExpansionData sig p Ntop Natt) :=
  Finite.of_injective (graftExpansionIndexEquiv sig Ntop Natt) (graftExpansionIndexEquiv sig Ntop Natt).injective

noncomputable instance {w p Ntop Natt : ℕ} {sig : Fin w → ℤˣ} : Fintype (GraftExpansionData sig p Ntop Natt) :=
  Fintype.ofFinite _

end WaveTurbulence.Induct
