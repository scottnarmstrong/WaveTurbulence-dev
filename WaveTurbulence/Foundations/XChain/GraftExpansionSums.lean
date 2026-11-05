/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionFinite
public import WaveTurbulence.Foundations.XChain.GraftFiniteSums
/-! Independent finite construction indices reindex exactly to the full source truncated garden sum. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem sum_graftExpansionData_eq_source {w p : ℕ} (sig : Fin w → ℤˣ) (hw : 4 ≤ w)
    (Ntop Natt : ℕ) (f : LayeredGarden w → ℂ) :
    (∑ D : GraftExpansionData sig p Ntop Natt, f D.toCanonical.graft) =
      ∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
        LG.IsTrunc p Ntop Natt}, f LG.1 := by
  have he := finsum_comp_equiv (graftExpansionDataEquiv (p := p) sig Ntop Natt)
    (f := fun C : {C : CanonicalGraftData sig p // C.IsTrunc Ntop Natt} => f C.1.graft)
  have hsum := finsum_eq_sum_of_fintype (fun D : GraftExpansionData sig p Ntop Natt => f D.toCanonical.graft)
  exact hsum.symm.trans (he.trans (finsum_canonicalGraft_trunc sig hw Ntop Natt f))

theorem sum_graftExpansionData_eq_index {w p : ℕ} (sig : Fin w → ℤˣ) (Ntop Natt : ℕ)
    (f : GraftExpansionData sig p Ntop Natt → ℂ) :
    (∑ D, f D) = ∑ top : Fin w → TrTree Ntop,
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P},
      ∑ low : (B : P.1.parts) → LowerGraftData
        (fun k => nodeSign sig ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).1) p Natt,
        f ⟨top, P.1, P.2, low⟩ := by
  have he := Fintype.sum_equiv (graftExpansionIndexEquiv sig Ntop Natt) f
    (fun D : GraftExpansionIndex sig p Ntop Natt => f ⟨D.1, D.2.1.1, D.2.1.2, D.2.2⟩) (fun _ => rfl)
  exact he.trans ((Fintype.sum_sigma _).trans (sum_congr rfl (fun _ _ => Fintype.sum_sigma _)))

end WaveTurbulence.Induct
