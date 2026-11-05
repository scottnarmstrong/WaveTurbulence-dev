/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestDecorationEquiv
public import WaveTurbulence.Foundations.XChain.CumulantPartitionSeries
/-! The root labels in the analytic series are exactly the labels of a forest decoration. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def univLabelEquiv {ι : Type*} [Fintype ι] (α : ι → Type*) :
    ((i : ↥(univ : Finset ι)) → α i.1) ≃ ((i : ι) → α i) where
  toFun a i := a ⟨i, mem_univ i⟩
  invFun a i := a i.1
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def forestSeriesLabelEquiv {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) :
    ((i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1)) ≃ ForestDecoration top d n :=
  (univLabelEquiv (fun i => TreeDecoration (top i) d (n i))).trans (forestDecorationEquiv top n).symm

theorem forestSeriesLabelEquiv_component {w d : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ))
    (a : (i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1)) (j : Fin w) :
    forestDecorationEquiv top n (forestSeriesLabelEquiv top n a) j = a ⟨j, mem_univ j⟩ := by
  have he := (forestDecorationEquiv top n).apply_symm_apply
    (univLabelEquiv (fun i => TreeDecoration (top i) d (n i)) a)
  exact congrArg (fun z => z j) he

end WaveTurbulence.Induct
