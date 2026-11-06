/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBaseMatrixChart
public import WaveTurbulenceVineParam.VineParamBaseOutgoing
public import WaveTurbulence.Foundations.Molecule.VineFiniteMatching
import Mathlib.Tactic

/-! # Exact directed matching of actual base bonds with a concrete chart -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Literal natural-number endpoints of a chart's directed bonds. -/
@[expose] def chartEndsNat {X : VineType} {p : Fin (baseProfileCount X)}
    (C : BaseMatrixChart X p) (j : Fin X.template.bonds.length) : ℕ×ℕ :=
  ((C.ends j).1.1,(C.ends j).2.1)

/-- Conditional matching consumer: the chart's profile is selected by the
actual count classification, and its checked fields force all directions. -/
theorem base_chart_multiset_eq {X : VineType} {p : Fin (baseProfileCount X)}
    (C : BaseMatrixChart X p) (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i => A.count (baseBundlePair X i))) :
    A=(List.ofFn (chartEndsNat C) : Multiset (ℕ×ℕ)) := by
  apply base_ordered_eq_of_counts X _ _ hU
  · rw [Multiset.map_coe,List.map_ofFn]
    change (List.ofFn (fun j => s((C.ends j).1.1,(C.ends j).2.1)) : Multiset (Sym2 ℕ))=_
    exact C.underlying_template
  · intro i
    have hc := C.forward_counts i
    simp only [hp,List.getElem_ofFn] at hc
    rw [Multiset.coe_count]
    unfold chartEndsNat
    exact hc.symm

/-- Exact bond-occurrence bijection after the actual counts select a profile.
Parallel occurrences remain distinct. This helper is consumed by the concrete
catalogue producer, rather than assumed as a source theorem. -/
theorem base_chart_bond_matching {X : VineType} {p : Fin (baseProfileCount X)}
    (C : BaseMatrixChart X p) {m : ℕ} (A : Fin m → ℕ×ℕ)
    (hU : ((List.ofFn A : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn A).count (baseBundlePair X i))) :
    ∃ σ : Fin m ≃ Fin X.template.bonds.length,∀ i,chartEndsNat C (σ i)=A i := by
  have hp' : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn A : Multiset (ℕ×ℕ)).count (baseBundlePair X i)) := by
    simpa only [Multiset.coe_count] using hp
  have hm := base_chart_multiset_eq C (List.ofFn A) hU hp'
  apply exists_label_matching A (chartEndsNat C)
  simpa only [Fin.univ_val_map] using hm

end WaveTurbulence.Vine.Param
