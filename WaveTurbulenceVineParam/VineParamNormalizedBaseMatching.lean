/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedBaseSupport
public import WaveTurbulenceVineParam.VineParamBaseChartMatching
import Mathlib.Tactic

/-! # Exact actual directed occurrence matching for normalized certificates -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- Literal endpoints in a normalized source certificate. -/
@[expose] def normalizedChartEnds {X : VineType} (C : NormalizedVineCertificate X)
    (j : Fin (2*C.shape.n)) : ℕ×ℕ :=
  ((C.matrix.ends j).1.1,(C.matrix.ends j).2.1)

/-- Actual direction counts determine the complete normalized endpoint
multiset, with every parallel occurrence retained. -/
theorem normalized_base_multiset_eq {X : VineType} {p : Fin (baseProfileCount X)}
    (C : NormalizedVineCertificate X) (H : NormalizedBaseSupport p C)
    (A : Multiset (ℕ×ℕ))
    (hU : A.map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i => A.count (baseBundlePair X i))) :
    A=(List.ofFn (normalizedChartEnds C) : Multiset (ℕ×ℕ)) := by
  apply base_ordered_eq_of_counts X _ _ hU
  · rw [Multiset.map_coe,List.map_ofFn]
    exact H.underlying_template
  · intro i
    have hc := H.forward_counts i
    simp only [hp,List.getElem_ofFn] at hc
    rw [Multiset.coe_count]
    exact hc.symm

/-- A source-selected normalized certificate gives a fixed bijection of
all actual directed bond occurrences, before choosing any labels. -/
theorem normalized_base_bond_matching {X : VineType} {p : Fin (baseProfileCount X)}
    (C : NormalizedVineCertificate X) (H : NormalizedBaseSupport p C)
    {m : ℕ} (A : Fin m → ℕ×ℕ)
    (hU : ((List.ofFn A : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun e => s(e.1,e.2))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn A).count (baseBundlePair X i))) :
    ∃ σ : Fin m ≃ Fin (2*C.shape.n),∀ i,normalizedChartEnds C (σ i)=A i := by
  have hp' : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn A : Multiset (ℕ×ℕ)).count (baseBundlePair X i)) := by
    simpa only [Multiset.coe_count] using hp
  have hm := normalized_base_multiset_eq C H (List.ofFn A) hU hp'
  apply exists_label_matching A (normalizedChartEnds C)
  simpa only [Fin.univ_val_map] using hm

end WaveTurbulence.Vine.Param
