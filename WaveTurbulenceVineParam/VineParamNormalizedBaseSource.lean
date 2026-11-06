/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedBaseIso
public import WaveTurbulenceVineParam.VineParamNormalizedPhysicalSupport
public import WaveTurbulenceVineParam.VineParamGroupInsert
public import WaveTurbulenceVineParam.VineParamGroupCert
import Mathlib.Tactic

/-! # Source matching consumer for a concrete normalized certificate

Directions are recovered from the source shape and degree equations.
All physical origins and cap supports are produced, not assumed.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- The exact pinned cap on the literal base source atom carrier. -/
@[expose] def baseSourceCap (X : VineType) (s : Fin X.template.slots.length) : Finset (Fin X.template.n) :=
  univ.filter (fun v => v.1 ∈ slotCap X s)

/-- The checked concrete certificate and actual source occurrence matching
produce the full physical base chart with every pinned cap supported. -/
theorem exists_physical_base_of_certificate {X : VineType} {p : Fin (baseProfileCount X)}
    (C : NormalizedVineCertificate X) (H : NormalizedBaseSupport p C) (hG : C.GroupsOK) {m : ℕ}
    (A : Fin m → Fin X.template.n × Fin X.template.n)
    (hU : ((List.ofFn (fun e => ((A e).1.1,(A e).2.1)) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map
      (fun e => s(e.1,e.2))=(X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn (fun e => ((A e).1.1,(A e).2.1))).count (baseBundlePair X i)))
    (a b : Fin X.template.n) (ha : C.matrix.a.1=a.1) (hb : C.matrix.b.1=b.1) :
    ∃ P : PhysicalGraphChart A X a b,
      (∀ s : Fin X.template.slots.length,P.CapSupported (baseSourceCap X s)) ∧
      (∀ s : Fin X.template.slots.length,∀ j : Fin P.full.indexing.shape.m,
        (P.full.indexing.atom (P.full.indexing.shape.xSlot j)).1 ∈ baseSourceCap X s ↔
          (P.full.indexing.atom (P.full.indexing.shape.ySlot j)).1 ∈ baseSourceCap X s) ∧
      indexingGroupSet P.full.indexing (fun v => v.1) = listGroupSet X.template.groups := by
  obtain ⟨I,hI⟩ := normalized_base_graph_iso C H A hU hp
  have hIa : I.atom C.matrix.a=a := Fin.ext ((hI _).trans ha)
  have hIb : I.atom C.matrix.b=b := Fin.ext ((hI _).trans hb)
  subst a
  subst b
  refine ⟨I.physicalChart C.physicalChart,?_,?_,?_⟩
  · intro s
    apply I.physicalChart_capSupported C.physicalChart (C.physicalCap s) (baseSourceCap X s)
    · intro v
      simp only [baseSourceCap,NormalizedVineCertificate.physicalCap,mem_filter,mem_univ,true_and,hI v]
    · exact C.physicalChart_capSupported H s
  · intro s
    apply I.physicalChart_pair_uniform C.physicalChart (C.physicalCap s) (baseSourceCap X s)
    · intro v
      simp only [baseSourceCap,NormalizedVineCertificate.physicalCap,mem_filter,mem_univ,true_and,hI v]
    · intro j
      change ((C.atom (C.shape.xSlot j)).1 ∈ C.physicalCap s ↔
        (C.atom (C.shape.ySlot j)).1 ∈ C.physicalCap s)
      simpa only [NormalizedVineCertificate.physicalCap,mem_filter,mem_univ,true_and] using H.pair_uniform s j
  · rw [I.physicalChart_groupSet C.physicalChart]
    have hf : (fun v => ((I.atom v).1 : ℕ)) = fun v => v.1 := funext hI
    simp only [hf]
    exact hG

end WaveTurbulence.Vine.Param
