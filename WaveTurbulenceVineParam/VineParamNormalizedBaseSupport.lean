/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedVineCertificate
public import WaveTurbulenceVineParam.VineParamNormalizedBaseShape
public import WaveTurbulenceVineParam.VineParamSlotCaps
public import WaveTurbulenceVineParam.VineParamBaseBundlePartition
public import WaveTurbulenceVineParam.VineParamProfileDegrees
import Mathlib.Tactic

/-! # Source-template and cap support data of a normalized base certificate

These finite geometric properties are the strengthened induction data for
arbitrary rung insertion. They assert no source chart existence theorem.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- A concrete base certificate is pinned to its actual source orientation
and retains fixed physical difference origins through every marked cap. -/
structure NormalizedBaseSupport {X : VineType} (p : Fin (baseProfileCount X))
    (C : NormalizedVineCertificate X) : Prop where
  shape_eq : C.shape=normalizedBaseShape X
  ends_profile : List.ofFn (fun e => ((C.matrix.ends e).1.1,(C.matrix.ends e).2.1))=normalizedBaseEnds X p
  underlying_template :
    ((List.ofFn (fun e => s((C.matrix.ends e).1.1,(C.matrix.ends e).2.1))) : Multiset (Sym2 ℕ))=
      (X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))
  forward_counts : ∀ i : Fin (baseBundles X).length,
    (List.ofFn (fun e => ((C.matrix.ends e).1.1,(C.matrix.ends e).2.1))).count (baseBundlePair X i)=
      (baseProfileCounts X p)[i.1]'(by rw [baseProfileCounts_length]; exact i.2)
  joints_eq : ({C.matrix.a.1,C.matrix.b.1} : Finset ℕ)={0,1}
  pair_uniform : ∀ s : Fin X.template.slots.length,∀ j : Fin C.shape.m,
    (C.atom (C.shape.xSlot j)).1.1 ∈ slotCap X s ↔ (C.atom (C.shape.ySlot j)).1.1 ∈ slotCap X s
  core_uniform : ∀ hn : X.IsBad=false,∀ s : Fin X.template.slots.length,∀ i j : Fin 3,
    (C.atom (C.shape.uSlot hn i)).1.1 ∈ slotCap X s ↔
      (C.atom (C.shape.uSlot hn j)).1.1 ∈ slotCap X s
  difference_support : ∀ i : {i : Fin C.shape.n // i ≠ C.shape.x0},∀ s : Fin X.template.slots.length,
    (((C.matrix.ends (C.differencePair i).1).1.1 ∈ slotCap X s ∨
        (C.matrix.ends (C.differencePair i).1).2.1 ∈ slotCap X s) ∧
      ((C.matrix.ends (C.differencePair i).2).1.1 ∈ slotCap X s ∨
        (C.matrix.ends (C.differencePair i).2).2.1 ∈ slotCap X s)) ∨
    (((C.matrix.ends (C.differencePair i).1).1.1 ∉ slotCap X s ∨
        (C.matrix.ends (C.differencePair i).1).2.1 ∉ slotCap X s) ∧
      ((C.matrix.ends (C.differencePair i).2).1.1 ∉ slotCap X s ∨
        (C.matrix.ends (C.differencePair i).2).2.1 ∉ slotCap X s))

end WaveTurbulence.Vine.Param
