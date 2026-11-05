/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA0
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA1
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA2
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA3
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA4
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA5
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA6
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA7
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA8
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA9
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA10
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA11
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA12
public import WaveTurbulence.Foundations.Molecule.VineCoreVIHyperA13
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type VI core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- Exhaustive masks with smaller joint 0. -/
theorem coreVI_hyper_0 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 0<j) (hj1 : j<15) (_ha : b 0=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=0 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=0 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=0 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=0 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=0 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=0 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=0 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=0 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=0 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=0 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=0 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=0 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=0 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=0 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=0 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_0_1 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_2 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_0_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 1. -/
theorem coreVI_hyper_1 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 1<j) (hj1 : j<15) (_ha : b 1=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=1 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=1 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=1 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=1 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=1 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=1 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=1 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=1 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=1 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=1 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=1 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=1 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=1 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=1 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=1 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_1_2 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_1_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 2. -/
theorem coreVI_hyper_2 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 2<j) (hj1 : j<15) (_ha : b 2=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=2 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=2 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=2 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=2 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=2 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=2 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=2 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=2 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=2 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=2 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=2 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=2 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=2 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=2 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=2 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_2_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_2_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 3. -/
theorem coreVI_hyper_3 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 3<j) (hj1 : j<15) (_ha : b 3=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=3 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=3 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=3 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=3 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=3 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=3 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=3 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=3 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=3 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=3 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=3 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=3 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=3 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=3 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=3 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_3_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_3_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 4. -/
theorem coreVI_hyper_4 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 4<j) (hj1 : j<15) (_ha : b 4=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=4 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=4 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=4 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=4 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=4 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=4 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=4 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=4 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=4 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=4 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=4 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=4 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=4 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=4 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=4 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_4_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_4_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 5. -/
theorem coreVI_hyper_5 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 5<j) (hj1 : j<15) (_ha : b 5=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=5 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=5 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=5 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=5 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=5 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=5 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=5 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=5 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=5 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=5 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=5 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=5 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=5 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=5 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=5 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_5_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_5_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 6. -/
theorem coreVI_hyper_6 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 6<j) (hj1 : j<15) (_ha : b 6=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=6 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=6 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=6 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=6 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=6 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=6 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=6 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=6 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=6 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=6 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=6 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=6 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=6 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=6 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_6_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_6_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 7. -/
theorem coreVI_hyper_7 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 7<j) (hj1 : j<15) (_ha : b 7=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=7 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=7 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=7 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=7 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=7 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=7 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=7 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=7 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=7 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=7 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=7 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=7 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=7 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=7 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=7 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_7_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_7_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 8. -/
theorem coreVI_hyper_8 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 8<j) (hj1 : j<15) (_ha : b 8=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=8 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=8 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=8 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=8 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=8 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=8 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=8 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=8 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=8 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=8 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=8 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=8 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=8 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=8 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=8 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([[0,0,0,0,0,0,0,0,1,1,1,1,1,0,0]] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_8_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_8_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_8_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_8_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_8_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_8_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 9. -/
theorem coreVI_hyper_9 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 9<j) (hj1 : j<15) (_ha : b 9=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=9 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=9 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=9 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=9 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=9 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=9 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=9 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=9 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=9 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=9 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=9 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=9 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=9 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=9 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=9 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_9_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_9_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_9_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_9_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_9_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 10. -/
theorem coreVI_hyper_10 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 10<j) (hj1 : j<15) (_ha : b 10=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=10 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=10 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=10 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=10 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=10 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=10 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=10 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=10 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=10 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=10 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=10 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=10 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=10 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=10 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=10 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([[0,0,0,0,0,0,0,0,0,0,1,1,1,0,0]] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_10_11 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_10_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_10_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_10_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 11. -/
theorem coreVI_hyper_11 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 11<j) (hj1 : j<15) (_ha : b 11=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=11 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=11 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=11 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=11 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=11 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=11 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=11 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=11 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=11 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=11 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=11 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=11 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=11 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=11 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=11 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_11_12 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_11_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_11_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 12. -/
theorem coreVI_hyper_12 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 12<j) (hj1 : j<15) (_ha : b 12=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=12 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=12 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=12 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=12 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=12 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=12 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=12 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=12 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=12 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=12 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=12 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=12 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=12 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=12 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=12 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_12_13 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14
  · exact coreVI_hyper_12_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

/-- Exhaustive masks with smaller joint 13. -/
theorem coreVI_hyper_13 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 13<j) (hj1 : j<15) (_ha : b 13=1) (hj : b j=1)
    (_hb : ∀ i<15,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=13 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 13+b 14=if 1=13 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 4=if 2=13 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 5=if 3=13 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → b 2+2*b 5+b 6=if 4=13 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → b 3+2*b 4+b 8=if 5=13 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → b 4+2*b 7+b 13=if 6=13 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → 2*b 6+b 9+b 14=if 7=13 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 5+2*b 9+b 10=if 8=13 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 7+2*b 8+b 11=if 9=13 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 8+b 11+2*b 12=if 10=13 ∨ 10=j then 3 else 4)
    (_hd11 : b 11=1 → b 9+b 10+2*b 12=if 11=13 ∨ 11=j then 3 else 4)
    (_hd12 : b 12=1 → 2*b 10+2*b 11=if 12=13 ∨ 12=j then 3 else 4)
    (_hd13 : b 13=1 → b 1+b 6+2*b 14=if 13=13 ∨ 13=j then 3 else 4)
    (_hd14 : b 14=1 → b 1+b 7+2*b 13=if 14=13 ∨ 14=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10,b 11,b 12,b 13,b 14] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVI_hyper_13_14 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10 _hd11 _hd12 _hd13 _hd14

end WaveTurbulence.Vine
