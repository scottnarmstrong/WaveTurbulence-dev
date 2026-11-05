/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA0
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA1
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA2
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA3
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA4
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA5
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA6
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA7
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA8
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIHyperA9
import Mathlib.Tactic

/-! # Exhaustive degree masks for the pinned type VII core (TARGET subsetvc)

Each theorem fixes the smaller joint. The equations are the actual adjacency
matrix of the pinned template; the proof is kernel-checked integer arithmetic.
These are degree masks, not yet the vine-like containment classification. -/

public section
namespace WaveTurbulence.Vine

/-- Exhaustive masks with smaller joint 0. -/
theorem coreVII_hyper_0 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 0<j) (hj1 : j<11) (_ha : b 0=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=0 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=0 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=0 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=0 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=0 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=0 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=0 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=0 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=0 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=0 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=0 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_0_1 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_2 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_0_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 1. -/
theorem coreVII_hyper_1 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 1<j) (hj1 : j<11) (_ha : b 1=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=1 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=1 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=1 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=1 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=1 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=1 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=1 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=1 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=1 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=1 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=1 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_1_2 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_1_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 2. -/
theorem coreVII_hyper_2 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 2<j) (hj1 : j<11) (_ha : b 2=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=2 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=2 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=2 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=2 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=2 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=2 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=2 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=2 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=2 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=2 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=2 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_2_3 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_2_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 3. -/
theorem coreVII_hyper_3 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 3<j) (hj1 : j<11) (_ha : b 3=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=3 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=3 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=3 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=3 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=3 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=3 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=3 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=3 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=3 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=3 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=3 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_3_4 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_3_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 4. -/
theorem coreVII_hyper_4 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 4<j) (hj1 : j<11) (_ha : b 4=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=4 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=4 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=4 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=4 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=4 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=4 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=4 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=4 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=4 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=4 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=4 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_4_5 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_4_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_4_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_4_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_4_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_4_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 5. -/
theorem coreVII_hyper_5 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 5<j) (hj1 : j<11) (_ha : b 5=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=5 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=5 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=5 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=5 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=5 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=5 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=5 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=5 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=5 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=5 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=5 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([[0,0,0,0,1,1,1,0,0,0,0]] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_5_6 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_5_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_5_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_5_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_5_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 6. -/
theorem coreVII_hyper_6 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 6<j) (hj1 : j<11) (_ha : b 6=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=6 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=6 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=6 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=6 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=6 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=6 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=6 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=6 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=6 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=6 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=6 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_6_7 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_6_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_6_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_6_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 7. -/
theorem coreVII_hyper_7 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 7<j) (hj1 : j<11) (_ha : b 7=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=7 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=7 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=7 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=7 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=7 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=7 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=7 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=7 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=7 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=7 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=7 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_7_8 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_7_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_7_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 8. -/
theorem coreVII_hyper_8 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 8<j) (hj1 : j<11) (_ha : b 8=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=8 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=8 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=8 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=8 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=8 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=8 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=8 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=8 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=8 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=8 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=8 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_8_9 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10
  · exact coreVII_hyper_8_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

/-- Exhaustive masks with smaller joint 9. -/
theorem coreVII_hyper_9 (b : ℕ → ℕ) (j : ℕ)
    (hj0 : 9<j) (hj1 : j<11) (_ha : b 9=1) (hj : b j=1)
    (_hb : ∀ i<11,b i≤1)
    (_hd0 : b 0=1 → b 2+b 3=if 0=9 ∨ 0=j then 3 else 4)
    (_hd1 : b 1=1 → b 9+b 10=if 1=9 ∨ 1=j then 3 else 4)
    (_hd2 : b 2=1 → b 0+2*b 3+b 7=if 2=9 ∨ 2=j then 3 else 4)
    (_hd3 : b 3=1 → b 0+2*b 2+b 8=if 3=9 ∨ 3=j then 3 else 4)
    (_hd4 : b 4=1 → 2*b 5+2*b 6=if 4=9 ∨ 4=j then 3 else 4)
    (_hd5 : b 5=1 → 2*b 4+b 6+b 7=if 5=9 ∨ 5=j then 3 else 4)
    (_hd6 : b 6=1 → 2*b 4+b 5+b 8=if 6=9 ∨ 6=j then 3 else 4)
    (_hd7 : b 7=1 → b 2+b 5+b 8+b 9=if 7=9 ∨ 7=j then 3 else 4)
    (_hd8 : b 8=1 → b 3+b 6+b 7+b 10=if 8=9 ∨ 8=j then 3 else 4)
    (_hd9 : b 9=1 → b 1+b 7+2*b 10=if 9=9 ∨ 9=j then 3 else 4)
    (_hd10 : b 10=1 → b 1+b 8+2*b 9=if 10=9 ∨ 10=j then 3 else 4)
    : [b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7,b 8,b 9,b 10] ∈ ([] : List (List ℕ)) := by
  interval_cases j
  · exact coreVII_hyper_9_10 b _ha hj _hb _hd0 _hd1 _hd2 _hd3 _hd4 _hd5 _hd6 _hd7 _hd8 _hd9 _hd10

end WaveTurbulence.Vine
