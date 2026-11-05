/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreIClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreIIClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreIIIClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreIVClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreVClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreVIClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIClassification
public import WaveTurbulence.Foundations.Molecule.VineCoreVIIIClassification
import Mathlib.Tactic

/-! # Exhaustive degree-shaped subsets of all eight base vine cores

This result classifies degree masks only. The later containment theorem must
also use the actual vine-like shape and the gap distinction. -/

public section
namespace WaveTurbulence.Vine

/-- Every block/hyper-block degree mask occurs in the explicit finite table. -/
theorem coreMask_exhaustive (X : VineType) (kind : CoreKind) (mask : ℕ → ℕ) (a b : ℕ)
    (h : CoreMaskShape X kind.jointDegree mask a b) :
    coreMaskVector X mask ∈ coreMaskCandidates X kind := by
  cases X <;> cases kind
  · exact coreI_block_exhaustive mask a b h
  · exact coreI_hyper_exhaustive mask a b h
  · exact coreII_block_exhaustive mask a b h
  · exact coreII_hyper_exhaustive mask a b h
  · exact coreIII_block_exhaustive mask a b h
  · exact coreIII_hyper_exhaustive mask a b h
  · exact coreIV_block_exhaustive mask a b h
  · exact coreIV_hyper_exhaustive mask a b h
  · exact coreV_block_exhaustive mask a b h
  · exact coreV_hyper_exhaustive mask a b h
  · exact coreVI_block_exhaustive mask a b h
  · exact coreVI_hyper_exhaustive mask a b h
  · exact coreVII_block_exhaustive mask a b h
  · exact coreVII_hyper_exhaustive mask a b h
  · exact coreVIII_block_exhaustive mask a b h
  · exact coreVIII_hyper_exhaustive mask a b h

/-- The finite classification does not depend on ordering the two joints. -/
theorem coreMask_exhaustive_unordered (X : VineType) (kind : CoreKind) (mask : ℕ → ℕ)
    (a b : ℕ) (ha : a<X.template.n) (hb : b<X.template.n) (hne : a ≠ b)
    (hma : mask a=1) (hmb : mask b=1) (hbound : ∀ i<X.template.n,mask i≤1)
    (hdegree : ∀ i<X.template.n,mask i=1 →
      coreDegree X mask i=if i=a ∨ i=b then kind.jointDegree else 4) :
    coreMaskVector X mask ∈ coreMaskCandidates X kind := by
  by_cases hab : a<b
  · exact coreMask_exhaustive X kind mask a b ⟨hab,hb,hma,hmb,hbound,hdegree⟩
  · have hba : b<a := by omega
    apply coreMask_exhaustive X kind mask b a
    refine ⟨hba,ha,hmb,hma,hbound,?_⟩
    intro i hi hm
    simpa only [or_comm] using hdegree i hi hm

end WaveTurbulence.Vine
